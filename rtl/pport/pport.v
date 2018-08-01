////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	pport.v
//
// Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
//
// Purpose:
//
//	Based upon an internet search, the fastest that a pin can toggle using
//	wiringPi is about 4.6 MHz.  We'll call this 5MHz for safety's sake,
//	or 200ns.  Since our internal clock is 100MHz (10ns), or even
//	if it were as slow as 80MHz (12.5ns), this allows us 16 clocks per
//	transition--hence we can do all our processing in logic.  Realistically,
//	even if we did it via bit-banging the RPi's wires, we'd only get 5.4MHz
//	or 185ns, still allowing 14 clocks at 12.5ns if we needed them.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017, Gisselquist Technology, LLC
//
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of  the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License, or (at
// your option) any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
//
module	pport(i_clk,
		o_rx_stb, o_rx_data,
		i_tx_wr, i_tx_data, o_tx_busy,
		i_pp_dir, i_pp_clk, i_pp_data, o_pp_data,
			o_pp_clkfb, o_dbg);
	input	wire	i_clk;
	// Receive interface
	output	reg		o_rx_stb;
	output	reg	[7:0]	o_rx_data;
	// Transmit interface
	input	wire		i_tx_wr;
	input	wire	[7:0]	i_tx_data;
	output	reg		o_tx_busy;
	// Parallel port interface itself
	input	wire		i_pp_dir;
	input	wire		i_pp_clk;
	input	wire	[7:0]	i_pp_data;
	output	reg	[7:0]	o_pp_data;
	output	reg		o_pp_clkfb;
	output	wire		o_dbg;

	//
	//
	// Synchronize our inputs
	//
	//

	localparam	SCLKS = 6; // 3 is the minimum

	// First, sycnrhonize the clock and generate a clock strobe
	reg		stb_pp_dir, ck_pp_dir;
	wire		stb_rd_dir, stb_wr_dir;
	wire		ck_rd_dir, ck_wr_dir;
	reg		pp_stb;
	reg	[(SCLKS-1):0]	pp_clk_transfer;
	initial	pp_clk_transfer = 0;
	initial	pp_stb = 0;
	always @(posedge i_clk)
		pp_clk_transfer <= { pp_clk_transfer[(SCLKS-2):0], i_pp_clk };

	initial o_pp_clkfb = 1'b0;
	always @(posedge i_clk)
		if (&pp_clk_transfer[(SCLKS-1):1])
			o_pp_clkfb <= 1'b1;
		else if (pp_clk_transfer[(SCLKS-1):1] == 0)
			o_pp_clkfb <= 1'b0;
	always @(posedge i_clk)
		pp_stb <= (&pp_clk_transfer[(SCLKS-1):1])&&(!o_pp_clkfb);

	reg	[7:0]	ck_pp_data;
	always @(posedge i_clk)
	if (!o_pp_clkfb)
		ck_pp_data <= i_pp_data;

	always @(posedge i_clk)
	if (!o_pp_clkfb)
		stb_pp_dir <= i_pp_dir;
	always @(posedge i_clk)
		ck_pp_dir <= stb_pp_dir;

	assign	stb_rd_dir =  stb_pp_dir; // Read from the PI
	assign	stb_wr_dir = !stb_rd_dir; // Write to the PI
	assign	ck_rd_dir  =  ck_pp_dir;
	assign	ck_wr_dir  = !ck_rd_dir;

	initial	o_rx_stb = 1'b0;
	always @(posedge i_clk)
		o_rx_stb <= (pp_stb)&&(stb_rd_dir);

	always @(posedge i_clk)
		if (pp_stb)
			o_rx_data <= ck_pp_data;

	reg	loaded;
	initial	loaded = 1'b0;
	always @(posedge i_clk)
		if ((i_tx_wr)&&(!o_tx_busy))
			loaded <= 1'b1;
		else if ((pp_stb)&&(stb_wr_dir))
			loaded <= 1'b0;

	initial	o_tx_busy = 1'b0;
	always @(posedge i_clk)
		// We are busy if ...
		//	1. We have a word loaded and ready to transmit
		o_tx_busy <= (loaded)
			// 2. We are not busy, and someone gives us a word
			// to transmit, or
			||((i_tx_wr)&&(!o_tx_busy))
			// 3. We are in the middle of a read transaction.
			// During transactions, things cannot be changed, so
			// ... we are hence busy
			||(((|pp_clk_transfer[(SCLKS-1):1])||(o_pp_clkfb))
						&&(ck_wr_dir));

	initial	o_pp_data = 8'hff;
	always @(posedge i_clk)
	if (!o_tx_busy)
	begin
		if (i_tx_wr)
			o_pp_data <= i_tx_data[7:0];
		else
			o_pp_data <= 8'hff;
	end

reg	r_dbg;
always @(posedge i_clk)
	r_dbg <= (i_tx_wr)&&(!o_tx_busy);
assign	o_dbg = r_dbg; // (o_rx_stb);
`ifdef	FORMAL
	reg	f_past_valid_gbl, f_past_valid;

	initial	f_past_valid_gbl = 1'b0;
	always @(posedge i_clk)
		f_past_valid_gbl <= 1'b1;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	//////////////////////
	// Clock generation
	reg	[1:0]	f_ckreg;
	always @($global_clock)
		f_ckreg <= f_ckreg + 1'b1;
	always @(*)
		assume(i_clk == f_ckreg[1]);

	reg	f_past_pp_clk;
	initial	f_past_pp_clk = 1'b0;
	always @($global_clock)
		f_past_pp_clk <= i_pp_clk;

	always @(*)
	if ((f_past_pp_clk)&&(!o_pp_clkfb))
		assume(i_pp_clk == f_past_pp_clk);

	always @(*)
	if ((!f_past_pp_clk)&&(o_pp_clkfb))
		assume(i_pp_clk == f_past_pp_clk);

	always @($global_clock)
	begin
		if ((f_past_valid_gbl)&&(!$rose(i_clk)))
		begin
			assume($stable(i_tx_wr));
			assume($stable(i_tx_data));

			assert($stable(o_tx_busy));
			assert($stable(o_rx_stb));
			assert($stable(o_rx_data));
		end

		if ($past(i_pp_clk != o_pp_clkfb))
			assume($stable(i_pp_clk));
		if (!$stable(o_pp_clkfb))
			assume($stable(i_pp_clk));
		if (i_pp_clk)
		begin
			assume($stable(i_pp_dir));
			assume($stable(i_pp_data));
		end
	end

	///////////////////////
	// Input assumptions
	initial	assume(!i_pp_clk);
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_tx_wr))&&($past(o_tx_busy)))
		assume(($stable(i_tx_wr))&&($stable(i_tx_data)));
	always @(*)
	if (!i_pp_dir)
		assume(i_pp_data === o_pp_data);

	reg	[2:0]	pp_clk_count;
	initial	pp_clk_count = 0;
	always @($global_clock)
	if ((i_pp_clk != o_pp_clkfb)||(!i_pp_clk))
		pp_clk_count <= 0;
	else
		pp_clk_count <= pp_clk_count + 1;
	always @(*)
		assume(pp_clk_count < 3'h7);


	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_rx_stb)))
		assert(!o_rx_stb);

	reg		f_rx_stb,  f_tx_stb;
	reg	[7:0]	f_rx_data, f_tx_data;

	initial	f_rx_stb = 1'b0;
	always @($global_clock)
	if (($rose(i_pp_clk))&&(i_pp_dir))
	begin
		assert(!o_pp_clkfb);
		assert(!f_rx_stb);
		f_rx_stb <= 1'b1;
		f_rx_data <= i_pp_data;
	end else if ((o_rx_stb)&&(o_rx_data == f_rx_data))
		f_rx_stb <= 1'b0;

	always @(*)
	if ((!i_pp_clk)&&(!o_pp_clkfb))
		assert(!f_rx_stb);

	always @($global_clock)
	if ($rose(o_rx_stb))
		assert(f_rx_stb);

	always @($global_clock)
	if (f_rx_stb)
	begin
		if (i_pp_clk)
			assert(i_pp_data == f_rx_data);
		if (f_past_valid_gbl)
		begin
			if ($rose(o_pp_clkfb))
				assert(ck_pp_data == f_rx_data);
			else if (pp_stb)
				assert(ck_pp_data == f_rx_data);
			else if (o_pp_clkfb)
				assert(o_rx_data == f_rx_data);
		end
		if (o_rx_stb)
			assert(o_rx_data == f_rx_data);
	end

	always @($global_clock)
	if ((f_past_valid_gbl)
			&&(!i_pp_dir)&&(i_pp_clk)&&($stable(i_pp_clk))
			&&(o_pp_clkfb)&&($stable(o_pp_clkfb)))
		assert($stable(o_pp_data));

	always @(posedge i_clk)
	if ((f_tx_stb)&&(i_pp_clk)&&(o_pp_clkfb)&&(!i_pp_dir))
		assert(o_pp_data == f_tx_data);

	always @($global_clock)
	if ((f_past_valid_gbl)&&($rose(o_pp_clkfb))&&(!f_tx_stb))
		assert(o_pp_data == 8'hff);

	always @($global_clock)
	if ((pp_clk_transfer != 0)&&(!(&pp_clk_transfer)))
		assert($stable(i_pp_clk));

	always @($global_clock)
	if ((pp_clk_transfer != 0)&&(!(&pp_clk_transfer)))
		assert($stable(o_pp_clkfb));

	always @($global_clock)
	if ((f_past_valid_gbl)&&($rose(o_pp_clkfb)))
		assert(f_tx_stb == loaded);
	initial	f_tx_stb = 1'b0;
	always @(posedge i_clk)
	if ((i_tx_wr)&&(!o_tx_busy))
	begin
		assert(!f_tx_stb);
		f_tx_stb <= 1'b1;
		f_tx_data <= i_tx_data;
	end else if (($fell(i_pp_clk))&&(!$past(i_pp_dir))
				&&($past(o_pp_data==f_tx_data)))
		f_tx_stb <= 1'b0;
	always @(*)
	if (loaded)
		assert((f_tx_stb)&&(f_tx_data == o_pp_data));

	always @(*)
	if ((f_tx_stb)&&(!o_pp_clkfb))
		assert(o_tx_busy);

	always @(*)
	if ((f_tx_stb)&&(!o_pp_clkfb)&&(!i_pp_dir))
		assert(o_tx_busy);

	always @($global_clock)
	if ((i_pp_clk == o_pp_clkfb)&&(i_pp_clk))
		assert(i_pp_dir == stb_pp_dir);
	always @($global_clock)
	if ((i_pp_clk == o_pp_clkfb)&&(i_pp_clk))
		assert(ck_pp_dir == stb_pp_dir);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(o_pp_clkfb))&&(o_pp_clkfb))
		assert(pp_stb);

	always @($global_clock)
	if ((f_past_valid)&&($past(o_pp_clkfb))&&(o_pp_clkfb))
		assert($stable(ck_pp_data));

	always @(posedge i_clk)
		cover((f_tx_stb)&&(!i_pp_dir)&&(o_pp_clkfb)
				&&(o_pp_data == f_tx_data));

	always @(posedge i_clk)
		cover(o_rx_stb);

	always @($global_clock)
	if (f_past_valid_gbl)
		cover($rose(i_pp_clk));
	always @($global_clock)
	if (f_past_valid_gbl)
		cover($fell(i_pp_clk));
	always @($global_clock)
	if (f_past_valid_gbl)
		cover(i_pp_clk);

//module	pport(i_clk,
//		o_rx_stb, o_rx_data,
//		i_tx_wr, i_tx_data, o_tx_busy,
//		i_pp_dir, i_pp_clk, i_pp_data, o_pp_data,
//			o_pp_clkfb, o_dbg);
`endif
endmodule
