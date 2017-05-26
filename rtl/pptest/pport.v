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
		i_pp_dir, i_pp_clk, i_pp_data, o_pp_data);
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

	//
	//
	// Synchronize our inputs
	//
	//

	// First, sycnrhonize the clock and generate a clock strobe
	wire		ck_pp_clk;
	wire		ck_rd_dir, ck_wr_dir;
	reg		pp_stb, pp_dbl_clk;
	reg	[2:0]	pp_clk_transfer;
	initial	pp_clk_transfer = 3'h0;
	always @(posedge i_clk)
		pp_clk_transfer <= { pp_clk_transfer[1:0], i_pp_clk };
	always @(posedge i_clk)
		pp_stb <= (pp_clk_transfer[2:1]== 2'b01);
	assign	ck_pp_clk = pp_clk_transfer[1];

	// Next, synchronize the incoming data
	//	Not really necessary, though, since ... these should
	//	be stable once we notice the clock is high
	/*
	reg	[7:0]	q_pp_data, ck_pp_data;
	always @(posedge i_clk)
		q_pp_data  <= i_pp_data;
	always @(posedge i_clk)
		ck_pp_data <= q_pp_data;
	*/
	reg	[7:0]	ck_pp_data;
	always @(posedge i_clk)
		ck_pp_data <= i_pp_data;

	// ... and the incoming direction
	//	which should also be stable, due to waiting on the clock
	/*
	reg		q_pp_dir, ck_pp_dir;
	always @(posedge i_clk)
		q_pp_dir  <= i_pp_dir;
	always @(posedge i_clk)
		ck_pp_dir <= q_pp_dir;
	*/
	reg	ck_pp_dir;
	always @(posedge i_clk)
		ck_pp_dir <= i_pp_dir;

	assign	ck_rd_dir =  ck_pp_dir; // Read from the PI
	assign	ck_wr_dir = !ck_rd_dir; // Write to the PI

	always @(posedge i_clk)
		o_rx_stb <= (pp_stb)&&(ck_rd_dir);
	always @(posedge i_clk)
		if (pp_stb)
			o_rx_data <= ck_pp_data;

	reg	loaded;
	always @(posedge i_clk)
		if ((i_tx_wr)&&(!o_tx_busy))
			loaded <= 1'b1;
		else if ((pp_stb)&&(ck_wr_dir))
			loaded <= 1'b0;

	always @(posedge i_clk)
		o_tx_busy <= (loaded)
			||((i_tx_wr)&&(!o_tx_busy))
			||((ck_pp_clk)&&(ck_wr_dir));

	always @(posedge i_clk)
		if (!o_tx_busy)
		begin
			if (i_tx_wr)
				o_pp_data <= { 1'b0, i_tx_data[6:0] };
			else
				o_pp_data <= 8'hff;
		end

endmodule