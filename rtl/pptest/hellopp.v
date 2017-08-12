////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	hellopp.v
//
// Project:
//
// Purpose:	To create a *very* simple parallel port testing program, which
//		can be used as the top level design file of any FPGA program.
//
//	This code has been taken from the wbuart32 library and modified for this
//	prpose.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2017, Gisselquist Technology, LLC
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
// with this program.  (It's in the $(ROOT)/doc directory, run make with no
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
module	hellopp(i_clk,
		o_ledg, o_ledr,
		i_pp_dir, i_pp_clk, io_pp_data, o_pp_clkfb);
	//
	input			i_clk;
	output	wire	[1:0]	o_ledg;
	output	wire		o_ledr;
	//
	input	wire		i_pp_dir, i_pp_clk;
	inout	wire	[7:0]	io_pp_data;
	output	wire		o_pp_clkfb;

	reg	[7:0]	message	[0:15];

	wire	s_clk;

`ifdef	VERILATOR
	assign	s_clk = i_clk;
`else
	wire	clk_66mhz, pll_locked;
	SB_PLL40_PAD #(
		.FEEDBACK_PATH("SIMPLE"),
		.DELAY_ADJUSTMENT_MODE_FEEDBACK("FIXED"),
		.DELAY_ADJUSTMENT_MODE_RELATIVE("FIXED"),
		.PLLOUT_SELECT("GENCLK"),
		.FDA_FEEDBACK(4'b1111),
		.FDA_RELATIVE(4'b1111),
		.DIVR(4'd8),		// Divide by (DIVR+1)
		.DIVQ(3'd3),		// Divide by 2^(DIVQ)
		.DIVF(7'd47),		// Multiply by (DIVF+1)
		.FILTER_RANGE(3'b001)
	) plli (
		.PACKAGEPIN     (i_clk        ),
		.PLLOUTCORE     (clk_66mhz    ),
		.LOCK           (pll_locked  ),
		.BYPASS         (1'b0         ),
		.RESETB         (1'b1         )
	);

	assign	s_clk = clk_66mhz;
`endif

	initial begin
		message[ 0] = "H";
		message[ 1] = "e";
		message[ 2] = "l";
		message[ 3] = "l";
		message[ 4] = "o";
		message[ 5] = ",";
		message[ 6] = " ";
		message[ 7] = "W";
		message[ 8] = "o";
		message[ 9] = "r";
		message[10] = "l";
		message[11] = "d";
		message[12] = "!";
		message[13] = " ";
		message[14] = 8'h0d; // "\r";
		message[15] = "\n";
	end

	reg	[27:0]	counter;
	initial	counter = 28'hffffff0;
	always @(posedge s_clk)
		counter <= counter + 1'b1;

	wire		tx_busy;
	reg		tx_stb;
	reg	[3:0]	tx_index;
	reg	[7:0]	tx_data;

	initial	tx_index = 4'h0;
	always @(posedge s_clk)
		if ((tx_stb)&&(!tx_busy))
			tx_index <= tx_index + 1'b1;
	always @(posedge s_clk)
		// if ((tx_stb)&&(!tx_busy))
		if (rx_stb)
			tx_data <= rx_data;
		else
			tx_data <= message[tx_index];

	initial	tx_stb = 1'b0;
	always @(posedge s_clk)
		if (&counter)
			tx_stb <= 1'b1;
		else if ((tx_stb)&&(!tx_busy)&&(tx_index==4'hf))
			tx_stb <= 1'b0;

	wire		rx_stb;
	wire	[7:0]	rx_data;

	wire	[7:0]	w_pp_data, i_pp_data;

	pport	pporti(s_clk, rx_stb, rx_data,
			tx_stb, tx_data, tx_busy,
			i_pp_dir, i_pp_clk, i_pp_data, w_pp_data, o_pp_clkfb);

`ifdef	VERILATOR
	assign	o_pp_data = w_pp_data;
	// assign	io_pp_data = (i_pp_dir) ? 8'bzzzz_zzzz : w_pp_data;
`else
	ppio	theppio(i_pp_dir, io_pp_data, w_pp_data, i_pp_data);
`endif


	reg	[24:0]	ledctr;
	initial	ledctr = 0;
	always @(posedge s_clk)
		if ((!tx_busy)&&(tx_stb))
			ledctr <= 0;
		else if (!ledctr[24])
			ledctr <= ledctr + 1'b1;
	assign	o_ledg[0] = !ledctr[24];

	reg	[24:0]	onectr;
	initial	onectr = 0;
	always @(posedge s_clk)
		if (tx_index == 4'h3)
			onectr <= 0;
		else if (!onectr[24])
			onectr <= onectr + 1'b1;
	assign	o_ledg[1] = !onectr[24];

endmodule
