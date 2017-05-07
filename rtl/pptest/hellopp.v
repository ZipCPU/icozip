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
		i_pp_dir, i_pp_clk, io_pp_data);
	//
	input		i_clk;
	output	wire	[1:0]	o_ledg;
	output	wire		o_ledr;
	//
	input	wire		i_pp_dir, i_pp_clk;
	inout	wire	[7:0]	io_pp_data;

	reg	[7:0]	message	[0:15];
	
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
	always @(posedge i_clk)
		counter <= counter + 1'b1;

	wire		tx_busy;
	reg		tx_stb;
	reg	[3:0]	tx_index;
	reg	[7:0]	tx_data;

	initial	tx_index = 4'h0;
	always @(posedge i_clk)
		if ((tx_stb)&&(!tx_busy))
			tx_index <= tx_index + 1'b1;
	always @(posedge i_clk)
		tx_data <= message[tx_index];

	initial	tx_stb = 1'b0;
	always @(posedge i_clk)
		if (&counter)
			tx_stb <= 1'b1;
		else if ((tx_stb)&&(!tx_busy)&&(tx_index==4'hf))
			tx_stb <= 1'b0;

	wire		rx_stb;
	wire	[7:0]	rx_data;

	wire	[7:0]	w_pp_data;
	pport	pporti(i_clk, rx_stb, rx_data,
			tx_stb, tx_data, tx_busy,
			i_pp_dir, i_pp_clk, io_pp_data, w_pp_data);
	assign	io_pp_data = (i_pp_dir) ? 8'bzzzz_zzzz : w_pp_data;


	reg	[24:0]	ledctr;
	initial	ledctr = 0;
	always @(posedge i_clk)
		if ((!tx_busy)&&(tx_stb))
			ledctr <= 0;
		else if (ledctr != {(25){1'b1}})
			ledctr <= ledctr + 1'b1;
	assign	o_ledg[0] = !ledctr[24];


endmodule
