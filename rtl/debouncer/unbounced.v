////////////////////////////////////////////////////////////////////////////////
//
// Filename:	unbounced.v
//
// Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
//
// Purpose:	To measure the "bouncing" characteristics of an FPGA input
//		device, such as a button.  Specifically, we'll measure here:
//
//	1. How long it takes from an initial change until things settle out
//
//	2. How many times the data changes between the initial input and the
//		final bounce/settling time.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017-2020, Gisselquist Technology, LLC
//
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of the GNU General Public License as published
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
module	unbounced(i_clk, i_reset, i_in, o_transitions, o_max_clock);
	parameter	NIN=2;
	input	wire			i_clk, i_reset;
	input	wire	[(NIN-1):0]	i_in;
	output	reg	[31:0]		o_transitions, o_max_clock;

	reg			triggered;
	reg	[31:0]		clock;
	reg	[(NIN-1):0]	q_in, r_in, r_last;

	always @(posedge i_clk)
		q_in <= i_in;
	always @(posedge i_clk)
		r_in <= q_in;
	always @(posedge i_clk)
		r_last <= r_in;

	always @(posedge i_clk)
		if (i_reset)
			triggered <= 1'b0;
		else if (r_last != r_in)
			triggered <= 1'b1;

	always @(posedge i_clk)
		if (i_reset)
			clock <= 0;
		else if ((triggered)&&(!clock[31]))
			clock <= clock + 1'b1;

	initial	o_max_clock = 0;
	always @(posedge i_clk)
		if (i_reset)
			o_max_clock <= 0;
		else if (r_last != r_in)
			o_max_clock <= clock;

	initial	o_transitions = 0;
	always @(posedge i_clk)
		if (i_reset)
			o_transitions <= 0;
		else if (r_last != r_in)
			o_transitions <= o_transitions + 1'b1;

endmodule
