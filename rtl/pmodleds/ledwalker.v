////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	ledwalker.v
//
// Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
//
// Purpose:	Turn on each of the 8 LED's in the PMod LED8 in succession, one
//		by one, for the purpose of verifying that they each work and
//	that the wiring is correct.
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
`default_nettype none
`define	FASTWALKER
//
module	ledwalker(i_clk, o_led);
	input	wire		i_clk;
	output	reg	[7:0]	o_led;

	reg	pps;
	reg	[31:0]	time_counter;
	always @(posedge i_clk)
		{ pps, time_counter } <= time_counter + 32'd43;

`ifdef	FASTWALKER
	wire	[2:0]	led_posn;
	assign	led_posn = time_counter[31:29];
`else
	reg	[2:0]	led_posn;
	always @(posedge i_clk)
		if (pps)
			led_posn <= led_posn + 1'b1;
`endif

	always @(posedge i_clk)
	begin
		o_led[0] <= (led_posn == 3'h0);
		o_led[1] <= (led_posn == 3'h1);
		o_led[2] <= (led_posn == 3'h2);
		o_led[3] <= (led_posn == 3'h3);
		o_led[4] <= (led_posn == 3'h4);
		o_led[5] <= (led_posn == 3'h5);
		o_led[6] <= (led_posn == 3'h6);
		o_led[7] <= (led_posn == 3'h7);
	end

endmodule
