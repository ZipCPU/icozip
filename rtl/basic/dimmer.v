////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	dimmer.v
//
// Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
//
// Purpose:	A very simple demonstration project, showing how an LED can be
//		gradually increased in brightness, and then reset to do it
//	again.
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
//
`default_nettype none
//
module dimmer(i_clk, o_led);
  input  wire i_clk;
  output wire o_led;

reg [26:0] counter;
always @(posedge i_clk)
  counter <= counter + 1'b1;

always @(posedge i_clk)
  o_led <= (counter[3:0] < counter[26:23]);

endmodule

