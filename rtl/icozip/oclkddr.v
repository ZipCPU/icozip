////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	oclkddr.v
// {{{
// Project:	ICO Zip, iCE40 ZipCPU demonstration project
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2018-2021, Gisselquist Technology, LLC
// {{{
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
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
// }}}
module	oclkddr (
		// {{{
		input	wire		i_clk,
		input	wire	[1:0]	i_ddr,
		output	wire		o_pin
		// }}}
	);

	SB_IO	#(
		// {{{
		.PIN_TYPE(6'b0100_01)
		// }}}
	) oddr(
		// {{{
		.OUTPUT_CLK(i_clk),
		.CLOCK_ENABLE(1'b1),
		.D_OUT_0(i_ddr[1]),
		.D_OUT_1(i_ddr[0]),
		.OUTPUT_ENABLE(1'b1),
		.PACKAGE_PIN(o_pin)
		// }}}
	);

endmodule
