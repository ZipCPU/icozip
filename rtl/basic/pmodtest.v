////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	pmodtest.v
//
// Project:	ICO Zip, iCE40 ZipCPU demonsrtation project, Basic Demos
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2016, Gisselquist Technology, LLC
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
module	pmodtest(i_clk, i_btn, o_ledg, o_ledr,
		o_pm1top, o_pm2top, o_pm3top, o_pm4top,
		o_pm1bot, o_pm2bot, o_pm3bot, o_pm4bot);
	parameter	CBITS = 27;
	input			i_clk;
	input		[1:0]	i_btn;
	output	wire	[1:0]	o_ledg;
	output	wire		o_ledr;
	output	wire	[3:0]	o_pm1top, o_pm2top, o_pm3top, o_pm4top;
	output	wire	[3:0]	o_pm1bot, o_pm2bot, o_pm3bot, o_pm4bot;

	reg [(CBITS-1):0]	ctr;
	initial ctr = 0;
	always @(posedge i_clk)
		ctr <= ctr + 1'b1;

	assign	o_ledg[1:0] = { (( ctr[CBITS-1]) & (i_btn[0]==0)),
				((!ctr[CBITS-1]) & (i_btn[1]==1)) };
	assign	o_ledr = (i_btn[0])|(i_btn[1]);

	assign	o_pm1top = 4'h0;
	assign	o_pm2top = 4'h0;
	assign	o_pm3top = 4'h0;
	assign	o_pm4top = 4'h8;

	assign	o_pm1bot = 4'h0;
	assign	o_pm2bot = 4'h0;
	assign	o_pm3bot = 4'h0;
	assign	o_pm4bot = 4'h0;

endmodule
