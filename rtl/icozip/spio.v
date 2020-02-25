////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	spio.v
//
// Project:	ICO Zip, iCE40 ZipCPU demonstration project
//
// Purpose:	
//
//	With the USB cord on top, the board facing you, LED[0] is on the left.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2020, Gisselquist Technology, LLC
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

module	spio(i_clk, i_wb_cyc, i_wb_stb, i_wb_we, i_wb_data, i_wb_sel,
		o_wb_stall, o_wb_ack, o_wb_data, i_btn, i_led, o_led);
	parameter	NLED = 2, NBTN = 2;
	//
	input			i_clk;
	//
	input			i_wb_cyc, i_wb_stb, i_wb_we;
	input		[31:0]	i_wb_data;
	input		[3:0]	i_wb_sel;
	output	wire		o_wb_stall, o_wb_ack;
	output	wire	[31:0]	o_wb_data;
	//
	input		[(NBTN-1):0]	i_btn;
	input				i_led;
	output	reg	[(NLED-1):0]	o_led;

	genvar	k;

	initial	o_led    = 2'h0;
	generate
	for(k=0; k<NLED; k=k+1)
		always @(posedge i_clk)
			if ((i_wb_stb)&&(i_wb_we))
				o_led[k] <= (i_wb_data[k+8])?i_wb_data[k]:o_led[k];
	endgenerate

	assign	o_wb_stall = 1'b0;
	assign	o_wb_ack   = 1'b0;
	assign	o_wb_data = { 24'h00, {(4-NBTN){1'b0}}, i_btn,
				{(3-NLED){1'b0}}, i_led, o_led};

	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wb_sel };
	// Verilator lint_on  UNUSED
endmodule
