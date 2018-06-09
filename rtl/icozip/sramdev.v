////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sramdev.v
//
// Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
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
`default_nettype	none
//
module sramdev(i_clk, i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data,
			i_wb_sel,
		o_wb_ack, o_wb_stall, o_wb_data,
		o_ram_ce_n, o_ram_oe_n, o_ram_we_n, o_ram_addr, o_ram_data,
		i_ram_data);
	parameter	WBADDR = 16;
	input	wire		i_clk;
	// Wishbone
	//  inputs
	input	wire			i_wb_cyc, i_wb_stb, i_wb_we;
	input	wire	[(WBADDR-1):0]	i_wb_addr;
	input	wire	[31:0]		i_wb_data;
	input	wire	[3:0]		i_wb_sel;
	//  and outputs
	output	reg			o_wb_ack, o_wb_stall;
	output	reg	[31:0]		o_wb_data;
	// RAM control wires
	output	reg			o_ram_ce_n, o_ram_oe_n, o_ram_we_n;
	output	reg	[(WBADDR):0]	o_ram_addr;
	output	reg	[15:0]		o_ram_data;
	output	reg	[1:0]		o_ram_sel;
	input	wire	[15:0]		i_ram_data;

	
	reg	[1:0]	ram_state;
	reg	[15:0]	hi_data;
	reg	[1:0]	hi_sel;

	initial	ram_state = 1'b0;
	always @(posedge i_clk)
	begin
		o_ram_ce_n <= 1'b1;
		o_ram_oe_n <= 1'b1;
		o_ram_we_n <= 1'b1;
		o_wb_stall <= 1'b0;
		o_wb_ack <= 1'b0;
		case(ram_state)
		2'b00: begin // Idle state
			// If we just finished a second cycle
			o_wb_data[31:16] <= i_ram_data;
			if (o_ram_oe_n)
				o_wb_ack <= 1'b1;
			o_ram_addr <= { i_wb_addr, 1'b0 };
			o_ram_sel  <= 2'b00;
			o_ram_ce_n <= 1'b1;
			if (i_wb_stb)
			begin
				o_ram_oe_n <=  (i_wb_we);
				o_ram_we_n <= (!i_wb_we);
				ram_state  <= 2'b01;
				o_ram_data <= i_wb_data[15:0];
				o_ram_sel  <= i_wb_sel[1:0];
				hi_data    <= i_wb_data[31:16];
				hi_sel     <= i_wb_sel[3:2];
				o_wb_stall <= 1'b1;
			end end
		2'b01: begin
			o_ram_ce_n <= 1'b0;
			state <= 2'b10;
			end
		2'b10: begin // Second half of read/write
			ram_state  <= 2'b11;
			o_ram_ce_n <= 1'b1;
			// o_ram_oe_n <= o_ram_oe_n;
			// o_ram_we_n <= o_ram_we_n;
			o_ram_data <= hi_data;
			o_ram_sel  <= hi_sel;
			o_wb_stall <= 1'b0;
			o_wb_data[15:0] <= i_ram_data;
			o_ram_addr[0] <= 1'b1;
		2'b11: begin
			o_ram_ce_n <= 1'b0;
			state <= 2'b00;
			end
		end endcase
	end

endmodule
