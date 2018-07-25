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
		o_ram_sel, i_ram_data);
	parameter	WBADDR = 15;
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

	
	reg		ram_state;
	reg	[15:0]	lo_data;
	reg	[1:0]	lo_sel;
	reg		next_ack;
	reg		write;

	initial	ram_state  = 1'b0;
	initial	o_wb_ack   = 1'b0;
	initial	o_wb_stall = 1'b0;
	initial	next_ack   = 1'b0;
	initial	o_ram_ce_n = 1'b1;
	initial	o_ram_oe_n = 1'b1;
	initial	o_ram_we_n = 1'b1;
	initial	o_ram_sel  = 2'b11;
	always @(posedge i_clk)
	begin
		o_ram_ce_n <= 1'b1;
		o_ram_oe_n <= 1'b1;
		o_ram_we_n <= 1'b1;
		o_wb_stall <= 1'b0;
		o_wb_ack   <= 1'b0;
		next_ack   <= 1'b0;
		case(ram_state)
		1'b0: begin // Idle state
			// If we just finished a second cycle
			o_ram_addr <= { i_wb_addr, 1'b0 };
			o_ram_sel  <= 2'b11;
			o_ram_ce_n <= 1'b1;
			o_wb_data[15:0] <= i_ram_data;
			o_wb_ack  <= (next_ack)&&(i_wb_cyc);
			//
			o_ram_data <= i_wb_data[31:16];
			o_ram_sel  <= i_wb_sel[3:2];
			if (i_wb_stb)
			begin
				// Start a cycle
				o_ram_ce_n <= 1'b0;
				o_ram_oe_n <=  (i_wb_we);
				o_ram_we_n <= (!i_wb_we);
				write      <= i_wb_we;
				ram_state  <= 1'b1;
				//
				lo_data    <= i_wb_data[15:0];
				lo_sel     <= i_wb_sel[1:0];
				o_wb_stall <= 1'b1;
				next_ack   <= 1'b1;
			end end
		1'b1: begin
			o_wb_data[31:16] <= i_ram_data;
			o_ram_data       <= lo_data;
			o_ram_sel        <= lo_sel;
			o_ram_ce_n       <= o_ram_ce_n;
			o_ram_oe_n       <= o_ram_oe_n;
			o_ram_we_n       <= o_ram_we_n;
			next_ack   <= (next_ack)&&(i_wb_cyc);
			o_wb_stall <= 1'b0;
			o_ram_addr[0] <= 1'b1;
			ram_state <= 1'b0;
			end
		endcase
	end

`ifdef	FORMAL
	reg	f_past_valid, f_reset;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;
	always @(*)
		f_reset = !f_past_valid;

	parameter	F_LGDEPTH = 3;
	wire	[F_LGDEPTH-1:0]	f_nreqs, f_nacks, f_outstanding;

	fwb_slave #(
		.AW(WBADDR),.DW(32),.F_MAX_STALL(4),.F_MAX_ACK_DELAY(4),
			.F_LGDEPTH(F_LGDEPTH),.F_MAX_REQUESTS(2)
		) fwb(i_clk, f_reset,
		i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, i_wb_sel,
			o_wb_ack, o_wb_stall, o_wb_data, 1'b0,
		f_nreqs, f_nacks, f_outstanding);

	always @(posedge i_clk)
		cover((i_wb_cyc)&&(o_wb_ack)&&(!$past(write)));

	always @(posedge i_clk)
		cover((i_wb_cyc)&&(o_wb_ack)&&($past(write)));

	always @(posedge i_clk)
	if (f_past_valid)
		assert(o_ram_ce_n != ((($past(i_wb_stb))&&(!$past(o_wb_stall)))
					||($past(ram_state))));

	always @(posedge i_clk)
	if ((f_past_valid)&&($past((!next_ack)||(!i_wb_cyc))))
		assert(!o_wb_ack);

	always @(*)
		assert(o_wb_stall == ram_state);

	always @(posedge i_clk)
	if (o_ram_ce_n)
	begin
		assert(o_ram_oe_n);
		assert(o_ram_we_n);
		assert(o_ram_sel == 2'b11);
	end

	always @(*)
	if (!o_ram_ce_n)
		assert(o_ram_we_n != o_ram_oe_n);

	always @(posedge i_clk)
	if (($past(o_ram_ce_n))||($past(o_ram_ce_n,2)))
		assert(!o_wb_ack);
	always @(posedge i_clk)
	if (o_wb_ack)
	begin
		assert(o_wb_data[15:0] == $past(i_ram_data));
		assert(o_wb_data[31:16] == $past(i_ram_data,2));
	end

	(* anyconst *)	reg	[15:0]	f_addr;
			reg	[15:0]	f_data;

	always @(posedge i_clk)
	if ((!o_ram_ce_n)&&(!o_we_n)&&(o_ram_addr == f_addr))
	begin
		if (o_ram_sel[1])
			f_data[15:8] <= o_ram_data[15:8];
		if (o_ram_sel[0])
			f_data[7:0] <= o_ram_data[7:0];
	end

	always @(*)
	if ((!o_ram_ce_n)&&(!o_ram_oe_n))
		assume(i_ram_data == f_data);

	always @(posedge i_clk)
	if (((o_wb_ack)&&($past(o_wb_addr[14:0],3)== f_addr[15:1]))
			&&(!$past(o_wb_we,3)))
	begin
		if (f_addr[0])
			assert(o_wb_data[15:0] == f_data);
		else
			assert(o_wb_data[31:16] == f_data);
	end
`endif
`ifdef	VERIFIC
	assert property (@(posedge i_clk)
		disable iff (!i_wb_cyc)
		(i_wb_stb)&&(!o_wb_stall)
		|=> (ram_state)&&(!o_ram_ce_n)&&(o_wb_stall)
			&&(o_ram_we_n == !$past(i_wb_we))
		##1 (!ram_state)&&(!o_ram_ce_n)&&(!o_wb_stall)
				&&(o_wb_data[31:16] == $past(i_ram_data))
				&&(o_ram_we_n == $past(o_ram_we_n))
		##1 (o_wb_ack)&&(o_wb_data[31:16] == o_wb_data[31:16])
			&&(o_wb_data[15:0] == $past(i_ram_data)));

	assert property (@(posedge i_clk)
		disable iff (!i_wb_cyc)
		(i_wb_stb)&&(!o_wb_stall)&&(o_wb_we)
		|=> (ram_state)&&(!o_ram_ce_n)&&(o_wb_stall)
			&&(!o_ram_we_n)&&(!o_ram_addr[0])
				&&(o_ram_data==$past(o_wb_data[31:16]))
		##1 (!ram_state)&&(!o_ram_ce_n)&&(!o_wb_stall)
				&&(o_wb_data[31:16] == $past(i_ram_data))
				&&(o_ram_we_n == $past(o_ram_we_n))
				&&(o_ram_data==$past(o_wb_data[15:0],2))
		##1 (o_wb_ack);
`endif
endmodule
