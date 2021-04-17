////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sramdev.v
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
// Copyright (C) 2015-2021, Gisselquist Technology, LLC
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
// with this program.  (It's in the $(ROOT)/doc directory, run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype	none
// }}}
module sramdev #(
		// {{{
		parameter	WBADDR = 15
		// }}}
	) (
		// {{{
		input	wire			i_clk,
		// Wishbone
		//  inputs
		input	wire			i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[(WBADDR-1):0]	i_wb_addr,
		input	wire	[31:0]		i_wb_data,
		input	wire	[3:0]		i_wb_sel,
		//  and outputs
		output	reg			o_wb_stall, o_wb_ack,
		output	reg	[31:0]		o_wb_data,
		// RAM control wires
		output	reg			o_ram_ce_n, o_ram_oe_n, o_ram_we_n,
		output	reg	[(WBADDR):0]	o_ram_addr,
		output	reg	[15:0]		o_ram_data,
		output	reg	[1:0]		o_ram_sel,
		input	wire	[15:0]		i_ram_data
		// }}}
	);

	// Local declarations
	// {{{
	reg	[2:0]	ram_state;
	reg	[31:0]	data;
	reg		next_ack;
	reg		write;
	reg	[3:0]	sel;
	// }}}

	initial	ram_state  = 3'b0;
	initial	sel        = 4'hf;
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

		if (ram_state != 3'b000)
		begin
			ram_state <= ram_state + 1'b1;
			next_ack   <= (next_ack)&&(i_wb_cyc);
		end

		case(ram_state)
		3'b00: begin // Idle state
			// If we just finished a second cycle
			//
			// Complete the last cycle
			o_wb_data[15:0] <= i_ram_data;
			//
			//
			o_ram_addr <= { i_wb_addr, 1'b0 };
			o_ram_sel  <= 2'b11;
			o_ram_ce_n <= 1'b1;
			o_ram_data <= i_wb_data[31:16];
			data       <= i_wb_data[31:0];
			sel        <= (!i_wb_we)? 4'h0 : ~i_wb_sel;
			write      <= i_wb_we;
			next_ack   <= 1'b0;
			if (i_wb_stb)
			begin
				// Start a cycle
				o_ram_ce_n <= 1'b0;
				o_ram_oe_n <=  (i_wb_we);
				o_ram_we_n <= (!i_wb_we);
				//
				ram_state  <= 3'b001;
				//
				next_ack   <= 1'b1;
				o_wb_stall <= 1'b1;
			end end
		3'b001: begin
			o_ram_ce_n <= 1'b0;
			o_ram_oe_n <=  (write);
			o_ram_we_n <= (!write);
			o_ram_sel  <= sel[3:2];
			//
			o_wb_stall <= 1'b1;
			end
		3'b010: begin
			o_ram_ce_n <= 1'b0;
			o_ram_oe_n <=  (write);
			o_ram_we_n <= (!write);
			o_ram_sel  <= sel[3:2];
			//
			o_wb_stall <= 1'b1;
			end
		3'b011: begin
			o_ram_ce_n    <= 1'b1;
			o_ram_oe_n    <= 1'b1;
			o_ram_we_n    <= 1'b1;
			o_ram_sel     <= 2'b11;
			o_ram_data    <= data[15:0];
			o_ram_addr[0] <= 1'b1;
			o_wb_data[31:16] <= i_ram_data;
			//
			o_wb_stall <= 1'b1;
			end
		3'b100: begin
			o_ram_ce_n <= 1'b0;
			o_ram_oe_n <=  (write);
			o_ram_we_n <= (!write);
			o_ram_sel  <= 2'b11;
			//
			o_wb_stall <= 1'b1;
			end
		3'b101: begin
			o_ram_ce_n <= 1'b0;
			o_ram_oe_n <=  (write);
			o_ram_we_n <= (!write);
			o_ram_sel  <= sel[1:0];
			//
			o_wb_stall <= 1'b1;
			end
		3'b110: begin
			o_ram_ce_n <= 1'b0;
			o_ram_oe_n <=  (write);
			o_ram_we_n <= (!write);
			o_ram_sel  <= sel[1:0];
			//
			o_wb_stall <= 1'b1;
			end
		3'b111: begin
			o_ram_ce_n <= 1'b1;
			o_ram_oe_n <= 1'b1;
			o_ram_we_n <= 1'b1;
			o_ram_sel  <= 2'b11;
			o_wb_data[15:0] <= i_ram_data;
			//
			o_wb_stall <= 1'b0;
			o_wb_ack  <= (next_ack)&&(i_wb_cyc);
			end
		endcase
	end

	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, data[31:16] };
	// Verilator lint_on  UNUSED
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
		.AW(WBADDR),.DW(32),.F_MAX_STALL(6),.F_MAX_ACK_DELAY(6),
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
	if ((f_past_valid)&&($past((!next_ack)||(!i_wb_cyc))))
		assert(!o_wb_ack);

	always @(*)
		assert(o_wb_stall == (ram_state!=0));

	always @(posedge i_clk)
	if (o_ram_ce_n)
	begin
		assert(o_ram_oe_n);
		assert(o_ram_we_n);
		assert(o_ram_sel == 2'b11);
		assert(ram_state[1:0] == 2'b00);
		assert(o_wb_stall == ram_state[2]);
	end else begin
		assert(ram_state[1:0] != 2'b00);
		assert(o_ram_oe_n == !o_ram_we_n);
		assert(write == !o_ram_we_n);

		if (ram_state[1:0] == 2'b01)
			assert(o_ram_sel == 2'b11);
		assert(o_wb_stall);
		assert(!o_wb_stall);
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
	if ((f_past_valid)&&(!o_ram_ce_n)&&(!o_we_n)&&(o_ram_addr == f_addr)
			&&($stable(o_ram_data))&&($stable(o_ram_addr)))
	begin
		if (!o_ram_sel[1])
			f_data[15:8] <= o_ram_data[15:8];
		if (!o_ram_sel[0])
			f_data[7:0] <= o_ram_data[7:0];
	end

	always @(*)
	case(ram_state)
	3'b000: begin
		assert(!o_wb_stall);
		end
	3'b001: begin
		assert(o_wb_stall);
		assert(!o_wb_ack);
		//
		assert(!o_ram_ce_n);
		assert(o_ram_we_n == !o_ram_oe_n);
		assert(o_ram_sel == 2'b11);
		assert(o_addr[0] == 1'b0);
		end
	3'b010: begin
		assert(o_wb_stall);
		assert(!o_wb_ack);
		//
		assert(!o_ram_ce_n);
		assert(o_ram_we_n == !o_ram_oe_n);
		assert(o_ram_oe_n == write);
		assert(o_addr[0] == 1'b0);
		end
	3'b011: begin
		assert(o_wb_stall);
		assert(!o_wb_ack);
		//
		assert(!o_ram_ce_n);
		assert(o_ram_we_n == !o_ram_oe_n);
		assert(o_ram_oe_n == write);
		assert(o_addr[0] == 1'b0);
		end
	3'b100: begin
		assert(o_wb_stall);
		assert(!o_wb_ack);
		//
		assert(o_ram_ce_n);
		assert(o_ram_we_n);
		assert(o_ram_oe_n);
		assert(o_ram_sel == 2'b11);
		end
	3'b101: begin
		assert(o_wb_stall);
		assert(!o_wb_ack);
		//
		assert(!o_ram_ce_n);
		assert(o_ram_we_n == !o_ram_oe_n);
		assert(o_ram_oe_n == write);
		assert(o_ram_sel == 2'b11);
		assert(o_addr[0] == 1'b1);
		end
	3'b110: begin
		assert(o_wb_stall);
		assert(!o_wb_ack);
		//
		assert(!o_ram_ce_n);
		assert(o_ram_we_n == !o_ram_oe_n);
		assert(o_ram_oe_n == write);
		assert(o_addr[0] == 1'b1);
		end
	3'b111: begin
		assert(o_wb_stall);
		assert(!o_wb_ack);
		//
		assert(!o_ram_ce_n);
		assert(o_ram_we_n == !o_ram_oe_n);
		assert(o_ram_oe_n == write);
		assert(o_addr[0] == 1'b1);
		end
	endcase

`endif
`ifdef	VERIFIC
	reg	[31:0]	f_tx_data;
	always @(posedge i_clk)
	if (!o_wb_stall)
		f_tx_data <= i_wb_data;

	assert property (@(posedge i_clk)
		(i_wb_stb)&&(!o_wb_stall)
		|=> (ram_state==3'b001)&&(!o_ram_ce_n)
			&&(o_wb_stall)&&(!o_wb_ack)&&(write == !$past(i_wb_we))
			&&(f_tx_data == $past(f_tx_data))
			&&((!write)||(sel == 4'h0))
			&&((write)||(sel == ~$past(i_wb_sel)))
			&&(o_ram_sel  == 2'b11)
			&&(o_ram_we_n == !write)
			&&(o_ram_oe_n ==  write)
		##1 (ram_state==3'b010)&&(!o_ram_ce_n)
			&&(o_wb_stall)&&(!o_wb_ack)&&($stable(write))
			&&((!write)||(sel == 4'h0))&&($stable(sel))
			&&($stable(f_tx_data))&&(o_ram_data == f_tx_data[31:16])
			&&(o_ram_sel  == sel[3:2])
			&&(o_ram_we_n == !write)
			&&(o_ram_oe_n ==  write)
		##1 (ram_state==3'b011)&&(!o_ram_ce_n)
			&&(o_wb_stall)&&(!o_wb_ack)&&($stable(write))
			&&((!write)||(sel == 4'h0))&&($stable(sel))
			&&($stable(f_tx_data))&&(o_ram_data == f_tx_data[31:16])
			&&(o_ram_sel  == sel[3:2])
			&&(o_ram_we_n == !write)
			&&(o_ram_oe_n ==  write)
		##1 (ram_state==3'b100)&&(o_ram_ce_n)
			&&(o_wb_stall)&&(!o_wb_ack)&&($stable(write))
			&&((!write)||(sel == 4'h0))&&($stable(sel))
			&&(o_ram_sel  == 2'b11)
			&&(o_ram_we_n == 1'b1)
			&&(o_ram_oe_n == 1'b1)
		##1 (ram_state==3'b101)&&(!o_ram_ce_n)
			&&(o_wb_stall)&&(!o_wb_ack)&&($stable(i_wb_we))
			&&((!write)||(sel == 4'h0))&&($stable(sel))
			&&(o_ram_sel  == 2'b11)
			&&(o_ram_we_n == !write)
			&&(o_ram_oe_n ==  write)
		##1 (ram_state==3'b110)&&(!o_ram_ce_n)
			&&(o_wb_stall)&&(!o_wb_ack)&&($stable(write))
			&&((!write)||(sel == 4'h0))
			&&(o_ram_sel  == sel[1:0])
			&&($stable(f_tx_data))&&(o_ram_data == f_tx_data[15:0])
			&&(o_ram_we_n == !write)
			&&(o_ram_oe_n ==  write)
		##1 (ram_state==3'b111)&&(!o_ram_ce_n)
			&&(o_wb_stall)&&(!o_wb_ack)&&($stable(write))
			&&((!write)||(sel == 4'h0))
			&&($stable(f_tx_data))&&(o_ram_data == f_tx_data[15:0])
			&&(o_ram_sel  == sel[1:0])
			&&(o_ram_we_n == !write)
			&&(o_ram_oe_n ==  write)
		##1 (ram_state==3'b000)&&(o_ram_ce_n)
			&&(!o_wb_stall)
			&&(o_ram_sel  == 2'b11)
			&&(o_ram_we_n == 1'b1)
			&&(o_ram_oe_n == 1'b1));

	assert property (@(posedge i_clk)
		disable iff (!i_wb_cyc)
		(i_wb_stb)&&(!o_wb_stall)
		|=> (next_ack)&&(!o_wb_ack) [7] ##1 o_wb_ack);

	assert property (@(posedge i_clk)
		disable iff (!i_wb_cyc)
		(i_wb_stb)&&(!o_wb_stall)
		##3 (i_ram_data == f_data)
		##4 |=> (o_wb_ack)&&(o_wb_data[31:16] == f_data));

	assert property (@(posedge i_clk)
		disable iff (!i_wb_cyc)
		(i_wb_stb)&&(!o_wb_stall)
		##7 (i_ram_data == f_data)
		|=> (o_wb_ack)&&(o_wb_data[15:0] == f_data));
`endif
endmodule
