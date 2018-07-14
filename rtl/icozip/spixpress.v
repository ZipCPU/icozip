////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	spixpress.v
//
// Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
//
// Purpose:	This module is intended to be a low logic flash controller.
// 		It uses the 8'h03 read command from the flash, and so it
// 	cannot be used with a clock speed any greater than 50MHz.
//
//	Although this controller has no erase or program capability, it
//	includes a control port.  When using the control port, you should be
//	able to send arbitrary commands to the flash--but not read from the
//	flash during that time.
//
// Actions:
// 	Control Port
// 	[31:9]	Unused bits, ignored on write, read as zero
// 	[8]	CS_n
// 			Can be activated via a write to the control port.
// 			This will render the memory addresses unreadable.
// 			Write a '1' to this value to return the memory to
// 			normal operation.
// 	[7:0]	BYTE-DATA
// 			Following a write to the control port where bit [8]
// 			is low, the controller will send bits [7:0] out the
// 			SPI port, top bit first.  Once accomplished, the
// 			control port may be read to see what values were
// 			read from the SPI port.  Those values will be stored
// 			in these same bits [7:0].
// 
//	Memory
//		Returns the data from the address read
//
//		Requires that the CS_N setting within the control port be
//		deactivated, otherwise requests to read from memory
//		will simply return the control port register immediately
//		without doing anything.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2018, Gisselquist Technology, LLC
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
`default_nettype	none
//
module	spixpress(i_clk, i_reset,
		i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data,
			o_wb_stall, o_wb_ack, o_wb_data,
		o_spi_cs_n, o_spi_sck, o_spi_mosi, i_spi_miso);
	//
	parameter [0:0]	OPT_PIPE = 1'b1;
	//
	input			i_clk, i_reset;
	//
	input			i_wb_cyc, i_wb_stb, i_wb_we;
	input		[22:0]	i_wb_addr;
	input		[31:0]	i_wb_data;
	output	reg		o_wb_stall, o_wb_ack;
	output	reg	[31:0]	o_wb_data;
	//
	output	reg		o_spi_cs_n, o_spi_sck, o_spi_mosi;
	input	wire		i_spi_miso;
	//
	//

	reg		cfg_user_mode;
	reg	[31:0]	wdata_pipe;
	reg	[6:0]	ack_delay;

	wire	[21:0]	next_addr;

	wire	user_request, bus_request, next_request;

	assign	user_request = (i_wb_stb)&&(!o_wb_stall)&&(i_wb_addr[22])
					&&(i_wb_we)&&(i_wb_data[8]);
	assign	bus_request  = (i_wb_stb)&&(!o_wb_stall)&&(!i_wb_addr[22])
					&&(!i_wb_we)&&(!cfg_user_mode);
	assign	next_request = (OPT_PIPE)&&(i_wb_stb)&&(!i_wb_we)
			&&(!i_wb_addr[22])&&(i_wb_addr[21:0] == next_addr);


	initial	wdata_pipe = 0;
	always @(posedge i_clk)
	if (bus_request)
		wdata_pipe <= { 8'h03, i_wb_addr[21:0], 2'b00 };
	else if (user_request)
		wdata_pipe <= { i_wb_data[7:0], 24'h0 };
	else
		wdata_pipe <= { wdata_pipe[30:0], 1'b0 };

	assign	o_spi_mosi = wdata_pipe[31];

	initial	ack_delay = 0;
	always @(posedge i_clk)
	if ((i_reset)||(!i_wb_cyc))
		ack_delay <= 0;
	else if (bus_request)
		ack_delay <= 7'd64;
	else if (user_request)
		ack_delay <= 7'd8;
	else if (ack_delay != 0)
		ack_delay <= ack_delay - 1;

	initial	o_wb_ack = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_wb_ack <= 0;
	else if (ack_delay == 1)
		o_wb_ack <= (i_wb_cyc);
	else if ((i_wb_stb)&&(!o_wb_stall)&&(!bus_request)&&(!user_request))
		o_wb_ack <= 1'b1;
	else
		o_wb_ack <= 0;

	initial	cfg_user_mode = 0;
	always @(posedge i_clk)
	if (i_reset)
		cfg_user_mode <= 0;
	else if ((i_wb_stb)&&(!o_wb_stall)&&(i_wb_we)&&(i_wb_addr[22]))
		cfg_user_mode <= !i_wb_data[8];

	always @(posedge i_clk)
	if (o_spi_sck)
	begin
		if (cfg_user_mode)
			o_wb_data <= { 23'h0, !cfg_user_mode, o_wb_data[6:0], i_spi_miso };
		else
			o_wb_data <= { o_wb_data[30:0], i_spi_miso };
	end

	initial	o_spi_cs_n = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		o_spi_cs_n <= 1'b1;
	else if ((!i_wb_cyc)&&(!cfg_user_mode))
		o_spi_cs_n <= 1'b1;
	else if (bus_request)
		o_spi_cs_n <= 1'b0;
	else if (user_request)
		o_spi_cs_n <= !i_wb_data[8];
	else if (cfg_user_mode)
		o_spi_cs_n <= !cfg_user_mode;
	else if ((ack_delay == 1)&&(!cfg_user_mode))
		o_spi_cs_n <= 1'b1;

	initial	o_spi_sck = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_spi_sck <= 1'b0;
	else if ((bus_request)||(user_request))
		o_spi_sck <= 1'b1;
	else if ((i_wb_cyc)&&(ack_delay > 1))
		o_spi_sck <= 1'b1;
	else
		o_spi_sck <= 1'b0;

	initial	o_wb_stall = 1'b0;
	always @(posedge i_clk)
	if (!i_wb_cyc)
		o_wb_stall <= 1'b0;
	else if ((bus_request)||(user_request))
		o_wb_stall <= 1'b1;
	else if ((OPT_PIPE)&&(next_request)&&(ack_delay == 2))
		o_wb_stall <= 1'b0;
	else
		o_wb_stall <= (ack_delay > 1);

	generate if (OPT_PIPE)
	begin
		reg	[21:0]	r_next_addr;
		always @(posedge i_clk)
		if ((i_wb_stb)&&(!o_wb_stall))
			r_next_addr <= i_wb_addr[21:0] + 1'b1;

		assign	next_addr = r_next_addr;

	end else begin

		assign next_addr = 0;

	end endgenerate

	// verilator lint_off UNUSED
	wire	[22:0]	unused;
	assign	unused = i_wb_data[31:9];
	// verilator lint_on  UNUSED
`ifdef	FORMAL
	parameter	[0:0]	F_OPT_COVER = 1'b0;

	reg	f_past_valid;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	wire	f_reset;
	assign	f_reset = (!f_past_valid);
	always @(*)
		assume(i_reset == f_reset);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		assert(o_spi_cs_n == 1'b1);
		assert(o_spi_sck  == 1'b0);
		//
		assert(ack_delay    ==  0);
		assert(cfg_user_mode == 0);
		assert(o_wb_stall == 1'b0);
		assert(o_wb_ack   == 1'b0);
	end

	localparam	F_LGDEPTH = 7;
	wire	[F_LGDEPTH-1:0]	f_nreqs, f_nacks, f_outstanding;

	fwb_slave #( .AW(23), .F_MAX_STALL(7'd70), .F_MAX_ACK_DELAY(7'd70),
			.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_REQUESTS((OPT_PIPE) ? 0 : 1'b1),
			.F_OPT_MINCLOCK_DELAY(1'b1)
		) slavei(i_clk, (i_reset)||(f_reset),
		i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, 4'hf,
			o_wb_ack, o_wb_stall, o_wb_data, 1'b0,
			f_nreqs, f_nacks, f_outstanding);

	always @(posedge i_clk)
	if (!f_past_valid)
		assert(f_outstanding == 0);
	else if ((!i_reset)&&(i_wb_cyc))
	begin
		if (((!OPT_PIPE)||($past(o_spi_cs_n)))
			&&($past(i_wb_stb))&&(!$past(o_wb_stall))&&(i_wb_cyc))
			assert(f_outstanding == 1);
		if (ack_delay > 0)
			assert((o_wb_ack)||(f_outstanding == 1));
	end

	always @(*)
	if (OPT_PIPE)
		assert(f_outstanding <= 2);
	else
		assert(f_outstanding <= 1);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_wb_stb))&&(!$past(o_wb_stall)))
	begin
		if ((i_wb_cyc)&&(!i_reset)
				&&(!$past(user_request))&&(!$past(bus_request)))
			assert((o_wb_ack)&&(f_outstanding == 1));
	end

	always @(*)
		assert(o_spi_sck == (ack_delay > 0));
	always @(*)
	if (o_spi_cs_n)
		assert(!o_spi_sck);

	always @(posedge i_clk)
	if (ack_delay == 0)
		assert((o_wb_ack)||(f_outstanding == 0));

	always @(posedge i_clk)
	if (ack_delay == 0)
		assert((o_wb_ack)||(!o_wb_stall));

	always @(*)
		assert(ack_delay < 7'd65);

	always @(*)
	if (cfg_user_mode)
		assert(ack_delay < 7'd9);

	always @(*)
	if ((!OPT_PIPE)&&(!cfg_user_mode)&&(!o_spi_cs_n))
		assert((o_spi_sck)&&(o_wb_stall));

	always @(*)
		assert((!bus_request)||(!user_request));

	generate if (F_OPT_COVER)
	begin

		always @(posedge i_clk)
			cover(o_wb_ack&&(!$past(bus_request))
				&&(!$past(user_request)));

		reg	f_pending_user_request, f_pending_bus_request;

		initial	f_pending_user_request = 1'b0;
		always @(posedge i_clk)
		if ((i_reset)||(!i_wb_cyc))
			f_pending_user_request <= 1'b0;
		else if (user_request)
			f_pending_user_request <= 1'b1;
		else if (o_wb_ack)
			f_pending_user_request <= 1'b0;

		initial	f_pending_bus_request = 1'b0;
		always @(posedge i_clk)
		if ((i_reset)||(!i_wb_cyc))
			f_pending_bus_request <= 1'b0;
		else if (bus_request)
			f_pending_bus_request <= 1'b1;
		else if (o_wb_ack)
			f_pending_bus_request <= 1'b0;

		always @(posedge i_clk)
			cover((o_wb_ack)&&(f_pending_user_request));

		always @(posedge i_clk)
			cover((o_wb_ack)&&(f_pending_bus_request));

		if (OPT_PIPE)
		begin

			always @(posedge i_clk)
				cover((!o_wb_stall)&&(f_pending_bus_request)&&(ack_delay == 1));
			always @(posedge i_clk)
				cover((next_request)&&(f_pending_bus_request)&&(ack_delay == 2));
		end

	end endgenerate

`endif
`ifdef	VERIFIC
	reg	[21:0]	f_last_addr, f_next_addr;

	always @(posedge i_clk)
	if (bus_request)
		f_last_addr <= i_addr[21:0];

	always @(*)
		f_next_addr <= f_last_addr + 1'b1;

	// Writes are immediately returned
	assert property (@(posedge i_clk)
		(i_wb_stb)&&(!o_wb_stall)&&(!user_request)&&(!bus_request)
		|=> (o_wb_ack)&&(!o_wb_stall));

	assert property (@(posedge i_clk)
		(i_wb_stb)&&(!o_wb_stall)&&(!o_spi_cs_n)&&(!i_wb_we)
		|-> (i_wb_addr == f_last_addr + 1)
		);

	sequence READ_COMMAND
		// Send command 8'h03
		(f_last_addr == $past(i_wb_addr))
				&&(!o_spi_cs_n)&&(o_spi_sck)&&(!o_spi_mosi)
		##1 ( ((f_last_addr == $past(f_last_addr))
			&&(!o_spi_cs_n)&&(o_spi_sck)) throughout
				(!o_spi_mosi)
				##1 (!o_spi_mosi)
				##1 (!o_spi_mosi)
				##1 (!o_spi_mosi)
				##1 (!o_spi_mosi)
				##1 ( o_spi_mosi)
				##1 ( o_spi_mosi));
	endsequence

	sequence	SEND_ADDRESS
		(((f_last_addr == $past(last_addr))&&(!o_spi_cs_n)&&(o_spi_sck))
		throughout
			(o_spi_mosi == f_last_addr[21])
			##1 (o_spi_mosi == f_last_addr[20])
			##1 (o_spi_mosi == f_last_addr[19])
			##1 (o_spi_mosi == f_last_addr[18])
			##1 (o_spi_mosi == f_last_addr[17])
			##1 (o_spi_mosi == f_last_addr[16])
			##1 (o_spi_mosi == f_last_addr[15])
			##1 (o_spi_mosi == f_last_addr[14])
			##1 (o_spi_mosi == f_last_addr[13])
			##1 (o_spi_mosi == f_last_addr[12])
			##1 (o_spi_mosi == f_last_addr[11])
			##1 (o_spi_mosi == f_last_addr[10])
			##1 (o_spi_mosi == f_last_addr[ 9])
			##1 (o_spi_mosi == f_last_addr[ 8])
			##1 (o_spi_mosi == f_last_addr[ 7])
			##1 (o_spi_mosi == f_last_addr[ 6])
			##1 (o_spi_mosi == f_last_addr[ 5])
			##1 (o_spi_mosi == f_last_addr[ 4])
			##1 (o_spi_mosi == f_last_addr[ 3])
			##1 (o_spi_mosi == f_last_addr[ 2])
			##1 (o_spi_mosi == f_last_addr[ 1])
			##1 (o_spi_mosi == f_last_addr[ 0])
			##1 (o_spi_mosi == 1'b0)
			##1 (o_spi_mosi == 1'b0));
	endsequence

	sequence	READ_DATA
		(!o_spi_cs_n)&&(o_spi_sck)&&(o_wb_data == $past(o_wb_data[30:0], i_spi_miso))
		[*32] ##1
		(o_wb_ack)&&(o_wb_data == $past(o_wb_data[30:0], i_spi_miso));
	endsequence

	assert property (@(posedge i_clk)
		(i_wb_stb)&&(!o_wb_stall)&&(!i_wb_we)&&(o_spi_cs_n)
			&&(!cfg_user_mode)&&(!i_wb_addr[22])
		// Send command 8'h03
		|=> READ_COMMAND
		##1 ((f_last_addr == $past(f_last_addr)) throughout
				SEND_ADDRESS(lastaddr))
		##1 READ_DATA);
`endif
endmodule
// Usage on an iCE40
// 		W/o Pipe	Piped
// Cells	156		243
// SB_CARRY	 10		 30
// SB_DFF	 21		 21
// SB_DFFE	 10		 32
// SB_DFFESR	 31		 31
// SB_DFFSR	 10		 10
// SB_DFFSS	  2		  2
// SB_LUT4	 72		117
//
