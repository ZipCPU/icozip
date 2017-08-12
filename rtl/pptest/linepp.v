////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	linepp.v
//
// Project:	wbuart32, a full featured UART with simulator
//
// Purpose:	To test whether or not the pport input module works in addition
//		to the pport output (which was proven via hellopp and speechpp).
//	This module works by buffering one line's worth of input, and then
//	piping that line to the transmitter while (possibly) receiving a new
//	line.
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
module	linepp(i_clk, o_ledg, o_ledr,
		i_pp_dir, i_pp_clk,
`ifdef	VERILATOR
		i_pp_data,
		o_pp_data,
`else
		io_pp_data,
`endif
		o_pp_clkfb
		);
	input	wire		i_clk;
	//
	output	wire	[1:0]	o_ledg;
	output	wire		o_ledr;
	//
	input	wire		i_pp_dir, i_pp_clk;
`ifdef	VERILATOR
	input	wire	[7:0]	i_pp_data;
	output	wire	[7:0]	o_pp_data;
`else
	inout	wire	[7:0]	io_pp_data;
`endif
	//
	output	wire		o_pp_clkfb;

	wire		s_clk;
`ifdef	VERILATOR
	assign	s_clk = i_clk;
`else
	wire	clk_66mhz, pll_locked;
	SB_PLL40_PAD #(
		.FEEDBACK_PATH("SIMPLE"),
		.DELAY_ADJUSTMENT_MODE_FEEDBACK("FIXED"),
		.DELAY_ADJUSTMENT_MODE_RELATIVE("FIXED"),
		.PLLOUT_SELECT("GENCLK"),
		.FDA_FEEDBACK(4'b1111),
		.FDA_RELATIVE(4'b1111),
		.DIVR(4'd8),		// Divide by (DIVR+1)
		.DIVQ(3'd3),		// Divide by 2^(DIVQ)
		.DIVF(7'd47),		// Multiply by (DIVF+1)
		.FILTER_RANGE(3'b001)
	) plli (
		.PACKAGEPIN     (i_clk        ),
		.PLLOUTCORE     (clk_66mhz    ),
		.LOCK           (pll_locked  ),
		.BYPASS         (1'b0         ),
		.RESETB         (1'b1         )
	);

	assign	s_clk = clk_66mhz;
`endif


	// If rx_stb is true, rx_data was just received.
	// If (tx_stb)&&(!tx_busy), then the tx_data was accepted by the
	//	output port.
	wire		rx_stb, tx_stb, tx_busy;
	wire	[7:0]	rx_data, tx_data;

	reg	[7:0]	buffer	[0:255];
	reg	[7:0]	head, tail;

	// Create a reset line that will always be true on a power on reset
	reg	pwr_reset;
	initial	pwr_reset = 1'b1;
	always @(posedge s_clk)
		pwr_reset = 1'b0;


	// The next step in this process is to dump everything we read into a 
	// FIFO.  First step: writing into the FIFO.  Always write into FIFO
	// memory.  (The next step will step the memory address if rx_stb was
	// true ...)
	wire	[7:0]	nxt_head;
	assign	nxt_head = head + 8'h01;	
	always @(posedge s_clk)
		buffer[head] <= rx_data;

	// Select where in our FIFO memory to write.  On reset, we clear the 
	// memory.  In all other cases/respects, we step the memory forward.
	//
	// However ... we won't step it forward IF ...
	//	rx_break	- we are in a BREAK condition on the line
	//		(i.e. ... it's disconnected)
	//	rx_perr		- We've seen a parity error
	//	rx_ferr		- Same thing for a frame error
	//	nxt_head != tail - If the FIFO is already full, we'll just drop
	//		this new value, rather than dumping random garbage
	//		from the FIFO until we go round again ...  i.e., we
	//		don't write on potential overflow.
	//
	// Adjusting this address will make certain that the next write to the
	// FIFO goes to the next address--since we've already written the FIFO
	// memory at this address.
	initial	head= 8'h00;
	always @(posedge s_clk)
		if (pwr_reset)
			head <= 8'h00;
		else if ((rx_stb)&&(nxt_head != tail))
			head <= nxt_head;

	wire	[7:0]	nused;
	reg	[7:0]	lineend;
	reg		run_tx;

	// How much of the FIFO is in use?  head - tail.  What if they wrap
	// around?  Still: head-tail, but this time truncated to the number of
	// bits of interest.  It can never be negative ... so ... we're good,
	// this just measures that number.
	assign	nused = head-tail;

	// Here's the guts of the algorithm--setting run_tx.  Once set, the
	// buffer will flush.  Here, we set it on one of two conditions: 1)
	// a newline is received, or 2) the line is now longer than 80
	// characters.
	//
	// Once the line has ben transmitted (separate from emptying the buffer)
	// we stop transmitting.
	initial	run_tx = 0;
	initial	lineend = 0;
	always @(posedge s_clk)
		if (pwr_reset)
		begin
			run_tx <= 1'b0;
			lineend <= 8'h00;
		end else if(((rx_data == 8'h0a)||(rx_data == 8'hd))&&(rx_stb))
		begin
			// Start transmitting once we get to either a newline
			// or a carriage return character
			lineend <= head+8'h1;
			run_tx <= 1'b1;
		end else if ((!run_tx)&&(nused>8'd80))
		begin
			// Start transmitting once we get to 80 chars
			lineend <= head;
			run_tx <= 1'b1;
		end else if (tail == lineend)
			// Line buffer has been emptied
			run_tx <= 1'b0;

	// When do we wish to transmit?
	//
	// Any time run_tx is true--but we'll give it an extra clock.
	initial	tx_stb = 1'b0;
	always @(posedge s_clk)
		tx_stb <= run_tx;

	// We'll transmit the data from our FIFO from ... wherever our tail
	// is pointed.
	always @(posedge s_clk)
		tx_data <= buffer[tail];

	// We increment the pointer to where we read from any time 1) we are
	// requesting to transmit a character, and 2) the transmitter was not
	// busy and thus accepted our request.  At that time, increment the
	// pointer, and we'll be ready for another round.
	initial	tail = 8'h00;
	always @(posedge s_clk)
		if(pwr_reset)
			tail <= 8'h00;
		else if ((tx_stb)&&(!tx_busy))
			tail <= tail + 8'h01;

	wire	[7:0]	w_pp_data, i_pp_data;

	pport pporti(s_clk,
		rx_stb, rx_data,		// Receive interface  (from Pi)
		tx_stb, tx_data, tx_busy,	// Transmit interface (to   Pi)
		i_pp_dir, i_pp_clk, i_pp_data, w_pp_data,
		o_pp_clkfb);


`ifdef	VERILATOR
	assign	io_pp_data = (i_pp_dir) ? 8'bzzzz_zzzz : w_pp_data;
`else
	ppio	theppio(i_pp_dir, io_pp_data, w_pp_data, i_pp_data);
`endif

	reg	[2:0]	r_led;

	always @(posedge s_clk)
		r_led[0] <= (head != tail);
	always @(posedge s_clk)
		r_led[1] <= (tx_stb)&&(!tx_busy);
	always @(posedge s_clk)
		r_led[2] <= (nxt_head == tail);

	assign	o_ledg[1:0] = r_led[1:0];
	assign	o_ledr      = r_led[2];


endmodule
