////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	speechpp.v
//
// Project:
//
// Purpose:	To test/demonstrate/prove the wishbone access to the FIFO'd
//		parallel port via sending more information than the FIFO can
//	hold, and then verifying that this was the value received.
//
//	To do this, we "borrow" a copy of Abraham Lincolns Gettysburg address,
//	make that the FIFO isn't large enough to hold it, and then try
//	to send this address every couple of minutes.
//
//	This code was originally a part of the wbuart32 repository, and has
//	since been modified for ICO parallel port support.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2017, Gisselquist Technology, LLC
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
`default_nettype none
//
module	speechpp(i_clk, o_ledg, o_ledr,
		i_pp_dir, i_pp_clk, io_pp_data,
		o_pp_clkfb);
	//
	input	wire		i_clk;
	//
	output	wire	[1:0]	o_ledg;
	output	wire		o_ledr;
	//
	input	wire		i_pp_dir, i_pp_clk;
	inout	wire	[7:0]	io_pp_data;
	output	wire		o_pp_clkfb;
	// Let's set our message length, in case we ever wish to change it in
	// the future
	localparam	MSGLEN=2203;

	wire	[7:0]	i_pp_data;
	reg		restart;
	reg		wb_stb;
	reg	[1:0]	wb_addr;
	reg	[31:0]	wb_data;


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

	wire		pport_stall, pport_ack;
	wire	[31:0]	pport_data;

	wire		tx_int, txfifo_int;

	// The next four lines create a strobe signal that is true on the first
	// clock, but never after.  This makes for a decent power-on reset
	// signal.
	reg	pwr_reset;
	initial	pwr_reset = 1'b1;
	always @(posedge s_clk)
		pwr_reset <= 1'b0;


	// The message we wish to transmit is kept in "message".  It needs to be
	// set initially.  Do so here.
	//
	// Since the message has fewer than 2048 elements in it, we preset every
	// element to a space so that if (for some reason) we broadcast past the
	// end of our message, we'll at least be sending something useful.
	integer	i;
	reg	[7:0]	message [0:4095];
	initial begin
		// xx Verilator needs this file to be in the directory the file
		// is run from.  For that reason, the project builds, makes,
		// and keeps speech.hex in bench/cpp.  
		//
		// Vivado, however, wants speech.hex to be in a project file
		// directory, such as bench/verilog.  For that reason, the
		// build function in bench/cpp also copies speech.hex to the
		// bench/verilog directory.  You may need to make certain the
		// file is both built, and copied into a directory where your
		// synthesis tool can find it.
		//
		$readmemh("speech.hex", message);
		for(i=MSGLEN; i<4095; i=i+1)
			message[i] = 8'h20;

		//
		// The problem with the above approach is Xilinx's ISE program.
		// It's broken.  It can't handle HEX files well (at all?) and
		// has more problems with HEX's defining ROM's.  For that
		// reason, the mkspeech program can be tuned to create an
		// include file, speech.inc.  We include that program here.
		// It is rather ugly, though, and not a very elegant solution,
		// since it walks through every value in our speech, byte by
		// byte, with an initial line for each byte declaring what it
		// is to be.
		//
		// If you (need to) use this route, comment out both the 
		// readmemh, the for loop, and the message[i] = 8'h20 lines
		// above and uncomment the include line below.
		//
		// `include "speech.inc"
	end

	// Let's keep track of time, and send our message over and over again.
	// To do this, we'll keep track of a restart counter.  When this counter
	// rolls over, we restart our message.
	reg	[30:0]	restart_counter;
	// Since we want to start our message just a couple clocks after power
	// up, we'll set the reset counter just a couple clocks shy of a roll
	// over.
	initial	restart_counter = -31'd16;
	always @(posedge s_clk)
		restart_counter <= restart_counter+1'b1;

	// Ok, now that we have a counter that tells us when to start over,
	// let's build a set of signals that we can use to get things started
	// again.  This will be the restart signal.  On this signal, we just
	// restart everything.
	initial	restart = 0;
	always @(posedge s_clk)
		restart <= (restart_counter == 0);

	// Our message index.  This is the address of the character we wish to
	// transmit next.  Note, there's a clock delay between setting this 
	// index and when the wb_data is valid.  Hence, we set the index on
	// restart[0] to zero.
	reg	[11:0]	msg_index;
	initial	msg_index = 12'h000 - 12'h8;
	always @(posedge s_clk)
	begin
		if (restart)
			msg_index <= 0;
		else if ((wb_stb)&&(!pport_stall))
			// We only advance the index if a port operation on the
			// wbpport has taken place.  That's what the
			// (wb_stb)&&(!pport_stall) is about.  (wb_stb) is the
			// request for a transaction on the bus, pport_stall
			// tells us to wait 'cause the peripheral isn't ready. 
			// In our case, it's always ready, pport_stall == 0, but
			// we keep/maintain this logic for good form.
			//
			// Note also, we only advance when restart[0] is zero.
			// This keeps us from advancing prior to the setup
			// word.
			msg_index <= msg_index + 1'b1;
	end

	// What data will we be sending to the port?
	always @(posedge s_clk)
		if ((wb_stb)&&(!pport_stall))
			// Then, if the last thing was received over the bus,
			// we move to the next data item.
			wb_data <= { 24'h00, message[msg_index] };

	// We send our first value to the SETUP address (all zeros), all other
	// values we send to the transmitters address.  We should really be
	// double checking that stall remains low, but its not required here.
	always @(posedge s_clk)
		if (restart)
			wb_addr <= 2'b00;
		else // if (!pport_stall)??
			wb_addr <= 2'b11;

	// Knowing when to stop sending the speech is important, but depends
	// upon an 11 bit comparison.  Since FPGA logic is best measured by the
	// number of inputs to an always block, we pull those 11-bits out of
	// the always block for wb_stb, and place them here on the clock prior.
	// If end_of_message is true, then we need to stop transmitting, and
	// wait for the next (restart) to get us started again.  We set that
	// flag hee.
	reg	end_of_message;
	initial	end_of_message = 1'b1;
	always @(posedge s_clk)
		if (restart)
			end_of_message <= 1'b0;
		else
			end_of_message <= (msg_index >= MSGLEN);

	// The wb_stb signal indicates that we wish to write, using the wishbone
	// to our peripheral.  We have two separate types of writes.  First,
	// we wish to write our setup.  Then we want to drop STB and write
	// our data.  Once we've filled half of the FIFO, we wait for the FIFO
	// to empty before issuing a STB again and then fill up half the FIFO
	// again.
	initial	wb_stb = 1'b0;
	always @(posedge s_clk)
		if (restart)
			// Start sending to the UART on a reset.  The first
			// thing we'll send will be the configuration, but
			// that's done elsewhere.  This just starts up the
			// writes to the peripheral wbuart.
			wb_stb <= 1'b1;
		else if (end_of_message)
			// Stop transmitting when we get to the end of our
			// message.
			wb_stb <= 1'b0;
		else if (tx_int)
			wb_stb <= 1'b1;
		else if (txfifo_int)
			// If the FIFO is less than half full, then write to
			// it.
			wb_stb <= 1'b1;
		else
			// But once the FIFO gets to half full, stop.
			wb_stb <= 1'b0;

	// We aren't using the receive interrupts, so we'll just mark them
	// here as ignored.
	wire	ignored_rx_int, ignored_rxfifo_int;
	// Finally--the unit under test--now that we've set up all the wires
	// to run/test it.
	wire	pp_rx_stb, pp_tx_stb, pp_tx_busy;
	wire	[7:0]	pp_rx_data, pp_tx_data;
	wbpport	wbpporti(s_clk, pwr_reset,
			wb_stb, wb_stb, 1'b1, wb_addr, wb_data,
			pport_ack, pport_stall, pport_data,
			pp_rx_stb, pp_rx_data[6:0],
			pp_tx_stb, pp_tx_data[6:0], pp_tx_busy,
			ignored_rx_int, tx_int,
			ignored_rxfifo_int, txfifo_int);
	assign	pp_tx_data[7] = 1'b0;

	wire	[7:0]	w_pp_data;
	pport	pporti(s_clk,
			pp_rx_stb, pp_rx_data,
			pp_tx_stb, pp_tx_data, pp_tx_busy,
			i_pp_dir, i_pp_clk, i_pp_data, w_pp_data,
			o_pp_clkfb);
`ifdef	VERILATOR
	assign	io_pp_data = (i_pp_dir) ? 8'bzzzz_zzzz : w_pp_data;
	assign	i_pp_data = io_pp_data;
`else
	ppio	theppio(i_pp_dir, io_pp_data, w_pp_data, i_pp_data);
`endif


	reg	[23:0]	evctr;
	initial	evctr = 0;
	always @(posedge s_clk)
		if ((pp_rx_stb)||(pp_tx_stb))
			evctr <= 0;
		else if (!evctr[23])
			evctr <= evctr + 1'b1;
	assign	o_ledg[0] = !evctr[23];
	assign	o_ledg[1] = pp_tx_busy;
	assign	o_ledr = !txfifo_int;


	// Make verilator happy
	// verilator lint_off UNUSED
	wire	[35:0] unused;
	assign	unused = { ignored_rx_int, ignored_rxfifo_int, pp_rx_data[7],
			pport_ack, pport_data };
	// verilator lint_off UNUSED

endmodule
