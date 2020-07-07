////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	speechfifo.v
//
// Project:	ICO Zip, iCE40 ZipCPU demonstration project
//
// Purpose:	To test/demonstrate/prove the wishbone access to the FIFO'd
//		UART via sending more information than the FIFO can hold,
//	and then verifying that this was the value received.
//
//	To do this, we "borrow" a copy of Abraham Lincolns Gettysburg address,
//	make that the FIFO isn't large enough to hold it, and then try
//	to send this address every couple of minutes.
//
//	This file has been taken from the wbuart32 repository, and turned into
//	an icoboard test file.
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
module	speechfifo(i_clk,
			o_ledg, o_ledr, i_rts, i_uart_rx, o_cts,
			o_uart_tx);
	input		i_clk;
	output	wire	[1:0] o_ledg;
	output	wire	o_ledr;
	input		i_rts, i_uart_rx;
	output	wire	o_uart_tx, o_cts;

	reg	clk_50mhz;
	wire	s_clk;

	initial	clk_50mhz = 0;
	always @(posedge i_clk)
		clk_50mhz <= !clk_50mhz;

        SB_GB global_buffer(clk_50mhz, s_clk);

	// Let's set our message length, in case we ever wish to change it in
	// the future
	localparam	MSGLEN=2203;
	assign	o_cts = 1'b1;

	// The i_setup wires are input when run under Verilator, but need to
	// be set internally if this is going to run as a standalone top level
	// test configuration.
	wire	[29:0]	i_setup;

	// Here we set i_setup to something appropriate to create a 115200 Baud
	// UART system from a 100MHz clock.  This also sets us to an 8-bit data
	// word, 1-stop bit, and no parity.
	assign	i_setup = 30'd868;

	reg		restart;
	reg		wb_stb;
	reg	[1:0]	wb_addr;
	reg	[31:0]	wb_data;

	wire		uart_stall;

	// We aren't using the receive interrupts, or the received data, or the
	// ready to send line, so we'll just mark them all here as ignored.

	/* verilator lint_off UNUSED */
	wire		uart_ack, tx_int;
	wire	[31:0]	uart_data;
	wire		ignored_rx_int, ignored_rxfifo_int;
	wire		rts_n_ignored;
	/* verilator lint_on UNUSED */

	/* verilator lint_on UNUSED */

	wire		txfifo_int;

	// The next four lines create a strobe signal that is true on the first
	// clock, but never after.  This makes for a decent power-on reset
	// signal.
	reg	pwr_reset;
	initial	pwr_reset = 1'b1;
	always @(posedge i_clk)
		pwr_reset <= 1'b0;

	reg	[25:0]	ledctr;
	initial	ledctr = 0;
	always @(posedge s_clk)
	if (restart)
		ledctr <= 0;
	else if (!ledctr[25])
		ledctr <= ledctr + 1'b1;

	assign	o_ledg[0] = !ledctr[25];

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
		$readmemh("speech.hex", message);
		for(i=MSGLEN; i<4095; i=i+1)
			message[i] = 8'h20;
	end

	// Let's keep track of time, and send our message over and over again.
	// To do this, we'll keep track of a restart counter.  When this counter
	// rolls over, we restart our message.
	reg	[30:0]	restart_counter;
	// Since we want to start our message just a couple clocks after power
	// up, we'll set the reset counter just a couple clocks shy of a roll
	// over.
	initial	restart_counter = -31'd16;
	always @(posedge i_clk)
		restart_counter <= restart_counter+1'b1;

	// Ok, now that we have a counter that tells us when to start over,
	// let's build a set of signals that we can use to get things started
	// again.  This will be the restart signal.  On this signal, we just
	// restart everything.
	initial	restart = 0;
	always @(posedge i_clk)
		restart <= (restart_counter == 0);

	// Our message index.  This is the address of the character we wish to
	// transmit next.  Note, there's a clock delay between setting this 
	// index and when the wb_data is valid.  Hence, we set the index on
	// restart[0] to zero.
	reg	[11:0]	msg_index;
	initial	msg_index = 12'h000 - 12'h8;
	always @(posedge s_clk)
	if (restart)
		msg_index <= 0;
	else if ((wb_stb)&&(!uart_stall))
		// We only advance the index if a port operation on the
		// wbuart has taken place.  That's what the
		// (wb_stb)&&(!uart_stall) is about.  (wb_stb) is the
		// request for a transaction on the bus, uart_stall
		// tells us to wait 'cause the peripheral isn't ready. 
		// In our case, it's always ready, uart_stall == 0, but
		// we keep/maintain this logic for good form.
		//
		// Note also, we only advance when restart[0] is zero.
		// This keeps us from advancing prior to the setup
		// word.
		msg_index <= msg_index + 1'b1;

	// What data will we be sending to the port?
	always @(posedge s_clk)
	if (restart)
		// The first thing we do is set the baud rate, and
		// serial port configuration parameters.  Ideally,
		// we'd only set this once.  But rather than complicate
		// the logic, we set it everytime we start over.
		wb_data <= { 1'b0, i_setup };
	else if ((wb_stb)&&(!uart_stall))
		// Then, if the last thing was received over the bus,
		// we move to the next data item.
		wb_data <= { 24'h00, message[msg_index] };

	// We send our first value to the SETUP address (all zeros), all other
	// values we send to the transmitters address.  We should really be
	// double checking that stall remains low, but its not required here.
	always @(posedge s_clk)
	if (restart)
		wb_addr <= 2'b00;
	else // if (!uart_stall)??
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
	else if (txfifo_int)
		// If the FIFO is less than half full, then write to
		// it.
		wb_stb <= 1'b1;
	else
		// But once the FIFO gets to half full, stop.
		wb_stb <= 1'b0;

	// The WBUART can handle hardware flow control signals.  This test,
	// however, cannot.  The reason?  Simply just to keep things simple.
	// If you want to add hardware flow control to your design, simply
	// make rts an input to this module.
	//
	// Since this is an output only module demonstrator, what would be the
	// cts output is unused.
	wire	cts_n;
	assign	cts_n = 1'b0;

	// Finally--the unit under test--now that we've set up all the wires
	// to run/test it.
	wbuart	// #(INITIAL_UART_SETUP)
	wbuarti(s_clk, pwr_reset,
		wb_stb, wb_stb, 1'b1, wb_addr, wb_data, 4'hf,
		uart_stall, uart_ack, uart_data,
		1'b1, o_uart_tx, cts_n, rts_n_ignored,
		ignored_rx_int, tx_int,
		ignored_rxfifo_int, txfifo_int);

	assign	o_ledr = 1'b0;

	reg	[23:0]	evctr;
	initial	ledctr = 0;
	always @(posedge s_clk)
	if (!o_uart_tx)
		evctr <= 0;
	else if (!evctr[23])
		evctr <= evctr + 1'b1;

	assign	o_ledg[1] = !evctr[23];

endmodule
////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbuart.v
//
// Project:	wbuart32, a full featured UART with simulator
//
// Purpose:	Unlilke wbuart-insert.v, this is a full blown wishbone core
//		with integrated FIFO support to support the UART transmitter
//	and receiver found within here.  As a result, it's usage may be
//	heavier on the bus than the insert, but it may also be more useful.
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
`default_nettype	none
//
`define	UART_SETUP	2'b00
`define	UART_FIFO	2'b01
`define	UART_RXREG	2'b10
`define	UART_TXREG	2'b11
//
`define	USE_LITE_UART
module	wbuart(i_clk, i_rst,
		//
		i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, i_wb_sel,
			o_wb_stall, o_wb_ack, o_wb_data,
		//
		i_uart_rx, o_uart_tx, i_cts_n, o_rts_n,
		//
		o_uart_rx_int, o_uart_tx_int,
		o_uart_rxfifo_int, o_uart_txfifo_int);
	parameter [30:0] INITIAL_SETUP = 31'd50; // 1MB 8N1, when using 50MHz clock
	parameter [3:0]	LGFLEN = 4;
	parameter [0:0]	HARDWARE_FLOW_CONTROL_PRESENT = 1'b1;
	// Perform a simple/quick bounds check on the log FIFO length, to make
	// sure its within the bounds we can support with our current
	// interface.
	localparam [3:0]	LCLLGFLEN = (LGFLEN > 4'ha)? 4'ha
					: ((LGFLEN < 4'h2) ? 4'h2 : LGFLEN);
	//
	input	wire		i_clk, i_rst;
	// Wishbone inputs
	input	wire		i_wb_cyc;	// We ignore CYC for efficiency
	input	wire		i_wb_stb, i_wb_we;
	input	wire	[1:0]	i_wb_addr;
	input	wire	[31:0]	i_wb_data;
	input	wire	[3:0]	i_wb_sel;
	output	wire		o_wb_stall;
	output	reg		o_wb_ack;
	output	reg	[31:0]	o_wb_data;
	//
	input	wire		i_uart_rx;
	output	wire		o_uart_tx;
	// RTS is used for hardware flow control.  According to Wikipedia, it
	// should probably be renamed RTR for "ready to receive".  It tell us
	// whether or not the receiving hardware is ready to accept another
	// byte.  If low, the transmitter will pause.
	//
	// If you don't wish to use hardware flow control, just set i_cts_n to
	// 1'b0 and let the optimizer simply remove this logic.
	input	wire		i_cts_n;
	// CTS is the "Clear-to-send" signal.  We set it anytime our FIFO
	// isn't full.  Feel free to ignore this output if you do not wish to
	// use flow control.
	output	reg		o_rts_n;
	output	wire		o_uart_rx_int, o_uart_tx_int,
				o_uart_rxfifo_int, o_uart_txfifo_int;

	wire	tx_busy;

	//
	// The UART setup parameters: bits per byte, stop bits, parity, and
	// baud rate are all captured within this uart_setup register.
	//
	reg	[30:0]	uart_setup;
	initial	uart_setup = INITIAL_SETUP
		| ((HARDWARE_FLOW_CONTROL_PRESENT==1'b0)? 31'h40000000 : 0);
	always @(posedge i_clk)
		// Under wishbone rules, a write takes place any time i_wb_stb
		// is high.  If that's the case, and if the write was to the
		// setup address, then set us up for the new parameters.
		if ((i_wb_stb)&&(i_wb_addr == `UART_SETUP)&&(i_wb_we))
			uart_setup <= {
				(i_wb_data[30])
					||(!HARDWARE_FLOW_CONTROL_PRESENT),
				i_wb_data[29:0] };

	/////////////////////////////////////////
	//
	//
	// First, the UART receiver
	//
	//
	/////////////////////////////////////////

	// First the wires/registers this receiver depends upon
	wire		rx_stb, rx_break, rx_perr, rx_ferr, ck_uart;
	wire	[7:0]	rx_uart_data;
	reg		rx_uart_reset;

	// Here's our UART receiver.  Basically, it accepts our setup wires, 
	// the UART input, a clock, and a reset line, and produces outputs:
	// a stb (true when new data is ready), and an 8-bit data out value
	// valid when stb is high.
`ifdef	USE_LITE_UART
//	rxuartlite	#(.CLOCKS_PER_BAUD(INITIAL_SETUP[23:0]))
//		rx(i_clk, i_uart_rx, rx_stb, rx_uart_data);
	assign	rx_stb   = 0;
	assign	rx_uart_data  = 0;
	assign	rx_break = 1'b0;
	assign	rx_perr  = 1'b0;
	assign	rx_ferr  = 1'b0;
	assign	ck_uart  = 1'b0;
`else
	// The full receiver also produces a break value (true during a break
	// cond.), and parity/framing error flags--also valid when stb is true.
	rxuart	#(.INITIAL_SETUP(INITIAL_SETUP)) rx(i_clk, (i_rst)||(rx_uart_reset),
			uart_setup, i_uart_rx,
			rx_stb, rx_uart_data, rx_break,
			rx_perr, rx_ferr, ck_uart);
	// The real trick is ... now that we have this extra data, what do we do
	// with it?
`endif


	// We place it into a receiver FIFO.
	//
	// Here's the declarations for the wires it needs.
	wire		rx_empty_n, rx_fifo_err;
	wire	[7:0]	rxf_wb_data;
	wire	[15:0]	rxf_status;
	reg		rxf_wb_read;
	//
	// And here's the FIFO proper.
	//
	// Note that the FIFO will be cleared upon any reset: either if there's
	// a UART break condition on the line, the receiver is in reset, or an
	// external reset is issued.
	//
	// The FIFO accepts strobe and data from the receiver.
	// We issue another wire to it (rxf_wb_read), true when we wish to read
	// from the FIFO, and we get our data in rxf_wb_data.  The FIFO outputs
	// four status-type values: 1) is it non-empty, 2) is the FIFO over half
	// full, 3) a 16-bit status register, containing info regarding how full
	// the FIFO truly is, and 4) an error indicator.
	ufifo	#(.LGFLEN(LCLLGFLEN), .RXFIFO(1))
		rxfifo(i_clk, (i_rst)||(rx_break)||(rx_uart_reset),
			rx_stb, rx_uart_data,
			rx_empty_n,
			rxf_wb_read, rxf_wb_data,
			rxf_status, rx_fifo_err);
	assign	o_uart_rxfifo_int = rxf_status[1];

	// We produce four interrupts.  One of the receive interrupts indicates
	// whether or not the receive FIFO is non-empty.  This should wake up
	// the CPU.
	assign	o_uart_rx_int = rxf_status[0];

	// The clear to send line, which may be ignored, but which we set here
	// to be true any time the FIFO has fewer than N-2 items in it.
	// Why not N-1?  Because at N-1 we are totally full, but already so full
	// that if the transmit end starts sending we won't have a location to
	// receive it.  (Transmit might've started on the next character by the
	// time we set this--thus we need to set it to one, one character before
	// necessary).
	wire	[(LCLLGFLEN-1):0]	check_cutoff;
	assign	check_cutoff = -3;
	always @(posedge i_clk)
		o_rts_n <= ((HARDWARE_FLOW_CONTROL_PRESENT)
			&&(!uart_setup[30])
			&&(rxf_status[(LCLLGFLEN+1):2] > check_cutoff));

	// If the bus requests that we read from the receive FIFO, we need to
	// tell this to the receive FIFO.  Note that because we are using a 
	// clock here, the output from the receive FIFO will necessarily be
	// delayed by an extra clock.
	initial	rxf_wb_read = 1'b0;
	always @(posedge i_clk)
		rxf_wb_read <= (i_wb_stb)&&(i_wb_addr[1:0]==`UART_RXREG)
				&&(!i_wb_we);

	// Now, let's deal with those RX UART errors: both the parity and frame
	// errors.  As you may recall, these are valid only when rx_stb is
	// valid, so we need to hold on to them until the user reads them via
	// a UART read request..
	reg	r_rx_perr, r_rx_ferr;
	initial	r_rx_perr = 1'b0;
	initial	r_rx_ferr = 1'b0;
	always @(posedge i_clk)
		if ((rx_uart_reset)||(rx_break))
		begin
			// Clear the error
			r_rx_perr <= 1'b0;
			r_rx_ferr <= 1'b0;
		end else if ((i_wb_stb)
				&&(i_wb_addr[1:0]==`UART_RXREG)&&(i_wb_we))
		begin
			// Reset the error lines if a '1' is ever written to
			// them, otherwise leave them alone.
			//
			r_rx_perr <= (r_rx_perr)&&(~i_wb_data[9]);
			r_rx_ferr <= (r_rx_ferr)&&(~i_wb_data[10]);
		end else if (rx_stb)
		begin
			// On an rx_stb, capture any parity or framing error
			// indications.  These aren't kept with the data rcvd,
			// but rather kept external to the FIFO.  As a result,
			// if you get a parity or framing error, you will never
			// know which data byte it was associated with.
			// For now ... that'll work.
			r_rx_perr <= (r_rx_perr)||(rx_perr);
			r_rx_ferr <= (r_rx_ferr)||(rx_ferr);
		end

	initial	rx_uart_reset = 1'b1;
	always @(posedge i_clk)
		if ((i_rst)||((i_wb_stb)&&(i_wb_addr[1:0]==`UART_SETUP)&&(i_wb_we)))
			// The receiver reset, always set on a master reset
			// request.
			rx_uart_reset <= 1'b1;
		else if ((i_wb_stb)&&(i_wb_addr[1:0]==`UART_RXREG)&&(i_wb_we))
			// Writes to the receive register will command a receive
			// reset anytime bit[12] is set.
			rx_uart_reset <= i_wb_data[12];
		else
			rx_uart_reset <= 1'b0;

	// Finally, we'll construct a 32-bit value from these various wires,
	// to be returned over the bus on any read.  These include the data
	// that would be read from the FIFO, an error indicator set upon
	// reading from an empty FIFO, a break indicator, and the frame and
	// parity error signals.
	wire	[31:0]	wb_rx_data;
	assign	wb_rx_data = { 16'h00,
				3'h0, rx_fifo_err,
				rx_break, rx_ferr, r_rx_perr, !rx_empty_n,
				rxf_wb_data};

	/////////////////////////////////////////
	//
	//
	// Then the UART transmitter
	//
	//
	/////////////////////////////////////////
	wire		tx_empty_n, txf_err, tx_break;
	wire	[7:0]	tx_data;
	wire	[15:0]	txf_status;
	reg		txf_wb_write, tx_uart_reset;
	reg	[7:0]	txf_wb_data;

	// Unlike the receiver which goes from RXUART -> UFIFO -> WB, the
	// transmitter basically goes WB -> UFIFO -> TXUART.  Hence, to build
	// support for the transmitter, we start with the command to write data
	// into the FIFO.  In this case, we use the act of writing to the 
	// UART_TXREG address as our indication that we wish to write to the 
	// FIFO.  Here, we create a write command line, and latch the data for
	// the extra clock that it'll take so that the command and data can be
	// both true on the same clock.
	initial	txf_wb_write = 1'b0;
	always @(posedge i_clk)
	begin
		txf_wb_write <= (i_wb_stb)&&(i_wb_addr == `UART_TXREG)
					&&(i_wb_we);
		txf_wb_data  <= i_wb_data[7:0];
	end

	// Transmit FIFO
	//
	// Most of this is just wire management.  The TX FIFO is identical in
	// implementation to the RX FIFO (theyre both UFIFOs), but the TX
	// FIFO is fed from the WB and read by the transmitter.  Some key
	// differences to note: we reset the transmitter on any request for a
	// break.  We read from the FIFO any time the UART transmitter is idle.
	// and ... we just set the values (above) for controlling writing into
	// this.
	ufifo	#(.LGFLEN(LGFLEN), .RXFIFO(0))
		txfifo(i_clk, (tx_break)||(tx_uart_reset),
			txf_wb_write, txf_wb_data,
			tx_empty_n,
			(!tx_busy)&&(tx_empty_n), tx_data,
			txf_status, txf_err);
	// Let's create two transmit based interrupts from the FIFO for the CPU.
	//	The first will be true any time the FIFO has at least one open
	//	position within it.
	assign	o_uart_tx_int = txf_status[0];
	//	The second will be true any time the FIFO is less than half
	//	full, allowing us a change to always keep it (near) fully 
	//	charged.
	assign	o_uart_txfifo_int = txf_status[1];

`ifndef	USE_LITE_UART
	// Break logic
	//
	// A break in a UART controller is any time the UART holds the line
	// low for an extended period of time.  Here, we capture the wb_data[9]
	// wire, on writes, as an indication we wish to break.  As long as you
	// write unsigned characters to the interface, this will never be true
	// unless you wish it to be true.  Be aware, though, writing a valid
	// value to the interface will bring it out of the break condition.
	reg	r_tx_break;
	initial	r_tx_break = 1'b0;
	always @(posedge i_clk)
		if (i_rst)
			r_tx_break <= 1'b0;
		else if ((i_wb_stb)&&(i_wb_addr[1:0]==`UART_TXREG)&&(i_wb_we))
			r_tx_break <= i_wb_data[9];
	assign	tx_break = r_tx_break;
`else
	assign	tx_break = 1'b0;
`endif

	// TX-Reset logic
	//
	// This is nearly identical to the RX reset logic above.  Basically,
	// any time someone writes to bit [12] the transmitter will go through
	// a reset cycle.  Keep bit [12] low, and everything will proceed as
	// normal.
	initial	tx_uart_reset = 1'b1;
	always @(posedge i_clk)
		if((i_rst)||((i_wb_stb)&&(i_wb_addr == `UART_SETUP)&&(i_wb_we)))
			tx_uart_reset <= 1'b1;
		else if ((i_wb_stb)&&(i_wb_addr[1:0]==`UART_TXREG)&&(i_wb_we))
			tx_uart_reset <= i_wb_data[12];
		else
			tx_uart_reset <= 1'b0;

`ifdef	USE_LITE_UART
	txuartlite #(.CLOCKS_PER_BAUD(INITIAL_SETUP[23:0])) tx(i_clk, (tx_empty_n), tx_data,
			o_uart_tx, tx_busy);
`else
	wire	cts_n;
	assign	cts_n = (HARDWARE_FLOW_CONTROL_PRESENT)&&(i_cts_n);
	// Finally, the UART transmitter module itself.  Note that we haven't
	// connected the reset wire.  Transmitting is as simple as setting
	// the stb value (here set to tx_empty_n) and the data.  When these
	// are both set on the same clock that tx_busy is low, the transmitter
	// will move on to the next data byte.  Really, the only thing magical
	// here is that tx_empty_n wire--thus, if there's anything in the FIFO,
	// we read it here.  (You might notice above, we register a read any
	// time (tx_empty_n) and (!tx_busy) are both true---the condition for
	// starting to transmit a new byte.)
	txuart	#(.INITIAL_SETUP(INITIAL_SETUP)) tx(i_clk, 1'b0, uart_setup,
			r_tx_break, (tx_empty_n), tx_data,
			cts_n, o_uart_tx, tx_busy);
`endif

	// Now that we are done with the chain, pick some wires for the user
	// to read on any read of the transmit port.
	//
	// This port is different from reading from the receive port, since
	// there are no side effects.  (Reading from the receive port advances
	// the receive FIFO, here only writing to the transmit port advances the
	// transmit FIFO--hence the read values are free for ... whatever.)  
	// We choose here to provide information about the transmit FIFO
	// (txf_err, txf_half_full, txf_full_n), information about the current
	// voltage on the line (o_uart_tx)--and even the voltage on the receive
	// line (ck_uart), as well as our current setting of the break and
	// whether or not we are actively transmitting.
	wire	[31:0]	wb_tx_data;
	assign	wb_tx_data = { 16'h00, 
				i_cts_n, txf_status[1:0], txf_err,
				ck_uart, o_uart_tx, tx_break, (tx_busy|txf_status[0]),
				(tx_busy|txf_status[0])?txf_wb_data:8'b00};

	// Each of the FIFO's returns a 16 bit status value.  This value tells
	// us both how big the FIFO is, as well as how much of the FIFO is in 
	// use.  Let's merge those two status words together into a word we
	// can use when reading about the FIFO.
	wire	[31:0]	wb_fifo_data;
	assign	wb_fifo_data = { txf_status, rxf_status };

	// You may recall from above that reads take two clocks.  Hence, we
	// need to delay the address decoding for a clock until the data is 
	// ready.  We do that here.
	reg	[1:0]	r_wb_addr;
	always @(posedge i_clk)
		r_wb_addr <= i_wb_addr;

	// Likewise, the acknowledgement is delayed by one clock.
	reg	r_wb_ack;

	initial	r_wb_ack = 1'b0;
	always @(posedge i_clk) // We'll ACK in two clocks
		r_wb_ack <= i_wb_stb;

	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk) // Okay, time to set the ACK
		o_wb_ack <= i_wb_cyc && r_wb_ack;

	// Finally, set the return data.  This data must be valid on the same
	// clock o_wb_ack is high.  On all other clocks, it is irrelelant--since
	// no one cares, no one is reading it, it gets lost in the mux in the
	// interconnect, etc.  For this reason, we can just simplify our logic.
	always @(posedge i_clk)
		casez(r_wb_addr)
		`UART_SETUP: o_wb_data <= { 1'b0, uart_setup };
		`UART_FIFO:  o_wb_data <= wb_fifo_data;
		`UART_RXREG: o_wb_data <= wb_rx_data;
		`UART_TXREG: o_wb_data <= wb_tx_data;
		endcase

	// This device never stalls.  Sure, it takes two clocks, but they are
	// pipelined, and nothing stalls that pipeline.  (Creates FIFO errors,
	// perhaps, but doesn't stall the pipeline.)  Hence, we can just
	// set this value to zero.
	assign	o_wb_stall = 1'b0;

	// Make verilator happy
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_rst, i_wb_cyc, i_wb_data, i_wb_sel };
	// verilator lint_on UNUSED

endmodule
////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	txuartlite.v
//
// Project:	wbuart32, a full featured UART with simulator
//
// Purpose:	Transmit outputs over a single UART line.  This particular UART
//		implementation has been extremely simplified: it does not handle
//	generating break conditions, nor does it handle anything other than the
//	8N1 (8 data bits, no parity, 1 stop bit) UART sub-protocol.
//
//	To interface with this module, connect it to your system clock, and
//	pass it the byte of data you wish to transmit.  Strobe the i_wr line
//	high for one cycle, and your data will be off.  Wait until the 'o_busy'
//	line is low before strobing the i_wr line again--this implementation
//	has NO BUFFER, so strobing i_wr while the core is busy will just
//	get ignored.  The output will be placed on the o_txuart output line.
//
//	(I often set both data and strobe on the same clock, and then just leave
//	them set until the busy line is low.  Then I move on to the next piece
//	of data.)
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2020, Gisselquist Technology, LLC
//
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of the GNU General Public License as published
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
`define	TXUL_BIT_ZERO	4'h0
`define	TXUL_BIT_ONE	4'h1
`define	TXUL_BIT_TWO	4'h2
`define	TXUL_BIT_THREE	4'h3
`define	TXUL_BIT_FOUR	4'h4
`define	TXUL_BIT_FIVE	4'h5
`define	TXUL_BIT_SIX	4'h6
`define	TXUL_BIT_SEVEN	4'h7
`define	TXUL_STOP	4'h8
`define	TXUL_IDLE	4'hf
//
//
module txuartlite(i_clk, i_wr, i_data, o_uart_tx, o_busy);
	parameter	[4:0]	TIMING_BITS = 5'd24;
	localparam		TB = TIMING_BITS;
	parameter	[(TB-1):0]	CLOCKS_PER_BAUD = 8; // 24'd868;
	input	wire		i_clk;
	input	wire		i_wr;
	input	wire	[7:0]	i_data;
	// And the UART input line itself
	output	reg		o_uart_tx;
	// A line to tell others when we are ready to accept data.  If
	// (i_wr)&&(!o_busy) is ever true, then the core has accepted a byte
	// for transmission.
	output	wire		o_busy;

	reg	[(TB-1):0]	baud_counter;
	reg	[3:0]	state;
	reg	[7:0]	lcl_data;
	reg		r_busy, zero_baud_counter;

	// Big state machine controlling: r_busy, state
	// {{{
	//
	initial	r_busy = 1'b1;
	initial	state  = `TXUL_IDLE;
	always @(posedge i_clk)
	begin
		if (!zero_baud_counter)
			// r_busy needs to be set coming into here
			r_busy <= 1'b1;
		else if (state > `TXUL_STOP)	// STATE_IDLE
		begin
			state <= `TXUL_IDLE;
			r_busy <= 1'b0;
			if ((i_wr)&&(!r_busy))
			begin	// Immediately start us off with a start bit
				r_busy <= 1'b1;
				state <= `TXUL_BIT_ZERO;
			end
		end else begin
			// One clock tick in each of these states ...
			r_busy <= 1'b1;
			if (state <=`TXUL_STOP) // start bit, 8-d bits, stop-b
				state <= state + 1'b1;
			else
				state <= `TXUL_IDLE;
		end
	end
	// }}}

	// o_busy
	// {{{
	//
	// This is a wire, designed to be true is we are ever busy above.
	// originally, this was going to be true if we were ever not in the
	// idle state.  The logic has since become more complex, hence we have
	// a register dedicated to this and just copy out that registers value.
	assign	o_busy = (r_busy);
	// }}}


	// lcl_data
	// {{{
	//
	// This is our working copy of the i_data register which we use
	// when transmitting.  It is only of interest during transmit, and is
	// allowed to be whatever at any other time.  Hence, if r_busy isn't
	// true, we can always set it.  On the one clock where r_busy isn't
	// true and i_wr is, we set it and r_busy is true thereafter.
	// Then, on any zero_baud_counter (i.e. change between baud intervals)
	// we simple logically shift the register right to grab the next bit.
	initial	lcl_data = 8'hff;
	always @(posedge i_clk)
		if ((i_wr)&&(!r_busy))
			lcl_data <= i_data;
		else if (zero_baud_counter)
			lcl_data <= { 1'b1, lcl_data[7:1] };
	// }}}

	// o_uart_tx
	// {{{
	//
	// This is the final result/output desired of this core.  It's all
	// centered about o_uart_tx.  This is what finally needs to follow
	// the UART protocol.
	//
	initial	o_uart_tx = 1'b1;
	always @(posedge i_clk)
		if ((i_wr)&&(!r_busy))
			o_uart_tx <= 1'b0;	// Set the start bit on writes
		else if (zero_baud_counter)	// Set the data bit.
			o_uart_tx <= lcl_data[0];
	// }}}

	// Baud counter
	// {{{
	// All of the above logic is driven by the baud counter.  Bits must last
	// CLOCKS_PER_BAUD in length, and this baud counter is what we use to
	// make certain of that.
	//
	// The basic logic is this: at the beginning of a bit interval, start
	// the baud counter and set it to count CLOCKS_PER_BAUD.  When it gets
	// to zero, restart it.
	//
	// However, comparing a 28'bit number to zero can be rather complex--
	// especially if we wish to do anything else on that same clock.  For
	// that reason, we create "zero_baud_counter".  zero_baud_counter is
	// nothing more than a flag that is true anytime baud_counter is zero.
	// It's true when the logic (above) needs to step to the next bit.
	// Simple enough?
	//
	// I wish we could stop there, but there are some other (ugly)
	// conditions to deal with that offer exceptions to this basic logic.
	//
	// 1. When the user has commanded a BREAK across the line, we need to
	// wait several baud intervals following the break before we start
	// transmitting, to give any receiver a chance to recognize that we are
	// out of the break condition, and to know that the next bit will be
	// a stop bit.
	//
	// 2. A reset is similar to a break condition--on both we wait several
	// baud intervals before allowing a start bit.
	//
	// 3. In the idle state, we stop our counter--so that upon a request
	// to transmit when idle we can start transmitting immediately, rather
	// than waiting for the end of the next (fictitious and arbitrary) baud
	// interval.
	//
	// When (i_wr)&&(!r_busy)&&(state == `TXUL_IDLE) then we're not only in
	// the idle state, but we also just accepted a command to start writing
	// the next word.  At this point, the baud counter needs to be reset
	// to the number of CLOCKS_PER_BAUD, and zero_baud_counter set to zero.
	//
	// The logic is a bit twisted here, in that it will only check for the
	// above condition when zero_baud_counter is false--so as to make
	// certain the STOP bit is complete.
	initial	zero_baud_counter = 1'b1;
	initial	baud_counter = 0;
	always @(posedge i_clk)
	begin
		zero_baud_counter <= (baud_counter == 1);
		if (state == `TXUL_IDLE)
		begin
			baud_counter <= 0;
			zero_baud_counter <= 1'b1;
			if ((i_wr)&&(!r_busy))
			begin
				baud_counter <= CLOCKS_PER_BAUD - 1'b1;
				zero_baud_counter <= 1'b0;
			end
		end else if ((zero_baud_counter)&&(state == 4'h9))
		begin
			baud_counter <= 0;
			zero_baud_counter <= 1'b1;
		end else if (!zero_baud_counter)
			baud_counter <= baud_counter - 1'b1;
		else
			baud_counter <= CLOCKS_PER_BAUD - 1'b1;
	end
	// }}}
//
//
// FORMAL METHODS
//
//
//
`ifdef	FORMAL

`ifdef	TXUARTLITE
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif

	// Setup
	// {{{
	reg	f_past_valid, f_last_clk;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	initial	`ASSUME(!i_wr);
	always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_wr))&&($past(o_busy)))
		begin
			`ASSUME(i_wr   == $past(i_wr));
			`ASSUME(i_data == $past(i_data));
		end
	// }}}

	// Check the baud counter
	// {{{
	always @(posedge i_clk)
		assert(zero_baud_counter == (baud_counter == 0));

	always @(posedge i_clk)
		if ((f_past_valid)&&($past(baud_counter != 0))&&($past(state != `TXUL_IDLE)))
			assert(baud_counter == $past(baud_counter - 1'b1));

	always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(zero_baud_counter))&&($past(state != `TXUL_IDLE)))
			assert($stable(o_uart_tx));

	reg	[(TB-1):0]	f_baud_count;
	initial	f_baud_count = 1'b0;
	always @(posedge i_clk)
		if (zero_baud_counter)
			f_baud_count <= 0;
		else
			f_baud_count <= f_baud_count + 1'b1;

	always @(posedge i_clk)
		assert(f_baud_count < CLOCKS_PER_BAUD);

	always @(posedge i_clk)
		if (baud_counter != 0)
			assert(o_busy);
	// }}}

	reg	[9:0]	f_txbits;
	// {{{
	initial	f_txbits = 0;
	always @(posedge i_clk)
		if (zero_baud_counter)
			f_txbits <= { o_uart_tx, f_txbits[9:1] };

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(zero_baud_counter))
			&&(!$past(state==`TXUL_IDLE)))
		assert(state == $past(state));

	reg	[3:0]	f_bitcount;
	initial	f_bitcount = 0;
	always @(posedge i_clk)
		if ((!f_past_valid)||(!$past(f_past_valid)))
			f_bitcount <= 0;
		else if ((state == `TXUL_IDLE)&&(zero_baud_counter))
			f_bitcount <= 0;
		else if (zero_baud_counter)
			f_bitcount <= f_bitcount + 1'b1;

	always @(posedge i_clk)
		assert(f_bitcount <= 4'ha);

	reg	[7:0]	f_request_tx_data;
	always @(posedge i_clk)
		if ((i_wr)&&(!o_busy))
			f_request_tx_data <= i_data;

	wire	[3:0]	subcount;
	assign	subcount = 10-f_bitcount;
	always @(posedge i_clk)
		if (f_bitcount > 0)
			assert(!f_txbits[subcount]);

	always @(posedge i_clk)
		if (f_bitcount == 4'ha)
		begin
			assert(f_txbits[8:1] == f_request_tx_data);
			assert( f_txbits[9]);
		end

	always @(posedge i_clk)
		assert((state <= `TXUL_STOP + 1'b1)||(state == `TXUL_IDLE));

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(f_past_valid))&&($past(o_busy)))
		cover(!o_busy);
	// }}}

`endif	// FORMAL
`ifdef	VERIFIC_SVA
	reg	[7:0]	fsv_data;

	//
	// Grab a copy of the data any time we are sent a new byte to transmit
	// We'll use this in a moment to compare the item transmitted against
	// what is supposed to be transmitted
	//
	always @(posedge i_clk)
		if ((i_wr)&&(!o_busy))
			fsv_data <= i_data;

	//
	// One baud interval
	// {{{
	//
	// 1. The UART output is constant at DAT
	// 2. The internal state remains constant at ST
	// 3. CKS = the number of clocks per bit.
	//
	// Everything stays constant during the CKS clocks with the exception
	// of (zero_baud_counter), which is *only* raised on the last clock
	// interval
	sequence	BAUD_INTERVAL(CKS, DAT, SR, ST);
		((o_uart_tx == DAT)&&(state == ST)
			&&(lcl_data == SR)
			&&(!zero_baud_counter))[*(CKS-1)]
		##1 (o_uart_tx == DAT)&&(state == ST)
			&&(lcl_data == SR)
			&&(zero_baud_counter);
	endsequence
	// }}}

	//
	// One byte transmitted
	// {{{
	//
	// DATA = the byte that is sent
	// CKS  = the number of clocks per bit
	//
	sequence	SEND(CKS, DATA);
		BAUD_INTERVAL(CKS, 1'b0, DATA, 4'h0)
		##1 BAUD_INTERVAL(CKS, DATA[0], {{(1){1'b1}},DATA[7:1]}, 4'h1)
		##1 BAUD_INTERVAL(CKS, DATA[1], {{(2){1'b1}},DATA[7:2]}, 4'h2)
		##1 BAUD_INTERVAL(CKS, DATA[2], {{(3){1'b1}},DATA[7:3]}, 4'h3)
		##1 BAUD_INTERVAL(CKS, DATA[3], {{(4){1'b1}},DATA[7:4]}, 4'h4)
		##1 BAUD_INTERVAL(CKS, DATA[4], {{(5){1'b1}},DATA[7:5]}, 4'h5)
		##1 BAUD_INTERVAL(CKS, DATA[5], {{(6){1'b1}},DATA[7:6]}, 4'h6)
		##1 BAUD_INTERVAL(CKS, DATA[6], {{(7){1'b1}},DATA[7:7]}, 4'h7)
		##1 BAUD_INTERVAL(CKS, DATA[7], 8'hff, 4'h8)
		##1 BAUD_INTERVAL(CKS, 1'b1, 8'hff, 4'h9);
	endsequence
	// }}}

	//
	// Transmit one byte
	// {{{
	// Once the byte is transmitted, make certain we return to
	// idle
	//
	assert property (
		@(posedge i_clk)
		(i_wr)&&(!o_busy)
		|=> ((o_busy) throughout SEND(CLOCKS_PER_BAUD,fsv_data))
		##1 (!o_busy)&&(o_uart_tx)&&(zero_baud_counter));
	// }}}

	// {{{
	assume property (
		@(posedge i_clk)
		(i_wr)&&(o_busy) |=>
			(i_wr)&&(o_busy)&&($stable(i_data)));

	//
	// Make certain that o_busy is true any time zero_baud_counter is
	// non-zero
	//
	always @(*)
		assert((o_busy)||(zero_baud_counter) );

	// If and only if zero_baud_counter is true, baud_counter must be zero
	// Insist on that relationship here.
	always @(*)
		assert(zero_baud_counter == (baud_counter == 0));

	// To make certain baud_counter stays below CLOCKS_PER_BAUD
	always @(*)
		assert(baud_counter < CLOCKS_PER_BAUD);

	//
	// Insist that we are only ever in a valid state
	always @(*)
		assert((state <= `TXUL_STOP+1'b1)||(state == `TXUL_IDLE));
	// }}}

`endif // Verific SVA
endmodule
////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	ufifo.v
//
// Project:	wbuart32, a full featured UART with simulator
//
// Purpose:	A synchronous data FIFO, designed for supporting the Wishbone
//		UART.  Particular features include the ability to read and
//	write on the same clock, while maintaining the correct output FIFO
//	parameters.  Two versions of the FIFO exist within this file, separated
//	by the RXFIFO parameter's value.  One, where RXFIFO = 1, produces status
//	values appropriate for reading and checking a read FIFO from logic,
//	whereas the RXFIFO = 0 applies to writing to the FIFO from bus logic
//	and reading it automatically any time the transmit UART is idle.
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
`default_nettype	none
//
module ufifo(i_clk, i_reset, i_wr, i_data, o_empty_n, i_rd, o_data, o_status, o_err);
	parameter	BW=8;	// Byte/data width
	parameter [3:0]	LGFLEN=4;
	parameter [0:0]	RXFIFO=1'b1;
	input	wire		i_clk, i_reset;
	input	wire		i_wr;
	input	wire [(BW-1):0]	i_data;
	output	wire		o_empty_n;	// True if something is in FIFO
	input	wire		i_rd;
	output	wire [(BW-1):0]	o_data;
	output	wire	[15:0]	o_status;
	output	wire		o_err;

	localparam	FLEN=(1<<LGFLEN);

	reg	[(BW-1):0]	fifo[0:(FLEN-1)];
	reg	[(BW-1):0]	r_data, last_write;
	reg	[(LGFLEN-1):0]	wr_addr, rd_addr, r_next;
	reg			will_overflow, will_underflow;
	reg			osrc;

	wire	[(LGFLEN-1):0]	w_waddr_plus_one, w_waddr_plus_two;
	wire			w_write, w_read;
	reg	[(LGFLEN-1):0]	r_fill;
	wire	[3:0]		lglen;
	wire			w_half_full;
	reg	[9:0]		w_fill;

	assign	w_write = (i_wr && (!will_overflow || i_rd));
	assign	w_read  = (i_rd && o_empty_n);

	assign	w_waddr_plus_two = wr_addr + 2;
	assign	w_waddr_plus_one = wr_addr + 1;

	initial	will_overflow = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		will_overflow <= 1'b0;
	else if (i_rd)
		will_overflow <= (will_overflow)&&(i_wr);
	else if (w_write)
		will_overflow <= (will_overflow)||(w_waddr_plus_two == rd_addr);
	else if (w_waddr_plus_one == rd_addr)
		will_overflow <= 1'b1;

	// Write

	initial	wr_addr = 0;
	always @(posedge i_clk)
	if (i_reset)
		wr_addr <= { (LGFLEN){1'b0} };
	else if (w_write)
		wr_addr <= w_waddr_plus_one;

	always @(posedge i_clk)
	if (w_write) // Write our new value regardless--on overflow or not
		fifo[wr_addr] <= i_data;

	// Reads
	//	Following a read, the next sample will be available on the
	//	next clock
	//	Clock	ReadCMD	ReadAddr	Output
	//	0	0	0		fifo[0]
	//	1	1	0		fifo[0]
	//	2	0	1		fifo[1]
	//	3	0	1		fifo[1]
	//	4	1	1		fifo[1]
	//	5	1	2		fifo[2]
	//	6	0	3		fifo[3]
	//	7	0	3		fifo[3]

	initial	will_underflow = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		will_underflow <= 1'b1;
	else if (i_wr)
		will_underflow <= 1'b0;
	else if (w_read)
		will_underflow <= (will_underflow)||(r_next == wr_addr);

	//
	// Don't report FIFO underflow errors.  These'll be caught elsewhere
	// in the system, and the logic below makes it hard to reset them.
	// We'll still report FIFO overflow, however.
	//
	initial	rd_addr = 0;
	initial	r_next  = 1;
	always @(posedge i_clk)
	if (i_reset)
	begin
		rd_addr <= 0;
		r_next  <= 1;
	end else if (w_read)
	begin
		rd_addr <= rd_addr + 1;
		r_next  <= rd_addr + 2;
	end

	always @(posedge i_clk)
	if (w_read)
		r_data <= fifo[r_next[LGFLEN-1:0]];

	always @(posedge i_clk)
	if (i_wr && (!o_empty_n || (w_read && r_next == wr_addr)))
		last_write <= i_data;

	initial	osrc = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		osrc <= 1'b0;
	else if (i_wr && (!o_empty_n || (w_read && r_next == wr_addr)))
		osrc <= 1'b1;
	else if (i_rd)
		osrc <= 1'b0;

	assign o_data = (osrc) ? last_write : r_data;

	//
	// If this is a receive FIFO, the FIFO count that matters is the number
	// of values yet to be read.  If instead this is a transmit FIFO, then
	// the FIFO count that matters is the number of empty positions that
	// can still be filled before the FIFO is full.
	//
	// Adjust for these differences here.
	generate if (RXFIFO)
	begin : RXFIFO_FILL
		//
		// Calculate the number of elements in our FIFO
		//
		// Although used for receive, this is actually the more
		// generic answer--should you wish to use the FIFO in
		// another context.

		initial	r_fill = 0;
		always @(posedge i_clk)
		if (i_reset)
			r_fill <= 0;
		else case({ w_write, w_read })
		2'b01:	r_fill <= r_fill - 1'b1;
		2'b10:	r_fill <= r_fill + 1'b1;
		default:  begin end
		endcase

	end else begin : TXFIFO_FILL
		//
		// Calculate the number of empty elements in our FIFO
		//
		// This is the number you could send to the FIFO
		// if you wanted to.

		initial	r_fill = -1;
		always @(posedge i_clk)
		if (i_reset)
			r_fill <= -1;
		else case({ w_write, w_read })
		2'b01:	r_fill <= r_fill + 1'b1;
		2'b10:	r_fill <= r_fill - 1'b1;
		default:  begin end
		endcase

	end endgenerate

	// Flag any overflows
	assign o_err = (i_wr && !w_write);

	assign lglen = LGFLEN;

	always @(*)
	begin
		w_fill = 0;
		w_fill[(LGFLEN-1):0] = r_fill;
	end

	assign	w_half_full = r_fill[(LGFLEN-1)];

	assign	o_status = {
		// Our status includes a 4'bit nibble telling anyone reading
		// this the size of our FIFO.  The size is then given by
		// 2^(this value).  Hence a 4'h4 in this position means that the
		// FIFO has 2^4 or 16 values within it.
		lglen,
		// The FIFO fill--for a receive FIFO the number of elements
		// left to be read, and for a transmit FIFO the number of
		// empty elements within the FIFO that can yet be filled.
		w_fill,
		// A '1' here means a half FIFO length can be read (receive
		// FIFO) or written to (not a receive FIFO).  If one, a
		// halfway interrupt can be sent indicating a half of a FIFOs
		// operationw (either transmit or receive) will be successful.
		w_half_full,
		// A '1' here means the FIFO can be read from (if it is a
		// receive FIFO), or be written to (if it isn't).  An interrupt
		// may be sourced from this bit, indicating that at least one
		// operation will be successful.
		(RXFIFO!=0)?!will_underflow:!will_overflow
	};

	assign	o_empty_n = !will_underflow;

////////////////////////////////////////////////////////////////////////////////
//
// Formal property section
//
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg	f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	////////////////////////////////////////////////////////////////////////
	//
	// Pointer checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[LGFLEN-1:0]	f_fill;
	wire	[LGFLEN-1:0]	f_raddr_plus_one;

	always @(*)
		f_fill = wr_addr - rd_addr;

	always @(*)
		assert(will_underflow == (f_fill == 0));

	always @(*)
		assert(will_overflow  == (&f_fill));

	assign	f_raddr_plus_one = rd_addr + 1;

	always @(*)
		assert(f_raddr_plus_one  == r_next);

	always @(*)
	if (will_underflow)
	begin
		assert(!w_read);
		assert(!osrc);
	end


	always @(posedge i_clk)
	if (RXFIFO)
		assert(r_fill == f_fill);
	else
		assert(r_fill == (~f_fill));

	////////////////////////////////////////////////////////////////////////
	//
	// Twin write check
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
`ifdef	UFIFO
	(* anyconst *) reg [LGFLEN-1:0]	f_const_addr;
	(* anyconst *) reg [BW-1:0]	f_const_data, f_const_second;
	reg [LGFLEN-1:0]	f_next_addr;
	reg	[1:0]		f_state;
	reg			f_first_in_fifo, f_second_in_fifo;
	reg	[LGFLEN-1:0]	f_distance_to_first, f_distance_to_second;

	always @(*)
	begin
		f_next_addr = f_const_addr + 1;

		f_distance_to_first  = f_const_addr - rd_addr;
		f_distance_to_second = f_next_addr  - rd_addr;

		f_first_in_fifo  = (f_distance_to_first  < f_fill)
			&& !will_underflow
			&& (fifo[f_const_addr] == f_const_data);
		f_second_in_fifo = (f_distance_to_second < f_fill)
			&& !will_underflow
			&& (fifo[f_next_addr] == f_const_second);
	end

	initial	f_state = 2'b00;
	always @(posedge i_clk)
	if (i_reset)
		f_state <= 2'b00;
	else case(f_state)
	2'b00: if (w_write &&(wr_addr == f_const_addr)
			&&(i_data == f_const_data))
		f_state <= 2'b01;
	2'b01: if (w_read && (rd_addr == f_const_addr))
			f_state <= 2'b00;
		else if (w_write && (wr_addr == f_next_addr))
			f_state <= (i_data == f_const_second) ? 2'b10 : 2'b00;
	2'b10: if (w_read && (rd_addr == f_const_addr))
			f_state <= 2'b11;
	2'b11: if (w_read)
			f_state <= 2'b00;
	endcase

	always @(*)
	case(f_state)
	2'b00: begin end
	2'b01: begin
		assert(!will_underflow);
		assert(f_first_in_fifo);
		assert(!f_second_in_fifo);
		assert(wr_addr == f_next_addr);
		assert(fifo[f_const_addr] == f_const_data);
		if (rd_addr == f_const_addr)
			assert(o_data == f_const_data);
		end
	2'b10: begin
		assert(f_first_in_fifo);
		assert(f_second_in_fifo);
		end
	2'b11: begin
		assert(f_second_in_fifo);
		assert(rd_addr == f_next_addr);
		assert(o_data  == f_const_second);
		end
	endcase
`endif
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	cvr_filled;

	always @(*)
		cover(o_empty_n);

`ifdef	UFIFO
	always @(*)
		cover(o_err);

	initial	cvr_filled = 0;
	always @(posedge i_clk)
	if (i_reset)
		cvr_filled <= 0;
	else if (&f_fill[LGFLEN-1:0])
		cvr_filled <= 1;

	always @(*)
		cover(cvr_filled && !o_empty_n);
`endif // UFIFO
`endif
endmodule
