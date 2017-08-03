////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbpport.v
//
// Project:
//
// Purpose:
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
`define	PPORT_SETUP	2'b00
`define	PPORT_FIFO	2'b01
`define	PPORT_RXREG	2'b10
`define	PPORT_TXREG	2'b11
module	wbpport(i_clk, i_rst,
		//
		i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data,
			o_wb_ack, o_wb_stall, o_wb_data,
		//
		i_pp_stb, i_pp_data,
		o_pp_stb, o_pp_data, i_pp_busy,
		//
		o_rx_int, o_tx_int,
		o_rxfifo_int, o_txfifo_int);
	parameter	LGFLEN = 4;
	// Perform a simple/quick bounds check on the log FIFO length, to make
	// sure its within the bounds we can support with our current
	// interface.
	localparam [3:0]	LCLLGFLEN = (LGFLEN > 4'ha)? 4'ha
					: ((LGFLEN < 4'h2) ? 4'h2 : LGFLEN);
	//
	input	wire		i_clk, i_rst;
	// Wishbone inputs
	input	wire		i_wb_cyc, i_wb_stb, i_wb_we;
	input	wire	[1:0]	i_wb_addr;
	input	wire	[31:0]	i_wb_data;
	output	reg		o_wb_ack;
	output	wire		o_wb_stall;
	output	reg	[31:0]	o_wb_data;
	//
	input	wire		i_pp_stb;
	input	wire	[6:0]	i_pp_data;
	//
	output	wire		o_pp_stb;
	output	wire	[6:0]	o_pp_data;
	input	wire		i_pp_busy;
	//
	output	wire		o_rx_int, o_tx_int,
				o_rxfifo_int, o_txfifo_int;

	//
	wire	[31:0]	pp_setup;
	assign	pp_setup = 32'd12;

	/////////////////////////////////////////
	//
	//
	// First, the receiver
	//
	//
	/////////////////////////////////////////


	// We place it into a receiver FIFO.
	//
	// Here's the declarations for the wires it needs.
	reg		rx_pp_reset;
	wire		rx_empty_n, rx_fifo_err;
	wire	[6:0]	rxf_wb_data;
	wire	[15:0]	rxf_status;
	reg		rxf_wb_read;
	//
	// And here's the FIFO proper.
	//
	// Note that the FIFO will be cleared upon any reset
	//
	// The FIFO accepts strobe and data from the receiver.
	// We issue another wire to it (rxf_wb_read), true when we wish to read
	// from the FIFO, and we get our data in rxf_wb_data.  The FIFO outputs
	// four status-type values: 1) is it non-empty, 2) is the FIFO over half
	// full, 3) a 16-bit status register, containing info regarding how full
	// the FIFO truly is, and 4) an error indicator.
	ufifo	#(.LGFLEN(LCLLGFLEN), .BW(7), .RXFIFO(1))
		rxfifo(i_clk, (i_rst)||(rx_pp_reset),
			i_pp_stb, i_pp_data,
			rx_empty_n,
			rxf_wb_read, rxf_wb_data,
			rxf_status, rx_fifo_err);
	assign	o_rxfifo_int = rxf_status[1];

	// We produce four interrupts.  One of the receive interrupts indicates
	// whether or not the receive FIFO is non-empty.  This should wake up
	// the CPU.
	assign	o_rx_int = rxf_status[0];

	// If the bus requests that we read from the receive FIFO, we need to
	// tell this to the receive FIFO.  Note that because we are using a 
	// clock here, the output from the receive FIFO will necessarily be
	// delayed by an extra clock.
	initial	rxf_wb_read = 1'b0;
	always @(posedge i_clk)
		rxf_wb_read <= (i_wb_stb)&&(i_wb_addr[1:0]==`PPORT_RXREG)
				&&(!i_wb_we);

	initial	rx_pp_reset = 1'b1;
	always @(posedge i_clk)
		if ((i_rst)||((i_wb_stb)&&(i_wb_addr[1:0]==`PPORT_SETUP)&&(i_wb_we)))
			// The receiver reset, always set on a master reset
			// request.
			rx_pp_reset <= 1'b1;
		else if ((i_wb_stb)&&(i_wb_addr[1:0]==`PPORT_RXREG)&&(i_wb_we))
			// Writes to the receive register will command a receive
			// reset anytime bit[12] is set.
			rx_pp_reset <= i_wb_data[12];
		else
			rx_pp_reset <= 1'b0;

	// Finally, we'll construct a 32-bit value from these various wires,
	// to be returned over the bus on any read.  These include the data
	// that would be read from the FIFO, an error indicator set upon
	// reading from an empty FIFO, a break indicator, and the frame and
	// parity error signals.
	wire	[31:0]	wb_rx_data;
	assign	wb_rx_data = { 16'h00, 4'h0, 3'h0, !rx_empty_n,
				1'b0, rxf_wb_data};

	/////////////////////////////////////////
	//
	//
	// Then the transmitter
	//
	//
	/////////////////////////////////////////
	wire		tx_empty_n, txf_err;
	wire	[15:0]	txf_status;
	reg		txf_wb_write, tx_pp_reset;
	reg	[6:0]	txf_wb_data;

	// Unlike the receiver which goes from RX -> UFIFO -> WB, the
	// transmitter basically goes WB -> UFIFO -> TX.  Hence, to build
	// support for the transmitter, we start with the command to write data
	// into the FIFO.  In this case, we use the act of writing to the 
	// PPORT_TXREG address as our indication that we wish to write to the 
	// FIFO.  Here, we create a write command line, and latch the data for
	// the extra clock that it'll take so that the command and data can be
	// both true on the same clock.
	initial	txf_wb_write = 1'b0;
	always @(posedge i_clk)
	begin
		txf_wb_write <= (i_wb_stb)&&(i_wb_addr == `PPORT_TXREG)
					&&(i_wb_we);
		txf_wb_data  <= i_wb_data[6:0];
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
	ufifo	#(.LGFLEN(LGFLEN), .BW(7), .RXFIFO(0))
		txfifo(i_clk, (tx_pp_reset),
			txf_wb_write, txf_wb_data,
			tx_empty_n,
			(!i_pp_busy)&&(tx_empty_n), o_pp_data,
			txf_status, txf_err);

	assign	o_pp_stb = tx_empty_n;

	// Let's create two transmit based interrupts from the FIFO for the CPU.
	//	The first will be true any time the FIFO has at least one open
	//	position within it.
	assign	o_tx_int = txf_status[0];
	//	The second will be true any time the FIFO is less than half
	//	full, allowing us a change to always keep it (near) fully 
	//	charged.
	assign	o_txfifo_int = txf_status[1];

	// TX-Reset logic
	//
	// This is nearly identical to the RX reset logic above.  Basically,
	// any time someone writes to bit [12] the transmitter will go through
	// a reset cycle.  Keep bit [12] low, and everything will proceed as
	// normal.
	initial	tx_pp_reset = 1'b1;
	always @(posedge i_clk)
		if((i_rst)||((i_wb_stb)&&(i_wb_addr == `PPORT_SETUP)&&(i_wb_we)))
			tx_pp_reset <= 1'b1;
		else if ((i_wb_stb)&&(i_wb_addr[1:0]==`PPORT_TXREG)&&(i_wb_we))
			tx_pp_reset <= i_wb_data[12];
		else
			tx_pp_reset <= 1'b0;

	// Now that we are done with the chain, pick some wires for the user
	// to read on any read of the transmit port.
	//
	// This port is different from reading from the receive port, since
	// there are no side effects.  (Reading from the receive port advances
	// the receive FIFO, here only writing to the transmit port advances the
	// transmit FIFO--hence the read values are free for ... whatever.)
	//
	wire	[31:0]	wb_tx_data;
	assign	wb_tx_data = { 16'h00, 
				1'b0, txf_status[1:0], txf_err,
				1'b0, o_pp_stb, 1'b0, (i_pp_busy|txf_status[0]),
				1'b0,(i_pp_busy|txf_status[0])?txf_wb_data:7'h0};

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
	always @(posedge i_clk) // We'll ACK in two clocks
		r_wb_ack <= i_wb_stb;
	always @(posedge i_clk) // Okay, time to set the ACK
		o_wb_ack <= r_wb_ack;

	// Finally, set the return data.  This data must be valid on the same
	// clock o_wb_ack is high.  On all other clocks, it is irrelelant--since
	// no one cares, no one is reading it, it gets lost in the mux in the
	// interconnect, etc.  For this reason, we can just simplify our logic.
	always @(posedge i_clk)
		casez(r_wb_addr)
		`PPORT_SETUP: o_wb_data <= pp_setup;
		`PPORT_FIFO:  o_wb_data <= wb_fifo_data;
		`PPORT_RXREG: o_wb_data <= wb_rx_data;
		`PPORT_TXREG: o_wb_data <= wb_tx_data;
		endcase

	// This device never stalls.  Sure, it takes two clocks, but they are
	// pipelined, and nothing stalls that pipeline.  (Creates FIFO errors,
	// perhaps, but doesn't stall the pipeline.)  Hence, we can just
	// set this value to zero.
	assign	o_wb_stall = 1'b0;

`ifdef	VERILATOR
	// Make Verilator happy
	//
	// verilator lint_off UNUSED
	wire	[25:0] unused;
	assign	unused = { i_wb_cyc, i_wb_data[31:13], i_wb_data[11:7],
			rx_fifo_err };
	// verilator lint_on  UNUSED
`endif
endmodule
