////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	testbus.v
//
// Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
//
// Purpose:	This file composes a top level "demonstration" bus that can
//		be used to prove that things work.  Components contained within
//	this demonstration include:
//
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2019, Gisselquist Technology, LLC
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
//
module	testbus(i_clk, i_btn, o_ledg, o_ledr,
		i_pp_dir, i_pp_clk, io_pp_data, o_pp_clkfb);
	parameter	NBTNS=2;
	input	wire		i_clk;
	input	wire	[1:0]	i_btn;
	output	wire	[1:0]	o_ledg;
	output	wire		o_ledr;
	//
	input	wire		i_pp_dir, i_pp_clk;
	inout	wire	[7:0]	io_pp_data;
	output	wire		o_pp_clkfb;

	wire	s_clk;
`ifdef	VERILATOR
	assign	s_clk = i_clk;
`else
	wire	clk_80mhz, pll_locked;
	SB_PLL40_PAD #(
		.FEEDBACK_PATH("SIMPLE"),
		.DELAY_ADJUSTMENT_MODE_FEEDBACK("FIXED"),
		.DELAY_ADJUSTMENT_MODE_RELATIVE("FIXED"),
		.PLLOUT_SELECT("GENCLK"),
		.FDA_FEEDBACK(4'b1111),
		.FDA_RELATIVE(4'b1111),
		.DIVR(4'd4),		// Divide by (DIVR+1)  = 5
		.DIVQ(3'd3),		// Divide by 2^(DIVQ)  = 1
		.DIVF(7'd31),		// Multiply by (DIVF+1)= 4
		.FILTER_RANGE(3'b010)
	) plli (
		.PACKAGEPIN     (i_clk        ),
		.PLLOUTCORE     (clk_80mhz    ),
		.LOCK           (pll_locked  ),
		.BYPASS         (1'b0         ),
		.RESETB         (1'b1         )
	);

	assign	s_clk = clk_80mhz;
`endif


	wire		rx_stb;
	wire	[7:0]	rx_data;
	wire		tx_stb, tx_busy;
	wire	[7:0]	tx_data;
	//
	wire	[7:0]	w_pp_data, i_pp_data;

	pport	pporti(s_clk,
		rx_stb, rx_data,
		tx_stb, { 1'b1, tx_data[6:0] }, tx_busy,
		i_pp_dir, i_pp_clk, i_pp_data, w_pp_data,
		o_pp_clkfb);
`ifdef	VERILATOR
	assign	io_pp_data = (i_pp_dir) ? 8'bzzzz_zzzz : w_pp_data;
	assign	i_pp_data = io_pp_data;
`else
	ppio	theppio(i_pp_dir, io_pp_data, w_pp_data, i_pp_data);
`endif

	// Bus interface wires
	wire	wb_cyc, wb_stb, wb_we;
	wire	[29:0]	wb_addr;
	wire	[31:0]	wb_odata;
	wire	[3:0]	wb_sel;
	reg		wb_ack;
	wire		wb_stall;
	reg		wb_err;
	reg	[31:0]	wb_idata;
	wire		bus_interrupt;

	hbbus	genbus(s_clk,
		// The receive transport wires
		rx_stb, { 1'b0, rx_data[6:0] },
		// The bus control output wires
		wb_cyc, wb_stb, wb_we, wb_addr, wb_odata, wb_sel,
		//	The return bus wires
		  wb_ack, wb_stall, wb_err, wb_idata,
		// An interrupt line
		bus_interrupt,
		// The return transport wires
		tx_stb, tx_data, tx_busy);

	//
	// Define some wires for returning values to the bus from our various
	// components
	reg	[31:0]	smpl_data;
	wire	[31:0]	scop_data;
	wire	smpl_stall, scop_stall;
	wire	scop_int;
	reg	smpl_interrupt;
	wire	scop_ack;
	reg	smpl_ack;

	wire	smpl_sel, scop_sel;

	// Nothing should be assigned to the null page
	assign	smpl_sel = (wb_addr[29:4] == 26'h081);
	assign	scop_sel = (wb_addr[29:4] == 26'h082);

	// The "null" device
	//
	// Replaced with looking for nothing being selected
	wire	none_sel;
	assign	none_sel = (!smpl_sel)&&(!scop_sel);

	always @(posedge s_clk)
		wb_err <= (wb_stb)&&(none_sel);


	// A "Simple" example device
	reg	[31:0]		smpl_register, power_counter;
	wire	[31:0]		transitions, max_clock;
	wire	[(NBTNS-1):0]	debounced;
	reg	[29:0]		bus_err_address;

	always @(posedge s_clk)
		smpl_ack <= ((wb_stb)&&(smpl_sel));
	assign	smpl_stall = 1'b0;
	initial	smpl_interrupt = 1'b0;
	initial	smpl_register  =    0;
	always @(posedge s_clk)
		if ((wb_stb)&&(smpl_sel)&&(wb_we))
		begin
			case(wb_addr[3:0])
			4'h1: smpl_register  <= wb_odata;
			4'h4: smpl_interrupt <= wb_odata[0];
			default: begin end
			endcase
		end

	always @(posedge s_clk)
		case(wb_addr[3:0])
		4'h0:    smpl_data <= 32'h20170622;
		4'h1:    smpl_data <= smpl_register;
		4'h2:    smpl_data <= { bus_err_address, 2'b00 };
		4'h3:    smpl_data <= power_counter;
		4'h4:    smpl_data <= { 31'h0, smpl_interrupt };
		4'h6:    smpl_data <= transitions;
		4'h7:    smpl_data <= max_clock;
		4'h8:    smpl_data <= { {(32-NBTNS){1'b0}}, debounced };
		default: smpl_data <= 32'h00;
		endcase

	// Start our clocks since power up counter from zero
	initial	power_counter = 0;
	always @(posedge s_clk)
		// Count up from zero until the top bit is set
		if (!power_counter[31])
			power_counter <= power_counter + 1'b1;
		else // Once the top bit is set, keep it set forever
			power_counter[30:0] <= power_counter[30:0] + 1'b1;

	initial	bus_err_address = 0;
	always @(posedge s_clk)
		if (wb_err)
			bus_err_address <= wb_addr;

	//
	// The debouncing device
	//
	wire	[30:0]	debounce_dbg;
	debouncer	#(NBTNS) thedebouncer(s_clk, i_btn,
					debounced, debounce_dbg);
	wire	unbounce_reset;
	assign	unbounce_reset = (wb_stb)&&(wb_we)&&(smpl_sel)
					&&(wb_addr[3:1]==3'b011);
	unbounced	#(NBTNS) theunbouncer(s_clk, 
					unbounce_reset,
					i_btn, transitions, max_clock);
	//
	// A wishbone scope
	//
	wire	scope_trigger;
	assign	scope_trigger = debounce_dbg[29];
	wire	[30:0]	debug_data;
	assign	debug_data    = debounce_dbg;
	wbscopc	#(5'd9) thescope(s_clk, 1'b1, scope_trigger, debug_data,
		s_clk, wb_cyc, (wb_stb)&&(scop_sel), wb_we, wb_addr[0],wb_odata,
		scop_ack, scop_stall, scop_data,
		scop_int);

	//
	//
	// Bus response composition
	//
	//
	// Now, let's put those bus responses together
	//
	always @(posedge s_clk)
		wb_ack <= (smpl_ack)||(scop_ack);

	always @(posedge s_clk)
		if (smpl_ack)
			wb_idata <= smpl_data;
		else if (scop_ack)
			wb_idata <= scop_data;
		else
			wb_idata <= 32'h0;

	assign	wb_stall = ((smpl_sel)&&(smpl_stall))
			||((scop_sel)&&(scop_stall));

	assign	bus_interrupt = (smpl_interrupt) | (scop_int);

	assign	o_ledg = i_btn;
	assign	o_ledr = scop_int;

`ifdef	VERILATOR
	// Make Verilator happy
	// verilator lint_off UNUSED
	wire	[(5+9-1):0]	unused;
	assign	unused = { rx_data[7], wb_sel,
		wb_odata[30:28], wb_odata[25:20] };
	// verilator lint_on  UNUSED
`endif
endmodule
