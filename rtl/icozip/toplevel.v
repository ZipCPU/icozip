////////////////////////////////////////////////////////////////////////////////
//
// Filename:	./toplevel.v
//
// Project:	ICO Zip, iCE40 ZipCPU demonstration project
//
// DO NOT EDIT THIS FILE!
// Computer Generated: This file is computer generated by AUTOFPGA. DO NOT EDIT.
// DO NOT EDIT THIS FILE!
//
// CmdLine:	autofpga autofpga -o . global.txt bkram.txt buserr.txt clock.txt pic.txt pwrcount.txt version.txt hbconsole.txt gpio.txt dlyarbiter.txt zipbones.txt spixpress.txt sramdev.txt sramscope.txt
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017-2018, Gisselquist Technology, LLC
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
// Here we declare our toplevel.v (toplevel) design module.
// All design logic must take place beneath this top level.
//
// The port declarations just copy data from the @TOP.PORTLIST
// key, or equivalently from the @MAIN.PORTLIST key if
// @TOP.PORTLIST is absent.  For those peripherals that don't need
// any top level logic, the @MAIN.PORTLIST should be sufficent,
// so the @TOP.PORTLIST key may be left undefined.
//
module	toplevel(i_clk,
	o_dbgwires,
		o_ram_ce_n, o_ram_oe_n, o_ram_we_n, o_ram_addr, o_ram_sel, 
			io_ram_data,
		// GPIO wires
		o_ledg, o_ledr, i_btn,
		// Top level Dual-SPI I/O ports
		o_spi_cs_n, o_spi_sck, o_spi_mosi, i_spi_miso,
		// Parallel port to wishbone / console interface
		i_pp_dir, i_pp_clk, io_pp_data, o_pp_clkfb);
	//
	// Declaring our input and output ports.  We listed these above,
	// now we are declaring them here.
	//
	// These declarations just copy data from the @TOP.IODECLS key,
	// or from the @MAIN.IODECL key if @TOP.IODECL is absent.  For
	// those peripherals that don't do anything at the top level,
	// the @MAIN.IODECL key should be sufficient, so the @TOP.IODECL
	// key may be left undefined.
	//
	input	wire		i_clk;
	output	wire	[7:0]	o_dbgwires;
	output	wire	o_ram_ce_n, o_ram_oe_n, o_ram_we_n;
	output	wire	[15:0]	o_ram_addr;
	output	wire	[1:0]	o_ram_sel;
	inout	wire	[15:0]	io_ram_data;
	// GPIO wires
	output	wire	[1:0]	o_ledg;
	output	wire		o_ledr;
	input	wire	[1:0]	i_btn;
	// Dual SPI flash
	output	wire		o_spi_cs_n;
	output	wire		o_spi_sck, o_spi_mosi;
	input	wire		i_spi_miso;
	// Parallel port to wishbone / console interface
	input	wire		i_pp_dir, i_pp_clk;
	inout	wire	[7:0]	io_pp_data;
	output	wire		o_pp_clkfb;


	//
	// Declaring component data, internal wires and registers
	//
	// These declarations just copy data from the @TOP.DEFNS key
	// within the component data files.
	//
	wire	[15:0]		i_ram_data, o_ram_data;

	// GPIO declarations.  The two wire busses are just virtual lists of
	// input (or output) ports.
	wire	[2 -1:0]	i_gpio;
	wire	[11-1:0]	o_gpio;
	wire		s_clk, s_reset;
	wire		spi_sck;
	//
	//
	// Parallel port interface
	//
	//
	wire	[7:0]	i_pp_data, w_pp_data;
	wire		w_pp_dbg;



	//
	// Time to call the main module within main.v.  Remember, the purpose
	// of the main.v module is to contain all of our portable logic.
	// Things that are Xilinx (or even Altera) specific, or for that
	// matter anything that requires something other than on-off logic,
	// such as the high impedence states required by many wires, is
	// kept in this (toplevel.v) module.  Everything else goes in
	// main.v.
	//
	// We automatically place s_clk, and s_reset here.  You may need
	// to define those above.  (You did, didn't you?)  Other
	// component descriptions come from the keys @TOP.MAIN (if it
	// exists), or @MAIN.PORTLIST if it does not.
	//

	main	thedesign(s_clk, s_reset,
		o_ram_ce_n, o_ram_oe_n, o_ram_we_n, o_ram_addr, o_ram_sel, 
			o_ram_data, i_ram_data,
		// GPIO wires
		i_gpio, o_gpio,
		// SPI flash
		o_spi_cs_n, spi_sck, o_spi_mosi, i_spi_miso,
		// External USB-UART bus control
		i_pp_clk, i_pp_dir, i_pp_data, w_pp_data, o_pp_clkfb, w_pp_dbg);


	//
	// Our final section to the toplevel is used to provide all of
	// that special logic that couldnt fit in main.  This logic is
	// given by the @TOP.INSERT tag in our data files.
	//


	assign	o_dbgwires[7:3] = { o_ram_ce_n, o_ram_oe_n, o_ram_we_n,
					o_ram_sel };
	assign	o_dbgwires[2:0] = (o_ram_we_n)? i_ram_data[2:0] : o_ram_data[2:0];

	//
	// SRAM Interface
	//
	// Use the PPIO primitive to give us access to a group of SB_IO's,
	// and therefore access to a tristate output
	//
	ppio #(.W(16))
		sramioi(o_ram_we_n, io_ram_data, o_ram_data, i_ram_data);


	assign	i_gpio = { i_btn };
	assign	o_ledr = o_gpio[0];
	assign	o_ledg = o_gpio[2:1];

	assign	s_reset = 1'b0; // This design requires local, not global resets

`ifdef	VERILATOR
	assign	s_clk = i_clk;
`else
	reg	[1:0]	clkgen;
	reg		clk_25mhz;

	initial clkgen = 2'b00;
	always @(posedge i_clk)
		clkgen <= clkgen + 1'b1;

	initial	clk_25mhz = 1'b0;
	always @(posedge i_clk)
		clk_25mhz <= clkgen[1];

	SB_GB global_buffer(clk_25mhz, s_clk);
`endif


	//
	//
	// Wires for setting up the SPI flash wishbone peripheral
	//
	//
	oclkddr spi_ddr_sck(s_clk, {!spi_sck, 1'b1}, o_spi_sck);


	//
	// Parallel port I/O pin control
	ppio	hbi_io(i_pp_dir, io_pp_data, w_pp_data, i_pp_data);



endmodule // end of toplevel.v module definition
