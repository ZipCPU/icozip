////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	clktest.v
//
// Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
//
// Purpose:	To determine the actual clock rate of the ICO board.  If the
//		clock is configured properly within here, then one LED will 
//	flash once per second, and a second LED will flash once per minute.
//	You should be able to use your stopwatch thus with this program to
//	achieve some level of calibration.
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
module	clktest(i_clk, o_ledg, o_ledr);
	input			i_clk;
	output	wire	[1:0]	o_ledg;	// The two green LEDs
	output	wire		o_ledr;	// The one red LED

	// Our first task is to generate a strobe that will be true at the
	// top of any second.  We do this using a 32-bit counter, but step
	// the counter by 2^32/clock_rate.  Hence, after clock_rate clocks tick
	// by, the counter should roll over.
	reg		pps;
	reg [31:0]	ctr;
	initial ctr = 0;
	always @(posedge i_clk)
		{pps, ctr} <= ctr + 32'd43;	// Valid if CLKRATE = 100MHz
		// {pps, ctr} <= ctr + 32'd89;  // Good if CLKRATE =  48MHz
		// {pps, ctr} <= ctr + 32'd172; // Good if CLKRATE =  25MHz

	// Let's set an LED to reflect this once per second value, but also
	// set it so that it is true for 1/4 of a second, turning on at the
	// top of the second we are referencing.
	assign	o_ledg[0] = (ctr[31:30] == 2'b00);

	// Now, we move on to minutes.  We'll count up to 60, and then restart.
	// Well, in actuality, though, our counter will go from 0..59 and then
	// go back to zero--so it will never actually hit 60.
	reg	[5:0]	secs;
	initial	mins = 6'h0;
	always @(posedge i_clk)
		if (secs >= 6'd60)
			secs <= 6'h0;
		else if ((pps)&&(secs == 6'd59))
			secs <= 0;
		else if (pps)
			secs <= secs + 1'b1;

	// We'll set the second green LED to blink when this second counter
	// is at the top of a minute.  We'll leave it on for a full second,
	// and then off for the rest of the minute.
	assign	o_ledg[1] = (secs == 6'h00);

	// As for the third LED, the red one, we'll keep that one off.
	assign	o_ledr = 1'b0;

endmodule
