////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	blinky.v
//
// Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
//
// Purpose:	Every board needs a blinky demo.  The ICO board is no different.
//		This demo, however, is different from the one delivered on the
//	board.  That allows you to prove, by loading this demo, that you can 
//	load your own configurations to the board.
//
//	Ok, so what does this do?  It proves that you can control all three
//	LEDs, and that you can read from both buttons, and that you can know
//	which LED is which.
//
//	The LEDs and switches are numbered similar to the board: low numbered
//	switches remain low numbered switches here, same with high numbered
//	ones.  Still, we've renamed the led's from led1, led2, and led3, to
//	help indicate that they have different colors associated with them.
//
//	If you get this working, you will notice ...
//	- One LED, green LED 0, blinking, and nothing else on.
//	- When you press a button, ...
//		The red LED will go on, no matter which button you push.
//		If you press the button next to the blinking LED, then it will
//			stop blinking.
//		If you press the other button, it will start blinking in a
//			fashion so that it alternates with the first blinking
//			LED.
//		The button pressed should correlate to the LED that changes.
//
//	By these tests, you should know which button is which, and which LED
//	is which.
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
module	blinky(i_clk, i_btn, o_ledg, o_ledr);
	parameter	CBITS = 27;
	input			i_clk;
	input		[1:0]	i_btn;
	output	wire	[1:0]	o_ledg;
	output	wire		o_ledr;

	// A counter--just to set things off and get things blinking.
	reg [(CBITS-1):0]	ctr;
	initial ctr = 0;
	always @(posedge i_clk)
		ctr <= ctr + 1'b1;

	// LED 0 ... Only turns on when button #1 is pressed.
	assign	o_ledg[0] = ((!ctr[CBITS-1]) & (i_btn[1]==1));

	// LED 1 ... always blinking, unless button #0 is pressed.
	assign	o_ledg[1] = (( ctr[CBITS-1]) & (i_btn[0]==0));

	// RED LED ... always ever blinks whenever either button is pressed
	assign	o_ledr = (i_btn[0])|(i_btn[1]);

endmodule
