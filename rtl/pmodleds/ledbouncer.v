////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	ledbouncer.v
//
// Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
//
// Purpose:	Create a Knight-Rider themed output on a PMod, using a PMod
//		LED8 from Digilent
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
module	ledbouncer(i_clk, o_led);
	parameter			NLEDS=8, CTRBITS=25, NPWM = 7;
	input	wire			i_clk;
	output	reg	[(NLEDS-1):0]	o_led;

	reg	[(NLEDS-1):0]	led_owner;
	reg			led_dir;
	reg	[(CTRBITS-1):0]	led_ctr;
	reg			led_clk;
	reg	[(NPWM-1):0]	led_pwm [0:(NLEDS-1)];
	wire	[(NPWM-1):0]	br_ctr;

	// The
	always @(posedge i_clk)
		{ led_clk, led_ctr } <= led_ctr + {{(CTRBITS-2){1'b0}},2'b10};

	initial	led_owner = { {(NLEDS-1){1'b0}}, 1'b1};
	always @(posedge i_clk)
	if (led_owner == 0)
	begin
		led_owner <= { {(NLEDS-1){1'b0}}, 1'b1 };
		led_dir   <= 1'b1; // Left, or shift up
	end else if ((led_clk)&&(led_dir)) // Go left
	begin
		if (led_owner == { 1'b1, {(NLEDS-1){1'b0}} })
			led_dir <= !led_dir;
		else
			led_owner <= { led_owner[(NLEDS-2):0], 1'b0 };
	end else if (led_clk) begin
		if (led_owner == { {(NLEDS-1){1'b0}}, 1'b1 })
			led_dir <= !led_dir;
		else
			led_owner <= { 1'b0, led_owner[(NLEDS-1):1] };
	end

	genvar	k;
	generate for(k=0; k<(NLEDS); k=k+1)
		always@(posedge i_clk)
		if (led_clk)
		begin
			if (led_owner[k])
				led_pwm[k] <= 7'h7f;
			else if (led_pwm[k] > 7'h04)
				led_pwm[k] <= 7'h04;
			else if (led_pwm[k] > 0)
				led_pwm[k] <= led_pwm[k] - 1;
		/*
			else if (led_pwm[k] > 9'h03)
				led_pwm[k] <= 9'h03;
			else if (led_pwm[k] > 9'h02)
				led_pwm[k] <= 9'h02;
			else if (led_pwm[k] > 9'h01)
				led_pwm[k] <= 9'h01;
			else
				led_pwm[k] <= 9'h00;
		*/
		end
	endgenerate

	generate for(k=0; k<NPWM; k=k+1)
	begin : BIT_REVERSE_LED_COUNTER

		assign	br_ctr[k] = led_ctr[NPWM-1-k];

	end endgenerate

	generate for(k=0; k<(NLEDS); k=k+1)

		initial	o_led[k] = 0;
		always @(posedge i_clk)
		if (&led_pwm[k])
			o_led[k] <= 1'b1;
		else if (led_pwm[k] == 0)
			o_led[k] <= 1'b0;
		else
			o_led[k] <= (br_ctr[(NPWM-1):0]<=led_pwm[k]);
	endgenerate

endmodule

