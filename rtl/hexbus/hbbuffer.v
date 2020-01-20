////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	hbbuffer.v
//
// Project:	dbgbus, a collection of 8b channel to WB bus debugging protocols
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2018-2020, Gisselquist Technology, LLC
//
// This file is part of the hexbus debugging interface.
//
// The hexbus interface is free software (firmware): you can redistribute it
// and/or modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation, either version 3 of the
// License, or (at your option) any later version.
//
// The hexbus interface is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public License
// for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program.  (It's in the $(ROOT)/doc directory.  Run make
// with no target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	LGPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/lgpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
//
//
module	hbbuffer(i_clk, i_reset, i_stb, i_word, o_busy,
			o_stb, o_word, i_busy);
	parameter	W=8;
	input	wire		i_clk, i_reset;
	//
	input	wire		i_stb;
	input	wire	[W-1:0]	i_word;
	output	wire		o_busy;
	//
	output	reg		o_stb;
	output	reg	[W-1:0]	o_word;
	input	wire		i_busy;

	reg		r_stb;
	reg	[W-1:0]	r_word;

	initial	r_stb = 1'b0;
	initial	o_stb = 1'b0;
	always @(posedge i_clk)
	begin
		if ((i_stb)&&(!o_busy))
		begin
			r_stb  <= (i_busy);
			r_word <= i_word;

			if (!i_busy)
			begin
				o_stb  <= 1'b1;
				o_word <= i_word;
			end
		end else if (!i_busy)
		begin
			o_stb  <= r_stb;
			o_word <= r_word;
			r_stb  <= 1'b0;
		end

		if (i_reset)
		begin
			o_stb <= 1'b0;
			r_stb <= 1'b0;
		end
	end

	assign	o_busy = r_stb;
`ifdef	FORMAL
`ifdef	HBBUFFER
`define	ASSUME	assume
`define	ASSERT	assert
`else
`define	ASSUME	assert
`define	ASSERT	assert
`endif

	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		`ASSUME(!i_stb);
		//
		`ASSERT(!r_stb);
		`ASSERT(!o_stb);
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset)))
	begin

		// Stability assumption about the input
		if (($past(i_stb))&&($past(o_busy)))
			`ASSUME(($stable(i_stb))&&($stable(i_word)));

		// Input goes directly to the output ... if we aren't busy
		if (($past(i_stb))&&(!$past(o_busy)))
		begin
			if ($past(i_busy))
				`ASSERT((r_stb)&&(r_word == $past(i_word)));
			else
				`ASSERT((o_stb)&&(o_word == $past(i_word)));
		end

		// Input goes directly to r_ if we are busy
		if (($past(i_stb))&&($past(o_stb))&&($past(i_busy))
				&&(!$past(r_stb)))
		begin
			`ASSERT((o_stb)&&($stable(o_word)));
			`ASSERT((r_stb)&&(r_word == $past(i_word)));
		end

		// Processing to the output
		if (($past(r_stb))&&(!$past(i_busy)))
			`ASSERT((o_stb)&&(o_word == $past(r_word))&&(!r_stb));

		// If we have to wait, r_stb register
		if (($past(r_stb))&&($past(i_busy)))
			`ASSERT((r_stb)&&($stable(r_word)));

		// If we have to wait, o_stb register
		if (($past(o_stb))&&($past(i_busy)))
			`ASSERT((o_stb)&&($stable(o_word)));
	end

`endif
endmodule

