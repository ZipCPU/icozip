////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	ppio.v
//
// Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
//
// Purpose:	The parallel port on the icozip, the port to the RPi, is a
//		bi-directional port.  However, ... arachne-pnr doesn't
//	infer bi-directional logic properly yet.  This, then, creates
//	bi-directional logic at the port, encapsulating that final output
//	requirement.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017, Gisselquist Technology, LLC
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
// License:	GPL, v3, as defined and found on www.gnu.org, //		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
module	ppio(i_dir, io_data, i_data, o_data);
	parameter	W=8;
	input			i_dir;
	inout	[(W-1):0]	io_data;
	input	[(W-1):0]	i_data;
	output	[(W-1):0]	o_data;

	genvar	k;
	generate
	for(k=0; k<W; k = k+1)
		SB_IO #(.PULLUP(1'b0),
			.PIN_TYPE(6'b101001))
			theio(
				.OUTPUT_ENABLE(!i_dir),
				.PACKAGE_PIN(io_data[k]),
				.D_OUT_0(i_data[k]),
				.D_IN_0( o_data[k])
			);
	endgenerate

endmodule
