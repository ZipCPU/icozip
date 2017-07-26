////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	btnscope.cpp
//
// Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
//
// Purpose:	
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
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>

#include "port.h"
#include "bregs.h"
#include "scopecls.h"
#include "hexbus.h"

#define	WBSCOPE		R_SCOPE
#define	WBSCOPEDATA	R_SCOPD

FPGA	*m_fpga;

class	BTNSCOPE : public SCOPE {
public:
	BTNSCOPE(FPGA *fpga, unsigned addr) : SCOPE(fpga, addr, true) {
		set_clkfreq_hz(80000000);
	};
	~BTNSCOPE(void) {}

	virtual	void	define_traces(void) {
		//
		register_trace("ztimer",    1, 30);
		register_trace("changed",   1, 29);
		// register_trace("hicount",   4, 18);
		register_trace("debounced", 4, 14);
		// register_trace("lowcount", 10,  4);
		register_trace("i_btn",     4,  0);
	}

	virtual	void	decode(DEVBUS::BUSW val) const {
		int	i_btn, debounced, changed, ztimer;

		ztimer    = (val >> 30)&1;
		changed   = (val >> 29)&1;
		debounced = (val >> 14)&0x0f;
		i_btn     = (val      )&0x0f;

		printf("%s", (ztimer)?"ZT":"  ");
		printf(" %s", (changed)?"CHANGED!":"        ");
		printf(" %x %x", (i_btn), debounced);
	}
};

int main(int argc, char **argv) {
	// Open and connect to our FPGA.  This macro needs to be defined in the
	// include files above.
	FPGAOPEN(m_fpga);

	// Here, we open a scope.  An BTNSCOPE specifically.  The difference
	// between an BTNSCOPE and any other scope is ... that the
	// BTNSCOPE has particular things wired to particular bits, whereas
	// a generic scope ... just has data.
	BTNSCOPE *scope = new BTNSCOPE(m_fpga, WBSCOPE);

	if (!scope->ready()) {
		// If we get here, then ... nothing started the scope.
		// It either hasn't primed, hasn't triggered, or hasn't finished
		// recording yet.  Trying to read data would do nothing but
		// read garbage, so we don't try.
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		// The scope has been primed, triggered, the holdoff wait 
		// period has passed, and the scope has now stopped.
		//
		// Hence we can read from our scope the values we need.
		scope->print();
		// If we want, we can also write out a VCD file with the data
		// we just read.
		scope->writevcd("scopd.vcd");
	}

	// Now, we're all done.  Let's be nice to our interface and shut it
	// down gracefully, rather than letting the O/S do it in ... whatever
	// manner it chooses.
	delete	m_fpga;
}
