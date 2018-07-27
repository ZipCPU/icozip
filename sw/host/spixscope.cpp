////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	spixscope.cpp
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
// Copyright (C) 2018, Gisselquist Technology, LLC
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
#include "regdefs.h"
#include "scopecls.h"

#ifdef	R_SPIXSCOPE

#define	WBSCOPE		R_SPIXSCOPE
#define	WBSCOPEDATA	R_SPIXSCOPED

FPGA	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

#define	BIT(V,N)	((V>>N)&1)
#define	BITV(N)		BIT(val,N)

class	SPIXSCOPE : public SCOPE {
public:
	SPIXSCOPE(FPGA *fpga, unsigned addr, bool vecread)
		: SCOPE(fpga, addr, false, false) {};
	~SPIXSCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
		int	trig, cyc, stb, cfg, we, stall, ack, idata, odata,
			csn, sck, mosi, miso;

		trig  = BITV(31);
		cyc   = BITV(30);
		stb   = BITV(29);
		cfg   = BITV(28);
		we    = BITV(27);
		stall = BITV(26);
		ack   = BITV(25);
		idata = (val>>16)&0x1f;
		odata = (val>> 7)&0x1f;
		csn   = BITV(3);
		sck   = BITV(2);
		mosi  = BITV(1);
		miso  = BITV(0);

		printf("WB[%s%s%s%s,%03x -> %s%s/%03x] "
			(cyc)?"CYC":"   ", (stb)?"STB":"   ", (cfg)?"CFG":"   ",
			(wbwe)?"WE":"  ", (ack)?"ACK":"   ",
			(stall) ? "STALL":"     " (idata), (odata));
		printf("SPI[%s%s %d-%d]\n",
			(csn)?"   ":"CSN", (sck)?"   ":"SCK",
			(mosi), (miso));
	}
};

int main(int argc, char **argv) {
	FPGAOPEN(m_fpga);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	SPIXSCOPE *scope = new SPIXSCOPE(m_fpga, WBSCOPE, false);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else
		scope->read();
	delete	m_fpga;
}

#else // SPIXSCOPE
int main(int argc, char **argv) {
	fprintf(stderr, "SPI Xpress scope not built, rebuild project with SPIX scope enabled to use this.\n");
	exit(EXIT_FAILURE);
}
#endif
