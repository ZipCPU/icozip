////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sramscope.cpp
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
// Copyright (C) 2018-2020, Gisselquist Technology, LLC
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
#include "hexbus.h"
#include "scopecls.h"

#ifdef	R_RAMSCOPE

#define	WBSCOPE		R_RAMSCOPE
#define	WBSCOPEDATA	R_RAMSCOPED

FPGA	*m_fpga;

#define	BIT(V,N)	((V>>N)&1)
#define	BITV(N)		BIT(val,N)


void	usage(void) {
	printf("USAGE: flashid [-n host] [-p port]\n"
"\n"
"\t[-n host]\tAttempt to connect, via TCP/IP, to host named [host].\n"
"\t\tThe default host is \'%s\'\n"
"\n"
"\t-p [port]\tAttempt to connect, via TCP/IP, to port number [port].\n"
"\t\tThe default port is \'%d\'\n"
"\n", FPGAHOST, FPGAPORT);
}

class	SRAMSCOPE : public SCOPE {
public:
	SRAMSCOPE(FPGA *fpga, unsigned addr, bool vecread)
		: SCOPE(fpga, addr, false, false) {};
	~SRAMSCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
		int	cyc, stb, we, stall, ack,
			cen, oen, wen, sel, addr, data;

		// trig  = BITV(31);
		cyc   = BITV(30);
		stb   = BITV(29);
		we    = BITV(28);
		stall = BITV(27);
		ack   = BITV(26);
		cen   = BITV(25);
		oen   = BITV(24);
		wen   = BITV(23);
		sel   = (val >> 21) & 0x03;
		addr  = (val >> 16) & 0x01f;
		data  = val & 0x0ffff;

		printf("WB[%s%s%s -> %s%s] ",
			(cyc)?"CYC":"   ", (stb)?"STB":"   ",
			(we)?"WE":"  ", (ack)?"ACK":"   ",
			(stall) ? "STALL":"     ");
		printf("SRAM[%s%s%s/%s%s @[%x] %s %04x\n",
			(cen)?"  ":"CE", (oen)?"  ":"OE", (wen)?"  ":"WE",
			(sel&2)?"  ":"UB", (sel&1)?"  ":"LB", addr,
			(cen==0) ? ((wen) ? "->" : "<-") : "  ", data);
	}
};

int main(int argc, char **argv) {
	const char *host = FPGAHOST;
	int	port=FPGAPORT;

	for(int argn=1; argn<argc; argn++) {
		if (argv[argn][0] == '-') {
			if (argv[argn][1] == 'h') {
				usage();
				exit(EXIT_SUCCESS);
			} else if (argv[argn][1] == 'n') {
				if (argn+1 >= argc) {
					fprintf(stderr, "ERR: No network host given\n");
					exit(EXIT_SUCCESS);
				}
				host = argv[argn+1];
				printf("HOST = %s\n", host);
				argn++;
			} else if (argv[argn][1] == 'p') {
				if (argn+1 >= argc) {
					fprintf(stderr, "ERR: No network port # given\n");
					exit(EXIT_SUCCESS);
				}
				port = strtoul(argv[argn+1], NULL, 0);
				printf("PORT = %d\n", port);
				argn++;
			} else {
				usage();
				exit(EXIT_SUCCESS);
			}
		} else {
			usage();
			exit(EXIT_FAILURE);
		}
	}

	m_fpga = new FPGA(new NETCOMMS(host, port));

	SRAMSCOPE *scope = new SRAMSCOPE(m_fpga, WBSCOPE, false);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("sramscope.vcd");
	}
	delete	m_fpga;
}
#else

int main(int argc, char **argv) {
	fprintf(stderr, "ERR: Design had no SRAM scope when this was built\n");
	exit(EXIT_FAILURE);
}
#endif
