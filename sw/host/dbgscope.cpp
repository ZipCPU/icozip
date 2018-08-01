////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	dbgscope.cpp
//
// Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
//
// Purpose:	An ad-hoc scope, whose purpose changes with need
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
#include "hexbus.h"
#include "scopecls.h"

#ifdef	R_DBGSCOPE

#define	WBSCOPE		R_DBGSCOPE
#define	WBSCOPEDATA	R_DBGSCOPED

FPGA	*m_fpga;

#define	BIT(V,N)	((V>>N)&1)
#define	BITV(N)		BIT(val,N)


void	usage(void) {
	printf("USAGE: dbgscope [-n host] [-p port]\n"
"\n"
"\t[-n host]\tAttempt to connect, via TCP/IP, to host named [host].\n"
"\t\tThe default host is \'%s\'\n"
"\n"
"\t-p [port]\tAttempt to connect, via TCP/IP, to port number [port].\n"
"\t\tThe default port is \'%d\'\n"
"\n", FPGAHOST, FPGAPORT);
}

class	DBGSCOPE : public SCOPE {
public:
	DBGSCOPE(FPGA *fpga, unsigned addr, bool vecread)
		: SCOPE(fpga, addr, false, false) {};
	~DBGSCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {

		printf("%s -- ", (BITV(31))?"ER":"  ");
		printf("%s ", BITV(25)?"CE":"  ");
		printf("%s ", BITV(24)?"SLP":"   ");
		printf("%s ", BITV(24)?"SLP":"   ");
		printf("%s ", BITV(23)?"GIE":"   ");
		printf("%s ", BITV(22)?"INT":"   ");
		printf("%s%s%s%d ",
			BITV(20)?"CYC":"   ",
			BITV(19)?"STB":"   ",
			BITV(18)?"W":"   ",
			(val>>16)&2);
		printf("%02x:%02x", (val>>16)&0x0ff, val&0x0ff);
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

	DBGSCOPE *scope = new DBGSCOPE(m_fpga, WBSCOPE, false);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("dbgscope.vcd");
	}
	delete	m_fpga;
}
#else

int main(int argc, char **argv) {
	fprintf(stderr, "ERR: Design had no DBG scope when this was built\n");
	exit(EXIT_FAILURE);
}
#endif
