////////////////////////////////////////////////////////////////////////////////
//
// Filename:	dumpflash.cpp
//
// Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
//
// Purpose:	Read the entire contents of the flash memory into a file.
//		The flash is unchanged by this process.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2018, Gisselquist Technology, LLC
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

FPGA	*m_fpga;

#define	DUMPMEM		FLASHBASE
#define	DUMPWORDS	(FLASHLEN>>2)	// 16MB Flash

void	usage(void) {
	printf("USAGE:\tdumpflash [-n host] [-p port] filename.bin\n"
"\n"
"\tReads the values from the flash on board, and dumps them directly into\n"
"\tthe file filename.bin.\n");
}


int main(int argc, char **argv) {
	FILE		*fp = NULL;
	const int	BUFLN = DUMPWORDS; // 1MB Flash
	FPGA::BUSW	*buf = new FPGA::BUSW[BUFLN];
	const	char	*fname = NULL;

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
		} else if (fname == NULL) {
			fname = argv[argn];
		} else {
			usage();
			exit(EXIT_FAILURE);
		}
	}

	if (fname == NULL) {
		fprintf(stderr, "No filename given\n\n");
		usage();
		exit(EXIT_FAILURE);
	//} else if (0 != access(fname, W_OK)) {
		//fprintf(stderr, "ERR: No permission to write %s\n\n", fname);
		//exit(EXIT_FAILURE);
	}
		
	m_fpga = new FPGA(new NETCOMMS(host, port));


	// SPI flash testing
	// Enable the faster (vector) reads
	bool	vector_read = true;
	unsigned	sz;

	try {
		if (vector_read) {
			m_fpga->readi(DUMPMEM, BUFLN, buf);
		} else {
			for(int i=0; i<BUFLN; i++) {
				buf[i] = m_fpga->readio(DUMPMEM+i);
				// if (0 == (i&0x0ff))
					printf("i = %02x / %04x, addr = i + %04x = %08x\n", i, BUFLN, DUMPMEM, i+DUMPMEM);
			}
		}
	} catch(BUSERR err) {
		fprintf(stderr, "Caught a bus ERROR at address 0x%08x\n", err.addr);
		exit(EXIT_FAILURE);
			
	} catch(char *err) {
		fprintf(stderr, "EXCEPTION: %s\n", err);
		exit(EXIT_FAILURE);
	} catch(...) {
		fprintf(stderr, "Caught an unexpected exception\n");
		fprintf(stderr, "Exiting on an unknown error\n");
		exit(EXIT_FAILURE);
	}

	printf("\nREAD-COMPLETE\n");

	// Now, let's find the end
	sz = BUFLN-1;
	while((sz>0)&&(buf[sz] == 0xffffffff))
		sz--;
	sz+=1;
	printf("The size of the buffer is 0x%06x or %d words\n", sz, sz);

	fp = fopen(fname,"w");
	if (fp == NULL) {
		fprintf(stderr, "ERR: Could not write %s\n", fname);
		exit(EXIT_FAILURE);
	}
	fwrite(buf, sizeof(buf[0]), sz, fp);
	fclose(fp);

	delete	m_fpga;
}
