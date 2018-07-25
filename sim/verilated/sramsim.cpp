////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sramsim.cpp
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU core
//
// Purpose:	This file implements a simulation of the SRAM found on the
// 		ICO board.
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
// with this program.  (It's in the $(ROOT)/doc directory, run make with no
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
#include <assert.h>
#include <string.h>
#include <stdint.h>
#include "byteswap.h"
#include "sramsim.h"

SRAMSIM::SRAMSIM(const unsigned int nwords) {
	unsigned int	nxt;

	for(nxt=1; nxt < nwords; nxt<<=1)
		;
	m_len = nxt; m_mask = nxt-1;
	m_mem = new BUSW[m_len];
	m_nxt_ack = 0;
}

SRAMSIM::~SRAMSIM(void) {
	delete[]	m_mem;
}

void	SRAMSIM::load(const char *fname) {
	FILE	*fp;
	unsigned int	nr;

	fp = fopen(fname, "r");
	if (!fp) {
		fprintf(stderr, "Could not open/load file \'%s\'\n",
			fname);
		perror("O/S Err:");
		fprintf(stderr, "\tInitializing memory with zero instead.\n");
		nr = 0;
	} else {
		nr = fread(m_mem, sizeof(BUSW), m_len, fp);
		fclose(fp);

		if (nr != m_len) {
			fprintf(stderr, "Only read %d of %d words\n",
				nr, m_len);
			fprintf(stderr, "\tFilling the rest with zero.\n");
		}
	}

	for(; nr<m_len; nr++)
		m_mem[nr] = 0l;
}

void	SRAMSIM::load(const unsigned addr, const char *buf, const unsigned len) {
	memcpy(&m_mem[addr], buf, len);
	byteswapbuf((len>>2), &m_mem[addr]);
}

SRAMSIM::BUSW SRAMSIM::apply(const uchar ce_n, const uchar oe_n, const uchar we_n,
			const unsigned addr, const unsigned data,
			const unsigned sel) {
	unsigned	selmsk = 0;
	unsigned	lcladdr, lcldata;

	if (ce_n)
		return rand();

	if (sel&0x2)
		selmsk |= 0x00000ff00;
	if (sel&0x1)
		selmsk |= 0x0000000ff;

	lcldata = data;
	if ((addr&1)==0) {
		selmsk <<= 16;
		lcldata = data << 16;
	} lcladdr = addr >> 1;

	if (!we_n) {
		printf("SRAM WR[%04x] = %04x ", addr, data);
		m_mem[lcladdr & m_mask] = (m_mem[lcladdr&m_mask]&(~selmsk))
				|(lcldata&selmsk);
		printf(" ([%05x] = %08x), sel=%08x\n",
					lcladdr & m_mask, lcldata, selmsk);
		// assert(oe_n);
		return data;
	} else {
		assert(!oe_n);
		unsigned	result = m_mem[lcladdr & m_mask];
		printf("SRAM RD[%08x] = %08x ", lcladdr & m_mask, result);
		if ((addr&1)==0)
			result >>= 16;
		printf(" (%08x -> %04x)\n", addr, result);
		return result;
	}
}


