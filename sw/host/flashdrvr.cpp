////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	flashdrvr.cpp
//
// Project:	OpenArty, an entirely open SoC based upon the Arty platform
//
// Purpose:	Flash driver.  Encapsulates the erasing and programming (i.e.
//		writing) necessary to set the values in a flash device.
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
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>

#include "port.h"
#include "regdefs.h"
#include "flashdrvr.h"

static const	int	F_EMPTY = 0,	// (No command)
			F_PP   = 0x002,	// Page program
			F_WRR  = 0x001,	// Write register (status or cfg)
			F_WRDI = 0x003,	// Write disable
			F_READ = 0x003,	// Slow SPI (1-bit) read
			F_RDSR1= 0x005,	// Read status register 1
			F_WREN = 0x006,	// Write Enable
			F_SE   = 0x0d8,	// Sector erase
			F_END  = 0x100; // End cfg access
 
void	FLASHDRVR::flwait(void) {
	const	int	WIP = 1;	// Write in progress bit
	DEVBUS::BUSW	v;

	m_fpga->writeio(R_FLASHCFG, F_END);
	m_fpga->writeio(R_FLASHCFG, F_RDSR1);
	do {
		m_fpga->writeio(R_FLASHCFG, F_EMPTY);
		sr = m_fpga->readio(R_FLASHCFG);
	} while(sr&WIP);
	m_fpga->writeio(R_FLASHCFG, F_END);
}

bool	FLASHDRVR::erase_sector(const unsigned sector, const bool verify_erase) {
	unsigned	flashaddr = sector & 0x0ffffff;

	// Write enable
	m_fpga->writeio(R_FLASHCFG, F_END);
	m_fpga->writeio(R_FLASHCFG, F_WREN);
	m_fpga->writeio(R_FLASHCFG, F_END);

	DEVBUS::BUSW	page[SZPAGEW];

	// printf("EREG before   : %08x\n", m_fpga->readio(R_QSPI_EREG));
	printf("Erasing sector: %08x\n", sector);

	m_fpga->writeio(R_FLASHCFG, F_SE);
	m_fpga->writeio(R_FLASHCFG, (flashaddr>>16)&0x0ff);
	m_fpga->writeio(R_FLASHCFG, (flashaddr>> 8)&0x0ff);
	m_fpga->writeio(R_FLASHCFG, (flashaddr    )&0x0ff);
	m_fpga->writeio(R_FLASHCFG, F_END);

	// Wait for the erase to complete
	flwait();

	// Now, let's verify that we erased the sector properly
	if (verify_erase) {
		for(int i=0; i<NPAGES; i++) {
			m_fpga->readi(sector+i*SZPAGEW, SZPAGEW, page);
			for(int i=0; i<SZPAGEW; i++)
				if (page[i] != 0xffffffff)
					return false;
		}
	}

	return true;
}

bool	FLASHDRVR::write_page(const unsigned addr, const unsigned len,
		const unsigned *data, const bool verify_write) {
	DEVBUS::BUSW	buf[SZPAGEW];
	unsigned	flashaddr = addr & 0x0ffffff;

	assert(len > 0);
	assert(len <= PGLENW);
	assert(PAGEOF(addr)==PAGEOF(addr+len-1));

	if (len <= 0)
		return true;

	// Write enable
	m_fpga->writeio(R_FLASHCFG, F_END);
	m_fpga->writeio(R_FLASHCFG, F_WREN);
	m_fpga->writeio(R_FLASHCFG, F_END);

	// Write the page
	m_fpga->writeio(R_FLASHCFG, F_END);

	// Issue the command
	m_fpga->writeio(R_FLASHCFG, F_PP);
	// The address
	m_fpga->writeio(R_FLASHCFG, (flashaddr>>16)&0x0ff);
	m_fpga->writeio(R_FLASHCFG, (flashaddr>> 8)&0x0ff);
	m_fpga->writeio(R_FLASHCFG, (flashaddr    )&0x0ff);
	// The page data itself
	for(i=0; i<len; i++) {
		m_fpga->writeio(R_FLASHCFG, data[i])
	m_fpga->writeio(R_FLASHCFG, F_END);

	printf("Writing page: 0x%08x - 0x%08x\n", addr, addr+len-1);

	flwait();
	if (verify_write) {
		// printf("Attempting to verify page\n");
		// NOW VERIFY THE PAGE
		m_fpga->readi(addr, len, buf);
		for(int i=0; i<len; i++) {
			if (buf[i] != data[i]) {
				printf("\nVERIFY FAILS[%d]: %08x\n", i, i+addr);
				printf("\t(Flash[%d]) %08x != %08x (Goal[%08x])\n", 
					i, buf[i], data[i], i+addr);
				return false;
			}
		} // printf("\nVerify success\n");
	} return true;
}

bool	FLASHDRVR::write(const unsigned addr, const unsigned len,
		const unsigned *data, const bool verify) {

	// Work through this one sector at a time.
	// If this buffer is equal to the sector value(s), go on
	// If not, erase the sector

	for(unsigned s=SECTOROF(addr); s<SECTOROF(addr+len+SECTORSZW-1);
				s+=SECTORSZW) {
		// printf("IN LOOP, s=%08x\n", s);
		// Do we need to erase?
		bool	need_erase = false;
		unsigned newv = 0; // (s<addr)?addr:s;
		{
			DEVBUS::BUSW	*sbuf = new DEVBUS::BUSW[SECTORSZW];
			const DEVBUS::BUSW *dp;
			unsigned	base,ln;
			base = (addr>s)?addr:s;
			ln=((addr+len>s+SECTORSZW)?(s+SECTORSZW):(addr+len))-base;
			m_fpga->readi(base, ln, sbuf);

			dp = &data[base-addr];
			for(unsigned i=0; i<ln; i++) {
				if ((sbuf[i]&dp[i]) != dp[i]) {
					printf("\nNEED-ERASE @0x%08x ... %08x != %08x (Goal)\n", 
						i+base-addr, sbuf[i], dp[i]);
					need_erase = true;
					newv = i+base;
					break;
				} else if ((sbuf[i] != dp[i])&&(newv == 0)) {
					// if (newv == 0)
						// printf("MEM[%08x] = %08x (!= %08x (Goal))\n",
							// i+base, sbuf[i], dp[i]);
					newv = i+base;
				}
			}
		}

		if (newv == 0)
			continue; // This sector already matches

		// Just erase anyway
		if (!need_erase)
			printf("NO ERASE NEEDED\n");
		else {
			printf("ERASING SECTOR: %08x\n", s);
			if (!erase_sector(s, verify)) {
				printf("SECTOR ERASE FAILED!\n");
				return false;
			} newv = (s<addr) ? addr : s;
		}
		for(unsigned p=newv; (p<s+SECTORSZW)&&(p<addr+len);
					p=PAGEOF(p+PGLENW)) {
			unsigned start = p, len = addr+len-start;

			// BUT! if we cross page boundaries, we need to clip
			// our results to the page boundary
			if (PAGEOF(start+len-1)!=PAGEOF(start))
				len = PAGEOF(start+PGLENW)-start;
			if (!write_page(start, len, &data[p-addr], verify)) {
				printf("WRITE-PAGE FAILED!\n");
				return false;
			}
		}
	}

	m_fpga->writeio(R_FLASHCFG, F_WEN);
	m_fpga->writeio(R_QSPI_EREG, ENABLEWP); // Re-enable write protection

	return true;
}

