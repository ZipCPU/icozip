////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sramsim.h
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU core
//
// Purpose:	This file contains the simulation interface for an SRAM found
// 		on the ICO board.
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
#ifndef	SRAMSIM_H
#define	SRAMSIM_H

class	SRAMSIM {
public:	
	typedef	unsigned int	BUSW;
	typedef	unsigned char	uchar;

	BUSW	*m_mem, m_len, m_mask;
	int	m_nxt_ack;
	BUSW	m_nxt_data;
	static	const	bool	m_debug;
	

	SRAMSIM(const unsigned int nwords);
	~SRAMSIM(void);
	void	load(const char *fname);
	void	load(const unsigned addr, const char *buf,const unsigned len);
	BUSW	apply(const uchar ce_n, const uchar oe_n, const uchar we_n,
			const BUSW addr, const BUSW data, const BUSW sel);
	BUSW	operator()(const uchar ce_n, const uchar oe_n, const uchar we_n,
			const BUSW addr, const BUSW data, const BUSW sel) {
		return apply(ce_n, oe_n, we_n, addr, data, sel);
	}
	BUSW &operator[](const BUSW addr) { return m_mem[addr&m_mask]; }
};

#endif
