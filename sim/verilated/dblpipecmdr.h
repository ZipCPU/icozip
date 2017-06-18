////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	dblpipecmdr.h
//
// Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
//
// Purpose:	This program attaches to a Verilated Verilog IP core.
//		It will not work apart from such a core.  Once attached,
//	it connects the simulated core to a controller via a TCP/IP pipe
//	interface designed to act like a UART.  This simple test facility
//	is thus designed to verify that the IP core that uses it works prior 
//	to such actual hardware implementation, or alternatively to help
//	debug a core after hardware implementation.
//
//	This extends the pipecmdr approach by creating two channels that share
//	the same bus: a command and a console channel.  The command channel
//	communicates with the 8'th bit set, allowing us to distinguish between
//	the two.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2017, Gisselquist Technology, LLC
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
#ifndef	DBLPIPECMDR_H
#define	DBLPIPECMDR_H

#include <sys/types.h>
#include <sys/socket.h>
#include <poll.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <string.h>

#include "testb.h"

// #define	i_pp_dir
// #define	i_pp_clk
// #define	i_pp_data	io_pp_data
// #define	o_pp_data	io_pp_data

#define	DBLPIPEBUFLEN	256

class	DBLPIPECMDR {
	bool	m_debug;

	int	setup_listener(const int port);
public:
	int	m_skt,	// Commands come in on this socket
		m_console,	// UART comes in/out on this socket
		m_cmd,	// Connection to the command port FD
		m_con;	// Connection to the console port FD
	char	m_conbuf[DBLPIPEBUFLEN],
		m_cmdbuf[DBLPIPEBUFLEN],
		m_rxbuf[DBLPIPEBUFLEN],
		m_intransit_data;
	int	m_ilen, m_rxpos, m_cmdpos, m_conpos, m_tx_busy,
		m_pp_phase;
	bool	m_started_flag;
	bool	m_copy;

	DBLPIPECMDR(const int port = FPGAPORT, const bool copy_to_stdout=true);
	virtual	void	kill(void);
		void	poll_accept(void);
		void	poll_read(void);

	int	operator()(int &, int&, int, int);
	void	debug(const bool dbg) { m_debug = dbg; }
};

#endif
