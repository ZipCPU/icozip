////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	pportsim.h
//
// Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
//
// Purpose:	This class implements a simulation of the parallel port, as it
//		has been used within this project.  Specific pieces include:
//
//	1. A clock line
//	2. A direction line
//	3. 8 data lines
//	4. and a clock feedback line
//
//	It accepts/handles two channels:
//
//	1. A command channel.  Bytes to and from the FPGA using the command
//		channel will have their high bit set.  This channel may be
//		communicated with using TCP/IP at the FPGAPORT given in port.h.
//
//	2. A consol channel.  This channel has the high bit cleared.  As with
//		the command channel, this one can also be communicated with,
//		but this time over TCP/IP port FPGAPORT+1.
//
//	Put together, the interface is designed to create a simulated stream
//	port, such as  UART or TCP/IP sim might create.
//
//	This simple test facility is thus designed to verify that the IP
//	core that uses it works prior to such actual hardware implementation,
//	or alternatively to help debug a core after hardware implementation.
//
//	This simulation class differs from the pipecmdr class I've built
//	elsewhere, in that 1) it creates creating two channels that share
//	the same bus: a command and a console channel, and 2) this version
//	doesn't use inheritance.  
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
#ifndef	PPORTSIM_H
#define	PPORTSIM_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <poll.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <signal.h>

#include "port.h"

// #define	i_pp_dir
// #define	i_pp_clk
// #define	i_pp_data	io_pp_data
// #define	o_pp_data	io_pp_data

#define	PPORTSIMBUFLEN	256

class	PPORTSIM {
	bool	m_debug;

	// setup_listener is an attempt to encapsulate all of the network
	// related setup stuff.
	//
	int	setup_listener(const int port);
public:
	// The file descriptors:
	int	m_skt,	// Commands come in on this socket
		m_console, // Console port comes in/out on this socket
		m_cmd,	// Connection to the command port FD
		m_con;	// Connection to the console port FD
	char	m_conbuf[PPORTSIMBUFLEN],
		m_cmdbuf[PPORTSIMBUFLEN],
		m_rxbuf[PPORTSIMBUFLEN],
		m_cmdline[PPORTSIMBUFLEN],
		m_intransit_data;
	int	m_ilen, m_rxpos, m_cmdpos, m_conpos, m_tx_busy, m_cllen,
		m_pp_phase;
	bool	m_started_flag;
	bool	m_copy;

		void	poll_accept(void);
		void	poll_read(void);
public:

	PPORTSIM(const int port = FPGAPORT, const bool copy_to_stdout=true);
	virtual	void	kill(void);

	// The operator() function is called on every tick.  The input is the
	// the output txuart transmit wire from the device.  The output is to
	// be connected to the the rxuart receive wire into the device.  This
	// makes hookup and operation very simple.
	//
	// This is the most appropriate simulation entry function if the 
	// setup register will never change.
	//
	int	operator()(int &, int&, int, int);
	void	debug(const bool dbg) { m_debug = dbg; }

	// Having just received a character, report it as received
	void	received(const char ch);
	//
	// Get the next character to transmit (if any)
	int	next(void);
};

#endif
