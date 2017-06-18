////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	dblpipecmdr.cpp
//
// Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
//
// Purpose:	This program simulates a parallel port peripheral to a
//		ICO Zip processor, one that is used to push data in and
//	pull data out of that CPU.
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
#include <sys/types.h>
#include <sys/socket.h>
#include <poll.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <string.h>

// #define	i_pp_dir
// #define	i_pp_clk
// #define	i_pp_data	io_pp_data
// #define	o_pp_data	io_pp_data

#define	DBLPIPEBUFLEN	256


int	DBLPIPECMDR::setup_listener(const int port) {
	struct	sockaddr_in	my_addr;
	int	skt;

	signal(SIGPIPE, SIG_IGN);

	if (m_debug) printf("Listening on port %d\n", port);

	skt = socket(AF_INET, SOCK_STREAM, 0);
	if (skt < 0) {
		perror("Could not allocate socket: ");
		exit(-1);
	}

	// Set the reuse address option
	{
		int optv = 1, er;
		er = setsockopt(skt, SOL_SOCKET, SO_REUSEADDR, &optv, sizeof(optv));
		if (er != 0) {
			perror("SockOpt Err:");
			exit(-1);
		}
	}

	memset(&my_addr, 0, sizeof(struct sockaddr_in)); // clear structure
	my_addr.sin_family = AF_INET;
	my_addr.sin_addr.s_addr = htonl(INADDR_ANY);
	my_addr.sin_port = htons(port);

	if (bind(skt, (struct sockaddr *)&my_addr, sizeof(my_addr))!=0) {
		perror("BIND FAILED:");
		exit(-1);
	}

	if (listen(skt, 1) != 0) {
		perror("Listen failed:");
		exit(-1);
	}

	return skt;
}

DBLPIPECMDR::DBLPIPECMDR(const int port, const bool copy_to_stdout)
		: m_copy(copy_to_stdout) {
	m_debug = true;
	m_con = m_cmd = -1;
	m_skt = setup_listener(port);
	m_console = setup_listener(port+1);
	m_rxpos = m_cmdpos = m_conpos = m_ilen = 0;
	m_started_flag = false;
	m_pp_phase = 0;
	m_tx_busy   = 0; // Flow control out of the FPGA
	m_intransit_data = 0x0ff;
}

virtual	void	DBLPIPECMDR::kill(void) {
	// Close any active connection
	if (m_con >= 0)	    close(m_con);
	if (m_skt >= 0)     close(m_skt);
	if (m_console >= 0) close(m_console);
	if (m_cmd >= 0)     close(m_cmd);

	m_con     = -1;
	m_skt     = -1;
	m_console = -1;
	m_cmd     = -1;
}

void	DBLPIPECMDR::poll_accept(void) {
	struct	pollfd	pb[2];
	int	npb = 0;

	// Check if we need to accept any connections
	if (m_cmd < 0) {
		pb[npb].fd = m_skt;
		pb[npb].events = POLLIN;
		npb++;
	}

	if (m_con < 0) {
		pb[npb].fd = m_console;
		pb[npb].events = POLLIN;
		npb++;
	}

	if (npb > 0) {
		int	pr;
		pr = poll(pb, npb, 0);

		assert(pr >= 0);

		if (pr > 0) for(int k=0; k<npb; k++) {
			if ((pb[k].revents & POLLIN)==0) {
				// printf("Not #%d\n", k);
				continue;
			}
			if (pb[k].fd == m_skt) {
				m_cmd = accept(m_skt, 0, 0);

				if (m_cmd < 0)
					perror("CMD Accept failed:");
				else printf("Accepted CMD connection\n");
			} else if (pb[k].fd == m_console) {
				m_con = accept(m_console, 0, 0);
				if (m_con < 0)
					perror("CON Accept failed:");
				else printf("Accepted CON connection\n");
			}
		}
	}

	// End of trying to accept more connections
}

void	DBLPIPECMDR::poll_read(void) {
	npb = 0;
	if (m_cmd >= 0) {
		pb[npb].fd = m_cmd;
		pb[npb].events = POLLIN;
		npb++;
	} if (m_con >= 0) {
		pb[npb].fd = m_con;
		pb[npb].events = POLLIN;
		npb++;
	}

	if (npb == 0)
		return;

	r = poll(pb, npb, 0);
	if (r < 0)
		perror("Polling error:");
	else if (r == 0)
		return;

	printf("POLL = %d\n", r);
	for(int i=0; i<npb; i++) {
		if (pb[i].revents & POLLIN) {
			int	nr;
			nr =recv(pb[i].fd, &m_rxbuf[m_ilen],
					sizeof(m_rxbuf)-m_ilen,
					MSG_DONTWAIT);
printf("RCVD: %d bytes\n", nr);
			if (pb[i].fd == m_cmd) {
				for(int j=0; j<nr; j++)
					m_rxbuf[j+m_ilen] |= 0x80;
			} if (nr > 0) {
				m_ilen += nr;
				if (m_ilen == sizeof(m_rxbuf))
					break;
			} else if (nr <= 0) {
				close(pb[i].fd);
				if (pb[i].fd == m_cmd)
					m_cmd = -1;
				else // if (pb[i].fd == m_con)
					m_con = -1;
			}
		}
	} m_rxpos = 0;
}

int DBLPIPECMDR::operator()(int &pp_clk, int &pp_dir, int pp_data, pp_clkfb) {
	struct	pollfd	pb[2];
	int	npb = 0, r;
	bool	stalled;

	poll_accept();

	// The way are comms work is that
	// 1. i_pp_clk = 0 is an idle condition
	// 2. i_pp_clk = 1 is an active condition.  The board is reading
	//    from the pins here, or holding the pins constant so we
	//    can read them.
	// We need to hold the clock in either condition until the board
	// responds that it has seen our clock.  Until then, our
	// interface must be "stalled".  I.e., any time the requested
	// clock and the clock feedback are different ... we are
	// stalled and have to wait.
	stalled = false;


	if (pp_clk != pp_clkfb) {
		if (pp_dir)
			return m_intransit_data;
		else
			return pp_data;
	}


#define	MAX_PP_PHASE	8
#define	PP_TO_FPGA	1
#define	PP_FROM_FPGA	0
	m_pp_phase++;
	if (m_pp_phase >= MAX_PP_PHASE)
		m_pp_phase = 0;

	if (m_pp_phase == 0) {
		// First half ... transmit

		// If our transmit buffer is empty, see if we can
		// fill it.
		if (m_ilen == 0)  
			poll_read();
		if (m_ilen > 0) {
			pp_dir = PP_TO_FPGA;
			pp_clk = 1;
			m_intransit_data = m_rxbuf[m_rxpos++];
if (m_debug) printf("INTRANSIT-DATA: %02x\n", m_intransit_data & 0x0ff);
			m_ilen--;
		} else {
			// Skip transmit, do straight to receive
			pp_dir = PP_FROM_FPGA;
			pp_clk = 1;
			m_pp_phase += (MAX_PP_PHASE/2);
			m_intransit_data = 0x0ff;
		}
	} else if ((m_pp_phase == MAX_PP_PHASE-1)
			&&(pp_data != 0x0ff)) {

		// Second half ... is there anything to be read?
		// If we get here, the answer is: yes.

		// TESTB<VA>::m_core->i_debug = 1;

		if (pp_data & 0x80) {
			m_cmdbuf[m_cmdpos++] = pp_data & 0x7f;
		} else
			m_conbuf[m_conpos++] = pp_data & 0x7f;
		if ((m_cmdpos>0)&&((m_cmdbuf[m_cmdpos-1] == '\n')||(m_cmdpos >= DBLPIPEBUFLEN-2))) {
			int	snt = 0;
			if (m_cmd >= 0)
				snt = send(m_cmd,m_cmdbuf, m_cmdpos, 0);
			if (snt < 0) {
				printf("Closing CMD socket\n");
				close(m_cmd);
				m_cmd = -1;
				snt = 0;
			} // else printf("%d/%d bytes returned\n", snt, m_cmdpos);
			m_cmdbuf[m_cmdpos] = '\0';
			if (m_copy) printf("> %s", m_cmdbuf);
			if (snt < m_cmdpos) {
				fprintf(stderr, "CMD: Only sent %d bytes of %d!\n",
					snt, m_cmdpos);
			}
			m_cmdpos = 0;
		}

		if ((m_conpos>0)&&((m_conbuf[m_conpos-1] == '\n')||(m_conpos >= DBLPIPEBUFLEN-2))) {
			int	snt = 0;
			if (m_con >= 0) {
				snt = send(m_con,m_conbuf, m_conpos, 0);
				if (snt < 0) {
					printf("Closing CONsole socket\n");
					close(m_con);
					m_con = -1;
					snt = 0;
				}
				if (snt < m_conpos) {
					fprintf(stderr, "CON: Only sent %d bytes of %d!\n",
						snt, m_conpos);
				}
			}
			m_conbuf[m_conpos] = '\0';
			printf("%s", m_conbuf);
			m_conpos = 0;
		} // else { m_conbuf[m_conpos] = '\0'; printf("B: %s\n", m_conbuf); }
	} // else TESTB<VA>::m_core->i_debug = 0;


	// Now that we know what we want to do, let's set our I/O values
	pp_dir = ((m_pp_phase<<1)&(MAX_PP_PHASE))?0:1;
	pp_clk = ((m_pp_phase<<2)&(MAX_PP_PHASE))?1:0;
	if ((m_debug)&&((m_intransit_data&0x0ff) != 0x0ff))
		printf("TICK:IN-TRANSIT: %02x [%c]\n",
			m_intransit_data & 0x0ff,
			(isgraph(m_intransit_data&0x7f))
			?(m_intransit_data&0x7f):'.');

	return m_intransit_data;
}

