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
#include <assert.h>

#include "port.h"
#include "pportsim.h"

// #define	i_pp_dir
// #define	i_pp_clk
// #define	i_pp_data	io_pp_data
// #define	o_pp_data	io_pp_data

#define	PP_TO_FPGA	1
#define	PP_FROM_FPGA	0

#define	DBLPIPEBUFLEN	256


int	PPORTSIM::setup_listener(const int port) {
	struct	sockaddr_in	my_addr;
	int	skt;

	signal(SIGPIPE, SIG_IGN);

	if (m_debug) printf("Listening on port %d\n", port);

	skt = socket(AF_INET, SOCK_STREAM, 0);
	if (skt < 0) {
		perror("ERR: Could not allocate socket: ");
		exit(EXIT_FAILURE);
	}

	// Set the reuse address option
	{
		int optv = 1, er;
		er = setsockopt(skt, SOL_SOCKET, SO_REUSEADDR, &optv, sizeof(optv));
		if (er != 0) {
			perror("ERR: SockOpt Err:");
			exit(EXIT_FAILURE);
		}
	}

	memset(&my_addr, 0, sizeof(struct sockaddr_in)); // clear structure
	my_addr.sin_family = AF_INET;
	my_addr.sin_addr.s_addr = htonl(INADDR_ANY);
	my_addr.sin_port = htons(port);

	if (bind(skt, (struct sockaddr *)&my_addr, sizeof(my_addr))!=0) {
		perror("ERR: BIND FAILED:");
		exit(EXIT_FAILURE);
	}

	if (listen(skt, 1) != 0) {
		perror("ERR: Listen failed:");
		exit(EXIT_FAILURE);
	}

	return skt;
}

PPORTSIM::PPORTSIM(const int port, const bool copy_to_stdout)
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

void	PPORTSIM::kill(void) {
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

void	PPORTSIM::poll_accept(void) {
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

void	PPORTSIM::poll_read(void) {
	struct	pollfd	pb[2];
	int		npb = 0, r;

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
				for(int j=0; j<nr; j++) {
					m_cmdline[m_cllen] = m_rxbuf[j+m_ilen];
					if (m_cmdline[m_cllen] != '\r') {
						if (m_cmdline[m_cllen] == '\n'){
							m_cmdline[m_cllen]='\0';
							printf("< %s\n", m_cmdline);
							m_cllen=0;
						} else
							m_cllen++;
					} if (m_cllen >= 64) {
						m_cmdline[m_cllen+1] = '\0';
						printf("< %s\n", m_cmdline);
						m_cllen = 0;
					}
					
					m_rxbuf[j+m_ilen] |= 0x80;
				} m_cmdline[m_cllen] = '\0';


				if (nr <= 0) {
					m_cmdline[m_cllen] = '\0';
					printf("< %s [CLOSED]\n", m_cmdline);
					m_cllen = 0;
				}
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

void	PPORTSIM::received(const char ch) {
	if (ch & 0x80) {
		m_cmdbuf[m_cmdpos++] = ch & 0x7f;
	} else
		m_conbuf[m_conpos++] = ch & 0x7f;
	if ((m_cmdpos>0)&&((m_cmdbuf[m_cmdpos-1] == '\n')
				||(m_cmdpos >= PPORTSIMBUFLEN-2))) {
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
	} if ((m_conpos>0)&&((m_conbuf[m_conpos-1] == '\n')
				||(m_conpos >= PPORTSIMBUFLEN-2))) {
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
	}
}

int	PPORTSIM::next(void) {
	// If our transmit buffer is empty, see if we can
	// fill it.
	if (m_ilen == 0)
		poll_read();
	if (m_ilen <= 0)
		return -1;

	int	nval;
	nval = m_rxbuf[m_rxpos++];
	m_ilen--;

	return nval & 0x0ff;
}

int	PPORTSIM::operator()(int &pp_clk, int &pp_dir, int pp_data, int pp_clkfb) {
	int	r;

	if (pp_dir == PP_TO_FPGA)
		r = m_intransit_data;
	else // else coming from the FPGA ... don't change it
		r = pp_data;

	// The way these comms work is that
	// 1. i_pp_clk = 0 is an idle condition
	// 2. i_pp_clk = 1 is an active condition.  The board is reading
	//    from the pins here, or holding the pins constant so we
	//    can read them.
	// We need to hold the clock in either condition until the board
	// responds that it has seen our clock.  

	if (pp_clk != pp_clkfb)
		return r;

	if (pp_clk) {
		pp_clk = 0;

		// Check if we just read something
		if ((pp_dir == PP_FROM_FPGA)&&(pp_data != 0x0ff))
			received(pp_data);

		return r;
	}

	if (pp_dir != PP_TO_FPGA) {
		// Check if we want to send something
		int	vl;
		vl = next();
		if (vl >= 0) {
			m_intransit_data = vl&0x0ff;
			pp_dir = PP_TO_FPGA;
			pp_clk = 1;
			return m_intransit_data;
		}
	}

	poll_accept();

	// Otherwise, let's run a cycle and see if the FPGA has anything to
	// send to us.
	pp_clk = 1;
	pp_dir = PP_FROM_FPGA;

	return pp_data;
}
