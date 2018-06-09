////////////////////////////////////////////////////////////////////////////////
//
// Filename:	netpport.cpp
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
// Copyright (C) 2017, Gisselquist Technology, LLC
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
#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>
#include <termios.h>
#include <assert.h>
#include <vector>
#include <string.h>
#include <ctype.h>
#include <errno.h>

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <poll.h>
#include <signal.h>

#include <sched.h>


bool verbose = false;

#  include <wiringPi.h>

//
// For reference, here are four valuable definitions found within wiringPi.h
//
// #define	LOW	0
// #define	HIGH	1
// #define	INPUT	0
// #define	OUTPUT	1

//
// RPi GPIO #, connector pin #, schematic name, fpga pin #
//
#  define RASPI_D8   0 // PIN 11, GPIO.0,  IO219,       D5
#  define RASPI_D7   1 // PIN 12, GPIO.1,  IO212,       D6
#  define RASPI_D6   3 // PIN 15, GPIO.3,  IO209,       C6
#  define RASPI_D5   4 // PIN 16, GPIO.4,  IO206,       C7
#  define RASPI_D4  12 // PIN 19, MOSI,    RPI_SPI_MOSI,A6
#  define RASPI_D3  13 // PIN 21, MISO,    RPI_SPI_MISO,A7
#  define RASPI_D2  11 // PIN 26, CE1,     IO224,       D4
#  define RASPI_D1  24 // PIN 35, GPIO.24, IO210,       D7
#  define RASPI_D0  27 // PIN 36, GPIO.27, IO193,       D9
#  define RASPI_DIR 28 // PIN 38, GPIO.28, IO191,       C9
#  define RASPI_CLK 29 // PIN 40, GPIO.29, IO185,       C10
#  define RASPI_CLKFB  RASPI_D8

#define	READ_FROM_ICO	0
#define	WRITE_TO_ICO	1

class	MUXDCOMMS {
private:
	char		*m_rd_buf;
	unsigned	m_rd_pos;
	unsigned	m_rd_fill;
	unsigned	m_rd_size;

// #define	PAUSE	sched_yield()
#define	PAUSE

	unsigned	pp_xfer(unsigned nbytes, const char *data, char *rdbuf){
		unsigned	nr = 0;

		for(unsigned i=0; i<nbytes; i++) {
			char	datab = data[i];

			digitalWrite(RASPI_DIR, OUTPUT);
			digitalWrite(RASPI_CLK, 0);
			//
			while(digitalRead(RASPI_CLKFB) != 0)
				PAUSE;
			pinMode(RASPI_D7, OUTPUT);
			pinMode(RASPI_D6, OUTPUT);
			pinMode(RASPI_D5, OUTPUT);
			pinMode(RASPI_D4, OUTPUT);
			pinMode(RASPI_D3, OUTPUT);
			pinMode(RASPI_D2, OUTPUT);
			pinMode(RASPI_D1, OUTPUT);
			pinMode(RASPI_D0, OUTPUT);

			digitalWrite(RASPI_D7, (datab & 0x80) ? 1:0);
			digitalWrite(RASPI_D6, (datab & 0x40) ? 1:0);
			digitalWrite(RASPI_D5, (datab & 0x20) ? 1:0);
			digitalWrite(RASPI_D4, (datab & 0x10) ? 1:0);
			digitalWrite(RASPI_D3, (datab & 0x08) ? 1:0);
			digitalWrite(RASPI_D2, (datab & 0x04) ? 1:0);
			digitalWrite(RASPI_D1, (datab & 0x02) ? 1:0);
			digitalWrite(RASPI_D0, (datab & 0x01) ? 1:0);

			digitalWrite(RASPI_CLK, 1);
			while(digitalRead(RASPI_CLK) != 1)
				PAUSE;
			while(digitalRead(RASPI_CLKFB) == 0)
				PAUSE;

			pinMode(RASPI_D7, INPUT);
			pinMode(RASPI_D6, INPUT);
			pinMode(RASPI_D5, INPUT);
			pinMode(RASPI_D4, INPUT);
			pinMode(RASPI_D3, INPUT);
			pinMode(RASPI_D2, INPUT);
			pinMode(RASPI_D1, INPUT);
			pinMode(RASPI_D0, INPUT);

			digitalWrite(RASPI_DIR, INPUT);
			digitalWrite(RASPI_CLK, 0);
			while(digitalRead(RASPI_CLKFB) != 0)
				PAUSE;
			digitalWrite(RASPI_CLK, 1);
			while(digitalRead(RASPI_CLKFB) != 1)
				PAUSE;

			datab = 0;
			if (digitalRead(RASPI_D7))	datab |= 0x80;
			if (digitalRead(RASPI_D6))	datab |= 0x40;
			if (digitalRead(RASPI_D5))	datab |= 0x20;
			if (digitalRead(RASPI_D4))	datab |= 0x10;
			if (digitalRead(RASPI_D3))	datab |= 0x08;
			if (digitalRead(RASPI_D2))	datab |= 0x04;
			if (digitalRead(RASPI_D1))	datab |= 0x02;
			if (digitalRead(RASPI_D0))	datab |= 0x01;

			if (datab != 0x0ff)
				rdbuf[nr++] = datab;
		}
		digitalWrite(RASPI_DIR, INPUT);
		digitalWrite(RASPI_CLK, 0);

		return nr;
	}


	unsigned	pp_read(unsigned nbytes, char *data) {
		unsigned	nr = 0;

		digitalWrite(RASPI_CLK, 0);
		pinMode(RASPI_D7, INPUT);
		pinMode(RASPI_D6, INPUT);
		pinMode(RASPI_D5, INPUT);
		pinMode(RASPI_D4, INPUT);
		pinMode(RASPI_D3, INPUT);
		pinMode(RASPI_D2, INPUT);
		pinMode(RASPI_D1, INPUT);
		pinMode(RASPI_D0, INPUT);
		digitalWrite(RASPI_DIR, INPUT);
		while(digitalRead(RASPI_DIR) != INPUT)
			PAUSE;

		for(unsigned i=0; i<nbytes; i++) {
			char	datab = 0;

			while(digitalRead(RASPI_CLKFB) != 0)
				PAUSE;
			digitalWrite(RASPI_CLK, 1);
			while(digitalRead(RASPI_CLK) == 0)
				PAUSE;
			while(digitalRead(RASPI_CLKFB) == 0)
				PAUSE;

			if (digitalRead(RASPI_D7))	datab |= 0x80;
			if (digitalRead(RASPI_D6))	datab |= 0x40;
			if (digitalRead(RASPI_D5))	datab |= 0x20;
			if (digitalRead(RASPI_D4))	datab |= 0x10;
			if (digitalRead(RASPI_D3))	datab |= 0x08;
			if (digitalRead(RASPI_D2))	datab |= 0x04;
			if (digitalRead(RASPI_D1))	datab |= 0x02;
			if (digitalRead(RASPI_D0))	datab |= 0x01;

			digitalWrite(RASPI_CLK, 0);
			while(digitalRead(RASPI_CLK) != 0)
				PAUSE;

			if (datab == 0x0ff)
				break;
			data[nr++] = datab;
		}

		return nr;
	}

	bool	pp_idle(void) {
		if ( digitalRead(RASPI_CLK))	return false;
		if ( digitalRead(RASPI_CLKFB))	return false;
		if (!digitalRead(RASPI_D7))	return false;
		if (!digitalRead(RASPI_D6))	return false;
		if (!digitalRead(RASPI_D5))	return false;
		if (!digitalRead(RASPI_D4))	return false;
		if (!digitalRead(RASPI_D3))	return false;
		if (!digitalRead(RASPI_D2))	return false;
		if (!digitalRead(RASPI_D1))	return false;
		if (!digitalRead(RASPI_D0))	return false;
		return true;
	}

	void	pp_dump(void) {
		unsigned	datab = 0, clk=0, clkfb=0, dir=0;

		dir   = digitalRead(RASPI_DIR);
		clk   = digitalRead(RASPI_CLK);
		clkfb = digitalRead(RASPI_CLKFB);

		if (digitalRead(RASPI_D7))	datab |= 0x80;
		if (digitalRead(RASPI_D6))	datab |= 0x40;
		if (digitalRead(RASPI_D5))	datab |= 0x20;
		if (digitalRead(RASPI_D4))	datab |= 0x10;
		if (digitalRead(RASPI_D3))	datab |= 0x08;
		if (digitalRead(RASPI_D2))	datab |= 0x04;
		if (digitalRead(RASPI_D1))	datab |= 0x02;
		if (digitalRead(RASPI_D0))	datab |= 0x01;


		printf("%s %s/%s %02x\n",
			(dir)?"OUT":" IN",
			(clk)?"CLK":" ( )",
			(clkfb)?"FB":" ()",
			datab & 0x0ff);
	}

	void	pp_init(void) {
		// Initialize the wiringPi library
		wiringPiSetup();

		// Comms take place over 8 bidirectional data bits, a clock,
		// and a direction bit

		pinMode(RASPI_DIR, OUTPUT);
		digitalWrite(RASPI_DIR, OUTPUT);
		pinMode(RASPI_CLK, OUTPUT);
		digitalWrite(RASPI_CLK, 0);
		pinMode(RASPI_CLKFB, INPUT);
		pinMode(RASPI_D7,    INPUT);
		pinMode(RASPI_D6,    INPUT);
		pinMode(RASPI_D5,    INPUT);
		pinMode(RASPI_D4,    INPUT);
		pinMode(RASPI_D3,    INPUT);
		pinMode(RASPI_D2,    INPUT);
		pinMode(RASPI_D1,    INPUT);
		pinMode(RASPI_D0,    INPUT);
		digitalWrite(RASPI_DIR, INPUT);
	}

public:
	MUXDCOMMS(void) {
		m_rd_size = 8192;
		m_rd_buf = new char[m_rd_size];
		m_rd_fill = 0;
		m_rd_pos  = 0;
		pp_init();
	}

	unsigned	read(unsigned nreq, char *buf) {
		unsigned	nr = 0;

		if (m_rd_fill > 0) {
			unsigned ln = nreq;
			if (ln > m_rd_fill)
				ln = m_rd_fill;
			memcpy(&buf[nr], &m_rd_buf[m_rd_pos], ln);
			m_rd_pos  += ln;
			m_rd_fill -= ln;
			if (m_rd_fill == 0)
				m_rd_pos = 0;
			nr += ln;
		}

		if (nr < nreq)
			nr += pp_read(nreq - nr, &buf[nr]);

		return nr;
	}

	void	write(unsigned nreq, char *buf) {
		unsigned	nr;

		if (nreq > m_rd_size - m_rd_fill - m_rd_pos) {
			if (m_rd_pos > 0) {
				memmove(m_rd_buf, &m_rd_buf[m_rd_pos], m_rd_fill);
				m_rd_pos = 0;
			}
			if (nreq > m_rd_size - m_rd_fill) {
				unsigned	newsz;
				char		*alt;

				newsz = m_rd_size;
				while(newsz < m_rd_fill + nreq)
					newsz <<= 1;

				alt = new char[newsz];
				memcpy(alt, m_rd_buf, m_rd_fill);
				delete m_rd_buf;
				m_rd_buf = alt;
			}
		}

		nr = pp_xfer(nreq, buf, &m_rd_buf[m_rd_pos]);
		m_rd_fill += nr;
	}

	bool	is_idle(void) { return pp_idle(); }
	void	dump(void) { pp_dump(); }
};

#include "port.h"
#define	NO_WAITING	0
#define	FOREVER		-1
#define	SHORTWHILE	1
#define	LONGWHILE	20

int	setup_listener(const int port) {
	int	skt;
	struct  sockaddr_in     my_addr;

	printf("Listening on port %d\n", port);

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

class	LINBUFS {
public:
	char	m_iline[512], m_oline[512];
	char	m_buf[256];
	int	m_ilen, m_olen;
	int	m_fd;
	bool	m_connected;
	MUXDCOMMS	*m_pport;

	LINBUFS(MUXDCOMMS *pport) {
		m_ilen = 0; m_olen = 0; m_connected = false; m_fd = -1;
		m_pport = pport;
	}

	void	close(void) {
		if (!m_connected) {
			m_fd = -1;
			return;
		} if (m_fd < 0) {
			m_connected = false;
			return;
		}
		::close(m_fd);
		m_fd = -1;
		m_connected = false;
	}

	int	read(void) {
		if (!m_connected)
			return 0;
		else
			return ::read(m_fd, m_buf, sizeof(m_buf));
	}

	void	accept(const int skt) {
		m_fd = ::accept(skt, 0, 0);
		if (m_fd < 0) {
			perror("CMD Accept failed!  O/S Err:");
			exit(EXIT_FAILURE);
		} m_connected = (m_fd >= 0);
	}

	void	pp_write(int ln, int mask = 0) {
		if (mask) {
			for(int i=0; i<ln; i++)
				m_buf[i] |= mask;
		}

		if (ln > 0)
			m_pport->write((unsigned)ln, m_buf);
	}

	int	write(int fd, int ln, int mask = 0) {
		int	pos = 0, nw;

		if (mask) {
			for(int i=0; i<ln; i++)
				m_buf[i] |= mask;
		}

		do {
			nw = ::write(fd, &m_buf[pos], ln-pos);

			if ((nw < 0)&&(errno == EAGAIN)) {
				nw = 0;
				usleep(10);
			} else if (nw < 0) {
				fprintf(stderr, "ERR: %4d\n", errno);
				perror("O/S Err: ");
				exit(EXIT_FAILURE);
				break;
			} else if (nw == 0) {
				// TTY(i.e. FPGA) dev has closed our connection
				fprintf(stderr, "Device has closed\n");
				exit(EXIT_SUCCESS);
				break;
			}
			pos += nw;
		} while(pos < ln);

		return pos;
	}

	void	print_in(FILE *fp, int ln, const char *prefix = NULL) {
		// lbcmd.print_in(ncmd, (lbcmd.m_fd>=0)?"> ":"# ");
		assert(ln > 0);
		for(int i=0; i<ln; i++) {
			m_iline[m_ilen++] = m_buf[i];
			// printf("CH[%02x] = %c\n", m_buf[i], isgraph(m_buf[i])?m_buf[i]:'.');
			bool	nl, fullline;
			nl = (m_iline[m_ilen-1] == '\n');
			nl=(nl)||(m_iline[m_ilen-1] == '\r');

			fullline = ((unsigned)m_ilen >= sizeof(m_iline)-1);

			if ((nl)||(fullline)) {
				m_iline[m_ilen] = '\0';
				fprintf(fp, "%s%s%s", // i, m_ilen,
					(prefix)?prefix:"", m_iline, (!nl)?"\n":"");
				m_ilen = 0;
			}
		}
	}

	void	print_out(FILE *fp, int ln, const char *prefix = NULL) {
		for(int i=0; i<ln; i++) {
			m_oline[m_olen++] = m_buf[i] & 0x07f;
			assert(m_buf[i] != '\0');
			if ((m_oline[m_olen-1]=='\n')
					||(m_oline[m_olen-1]=='\r')
					||((unsigned)m_olen
						>= sizeof(m_oline)-1)) {
				if ((unsigned)m_olen >= sizeof(m_oline)-1)
					m_oline[m_olen] = '\0';
				else
					m_oline[m_olen-1] = '\0';
				if (m_olen > 1)
					fprintf(fp,"%s%s\n",
						(prefix)?prefix:"", m_oline);
				m_olen = 0;
			}
		}
	}

	void	flush_out(FILE *fp, const char *prefix = NULL) {
		if(m_olen > 0) {
			m_oline[m_olen] = '\0';
			fprintf(fp, "%s%s\n", (prefix)?prefix:"", m_oline);
			m_olen = 0;
		}
	}
};


int main(int argc, char **argv)
{
	bool	last_busy = false;

	// First, set ourselves up to listen on a variety of network ports
	int	skt = setup_listener(FPGAPORT),
		console = setup_listener(FPGAPORT+1);
		// configuration socket = setup_listener(FPGAPORT+2); ??
	bool	done = false;

	MUXDCOMMS	*pport = new MUXDCOMMS();

	LINBUFS	lbcmd(pport), lbcon(pport);
	while(!done) {
		struct	pollfd	p[4];
		int	pv, nfds;

		//
		// Set up a poll to see if we have any events to examine
		//
		nfds = 0;

		if (lbcmd.m_connected) {
			p[nfds].fd = lbcmd.m_fd;
			p[nfds].events = POLLIN | POLLRDHUP | POLLERR;
			nfds++;
		} else {
			p[nfds].fd = skt;
			p[nfds].events = POLLIN | POLLERR;
			nfds++;
		}

		if (lbcon.m_connected) {
			p[nfds].fd = lbcon.m_fd;
			p[nfds].events = POLLIN | POLLRDHUP | POLLERR;
			nfds++;
		} else {
			p[nfds].fd = console;
			p[nfds].events = POLLIN | POLLERR;
			nfds++;
		}

		int	wait_time;

		if (!pport->is_idle()) {
			wait_time = NO_WAITING;
		} else if (last_busy) {
			wait_time = SHORTWHILE;
		} else
			wait_time = LONGWHILE;
		
		if ((pv=poll(p, nfds, wait_time)) < 0) {
			perror("Poll Failed!  O/S Err:");
			exit(-1);
		}

		last_busy  = false;

		//
		//
		// Now we evaluate what just happened
		//
		//

		// Start by flushing everything on the TTY channel
		unsigned	nr;
		char	rawbuf[256];
		nr = pport->read(sizeof(rawbuf), rawbuf);
		if (nr > 0) {
			unsigned iterations = 0;
			last_busy  = (nr == sizeof(rawbuf));
			while((nr > 0)&&(iterations++ < 16)) {
				int	ncmd = 0, ncon = 0;
				for(unsigned i=0; i<nr; i++) {
					if (rawbuf[i] & 0x80)
						lbcmd.m_buf[ncmd++] = rawbuf[i] & 0x07f;
					else
						lbcon.m_buf[ncon++] = rawbuf[i];
				}

				/* printf("NR = %3d, NCMD = %3d, NCON = %3d", nr, ncmd, ncon);
				printf(": %02x:%02x:%02x...\n",
					lbcon.m_buf[0], lbcon.m_buf[1],
					lbcon.m_buf[2]);
				*/
				if ((lbcmd.m_fd >= 0)&&(ncmd>0)) {
					int	nw;
					nw = lbcmd.write(lbcmd.m_fd, ncmd);
					if(nw != ncmd) {
					// This fails when the other end resets
					// the connection.  Thus, we'll just
					// kindly close the connection and skip
					// the assert that once was at the end.
					lbcmd.close();
					}
				}

				if ((lbcon.m_fd >= 0)&&(ncon>0)) {
					int	nw;
					nw = lbcon.write(lbcon.m_fd, ncon);
					if(nw != ncon) {
					// This fails when the other end resets
					// the connection.  Thus, we'll just
					// kindly close the connection and skip
					// the assert that once was at the end.
					lbcon.close();
					}
				}

				if (ncmd > 0)
					lbcmd.print_in(stdout, ncmd, (lbcmd.m_fd>=0)?"> ":"# ");
				if (ncon > 0)
					lbcon.print_in(stdout, ncon, (lbcon.m_fd >= 0)?") ":". ");

				nr = pport->read(sizeof(rawbuf), rawbuf);
			}
		}

		if (p[0].revents & POLLIN) {
			if (p[0].fd == skt) {
				lbcmd.accept(skt);
				if (lbcmd.m_connected)
					printf("Command port is now connected\n");
			} else { // p[0].fd == lbcmd.m_fd
				int nr = lbcmd.read();
				if (nr == 0) {
					lbcmd.flush_out(stdout, "< ");
					// printf("Disconnect\n");
					lbcmd.close();
					pport->dump();
					printf("Command port disconnect\n");
				} else if (nr > 0) {
					// printf("%d read from SKT\n", nr);
					lbcmd.pp_write(nr, 0x80);
					last_busy = true;
					lbcmd.print_out(stdout, nr, "< ");
				}
			}
		}

		if (p[1].revents & POLLIN) {
			if (p[1].fd == console) {
				lbcon.accept(console);
				if (lbcon.m_connected)
					printf("Console port is now connected\n");
			} else { // p[1].fd == lbcon.m_fd
				int nr = lbcon.read();
				if (nr == 0) {
					lbcon.flush_out(stdout);
					lbcon.close();
					pport->dump();
					printf("Console port closed\n");
				} else if (nr > 0) {
					lbcon.pp_write(nr, 0x0);
					last_busy = true;
					lbcon.print_out(stdout, nr, "( ");
				}
			}
		}
	}

	printf("Closing our sockets\n");
	close(console);
	close(skt);
	return 0;
}
