////////////////////////////////////////////////////////////////////////////////
//
// Filename:	pptest.cpp
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
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>
#include <assert.h>

#include <ctype.h>
#include <assert.h>
#include <errno.h>

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

unsigned	pp_xfer(unsigned nbytes, char *data) {
	unsigned	nr = 0;


	// digitalWrite(RASPI_CLK, OUTPUT);
	// digitalWrite(RASPI_DIR, OUTPUT);
	// digitalWrite(RASPI_CLK, 0);

	for(unsigned i=0; i<nbytes; i++) {
		char	datab = data[i];

		// digitalWrite(RASPI_D8, (v & 0x100) ? 1:0);
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

		digitalWrite(RASPI_CLK, 1);

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
			data[nr++] = datab;

		digitalWrite(RASPI_CLK, 0);
	}

	// digitalWrite(RPI_DIR, 1);
	// digitalWrite(RPI_DIR,  1);

	return nr;
}

void	pp_write(unsigned nbytes, char *data) {
	digitalWrite(RASPI_DIR, OUTPUT);
	pinMode(RASPI_D7, OUTPUT);
	pinMode(RASPI_D6, OUTPUT);
	pinMode(RASPI_D5, OUTPUT);
	pinMode(RASPI_D4, OUTPUT);
	pinMode(RASPI_D3, OUTPUT);
	pinMode(RASPI_D2, OUTPUT);
	pinMode(RASPI_D1, OUTPUT);
	pinMode(RASPI_D0, OUTPUT);

	for(unsigned i=0; i<nbytes; i++) {
		char	datab = data[i];

		digitalWrite(RASPI_D7, (datab & 0x80) ? 1:0);
		digitalWrite(RASPI_D6, (datab & 0x40) ? 1:0);
		digitalWrite(RASPI_D5, (datab & 0x20) ? 1:0);
		digitalWrite(RASPI_D4, (datab & 0x10) ? 1:0);
		digitalWrite(RASPI_D3, (datab & 0x08) ? 1:0);
		digitalWrite(RASPI_D2, (datab & 0x04) ? 1:0);
		digitalWrite(RASPI_D1, (datab & 0x02) ? 1:0);
		digitalWrite(RASPI_D0, (datab & 0x01) ? 1:0);

		digitalWrite(RASPI_CLK, 1);
		digitalWrite(RASPI_CLK, 0);
	}
}

unsigned	pp_read(unsigned nbytes, char *data) {
	unsigned	nr = 0;

	digitalWrite(RASPI_DIR, OUTPUT);
	digitalWrite(RASPI_CLK, OUTPUT);
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

	for(unsigned i=0; i<nbytes; i++) {
		char	datab = 0;

		digitalWrite(RASPI_CLK, 1);
		digitalWrite(RASPI_D7, (datab & 0x80) ? 1:0);

		if (digitalRead(RASPI_D7))	datab |= 0x80;
		if (digitalRead(RASPI_D6))	datab |= 0x40;
		if (digitalRead(RASPI_D5))	datab |= 0x20;
		if (digitalRead(RASPI_D4))	datab |= 0x10;
		if (digitalRead(RASPI_D3))	datab |= 0x08;
		if (digitalRead(RASPI_D2))	datab |= 0x04;
		if (digitalRead(RASPI_D1))	datab |= 0x02;
		if (digitalRead(RASPI_D0))	datab |= 0x01;

		digitalWrite(RASPI_CLK, 0);

		if (datab == 0x0ff)
			break;
/*
#warning "A zero here breaks protocol"
		if (datab == 0x0)
			break;
*/
		data[nr++] = datab;
	}

	return nr;
}

int main(int argc, char **argv)
{
	wiringPiSetup();

	// Comms take place over 8 bidirectional data bits, a clock,
	// and a direction bit
	pinMode(RASPI_CLK, OUTPUT);
	pinMode(RASPI_DIR, OUTPUT);

	digitalWrite(RASPI_DIR, OUTPUT);
	digitalWrite(RASPI_CLK, 0);

	pinMode(RASPI_D7, OUTPUT);
	pinMode(RASPI_D6, OUTPUT);
	pinMode(RASPI_D5, OUTPUT);
	pinMode(RASPI_D4, OUTPUT);
	pinMode(RASPI_D3, OUTPUT);
	pinMode(RASPI_D2, OUTPUT);
	pinMode(RASPI_D1, OUTPUT);
	pinMode(RASPI_D0, OUTPUT);

	for(int i=0; i<256; i++) {
		char	datab = i;

		digitalWrite(RASPI_D7, (datab & 0x80) ? 1:0);
		digitalWrite(RASPI_D6, (datab & 0x40) ? 1:0);
		digitalWrite(RASPI_D5, (datab & 0x20) ? 1:0);
		digitalWrite(RASPI_D4, (datab & 0x10) ? 1:0);
		digitalWrite(RASPI_D3, (datab & 0x08) ? 1:0);
		digitalWrite(RASPI_D2, (datab & 0x04) ? 1:0);
		digitalWrite(RASPI_D1, (datab & 0x02) ? 1:0);
		digitalWrite(RASPI_D0, (datab & 0x01) ? 1:0);

		sleep(1);
		digitalWrite(RASPI_CLK, 1);
		sleep(1);
		digitalWrite(RASPI_CLK, 0);
		sleep(1);
	}
	return 0;
}
