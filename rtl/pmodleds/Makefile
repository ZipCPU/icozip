################################################################################
## 
## Filename: 	rtl/pmodleds/Makefile
##
## Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
##
## Purpose:	To direct the build of the files in the rtl/pmodleds directory.
##		The files in this directory assume that the user has a Digilent
##	PMod LED8 connected to their ICO board.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2016-2017, Gisselquist Technology, LLC
##
## This program is free software (firmware): you can redistribute it and/or
## modify it under the terms of  the GNU General Public License as published
## by the Free Software Foundation, either version 3 of the License, or (at
## your option) any later version.
##
## This program is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
## for more details.
##
## You should have received a copy of the GNU General Public License along
## with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
## target there if the PDF file isn't present.)  If not, see
## <http://www.gnu.org/licenses/> for a copy.
##
## License:	GPL, v3, as defined and found on www.gnu.org,
##		http://www.gnu.org/licenses/gpl.html
##
##
################################################################################
##
##
all: ledbouncer	ledwalker

# GNU Make automatic variables (since I can never remember these ...)
# $@	- name of the target
# $<	- Name of the first prerequisite
# $^	- Names of all the prerequisites
%.blif: %.v
	yosys -p 'synth_ice40 -blif $@' $<
%.asc: %.blif %.pcf
	arachne-pnr -d 8k -p $*.pcf -o $@ $<
%.bin: %.asc
	icetime -d hx8k -c 100 $<
	icepack $< $@

.PHONY: bouncer walker ledbouncer ledwalker
walker:     ledwalker.bin
ledwalker:  ledwalker.bin
bouncer:    ledbouncer.bin
ledbouncer: ledbouncer.bin

.PHONY: load
load: ledwalker.bin
	echo "Type/run sudo icoprog -p < ledwalker.bin" # Needs sudo

clean:
	rm -f *.blif *.asc *.bin
	# rm -rf obj_dir

