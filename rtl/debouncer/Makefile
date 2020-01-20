################################################################################
##
## Filename: 	debouncer/Makefile
##
## Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
##
## Purpose:	To coordinate the build of a button debouncing test design
##		for the icoboard.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2016-2019, Gisselquist Technology, LLC
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
all: testbus
YOSYS      := yosys
NEXTPNR    := nextpnr-ice40 --hx8k -r --package ct256
ICEPACK    := icepack
ICETIME    := icetime

# GNU Make automatic variables (since I can never remember these ...)
# $@	- name of the target
# $<	- Name of the first prerequisite
# $^	- Names of all the prerequisites
%.json: %.v
	$(YOSYS) -p 'synth_ice40 -json $@' $<
%.asc: %.json %.pcf
	$(NEXTPNR) --freq 80 --pcf $*.pcf --json $*.json --asc $@
%.bin: %.asc
	$(ICETIME) -d hx8k -c 80 $<
	$(ICEPACK) $< $@

PPSRCS := ppio.v pport.v
HEXSRCS := hbbus.v hbdechex.v hbdeword.v hbexec.v hbgenhex.v hbidle.v hbints.v hbnewline.v hbpack.v
PSRCS := $(addprefix ../pport/,$(PPSRCS))
HSRCS := $(addprefix ../hexbus/,$(HEXSRCS))
VSRCS :=  testbus.v debouncer.v unbounced.v wbscopc.v # wbscope.v
testbus.json: $(VSRCS) $(HSRCS)
	$(YOSYS) -p 'synth_ice40 -json $@ -top testbus' $(VSRCS) $(HSRCS) $(PSRCS) | tee log.txt
testbus.asc: testbus.json debouncer.pcf
	$(NEXTPNR) --freq 80 --pcf debouncer.pcf --json testbus.json --asc $@


.PHONY: testbus
testbus: testbus.bin

clean:
	rm -f *.blif *.asc *.json *.bin
	rm -rf obj_dir

