################################################################################
##
## Filename:	auto-data/Makefile
##
## Project:	ICO Zip, iCE40 ZipCPU demonstration project
##
## Purpose:	To coordinate the build of the glue logic holding this design
##		together via autofpga.
##
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2017-2020, Gisselquist Technology, LLC
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
.PHONY: all
all:	data
#
# Could also depend upon load, if desired, but not necessary
#
# This is the list of components that will form our project.  Each file consists
# of parts and pieces of our project that autofpga will copy/paste into our
# main project files.
#
BASE    := global.txt # dlyarbiter.txt
AUX     := version.txt buserr.txt pic.txt pwrcount.txt
IO      := gpio.txt # spio.txt
MEMORY  := spixpress.txt sramdev.txt bkram.txt
DBGBUS  := hbconsole.txt
CPU     := zipbones.txt
SCOPES  := # spixscope.txt
LDSCRIPT:= mem_flash_bkram.txt mem_bkram_only.txt mem_flash_sram.txt mem_sram_only.txt
BONUS   :=
DATA := clock50.txt $(BASE) $(AUX) $(IO) $(MEMORY) $(DBGBUS) $(CPU) $(SCOPES) $(BONUS) $(LDSCRIPT)
	# Not used: rtclite.txt watchdog.txt
	# Scopes, pick only one: spixscope sramscope dbgscope

AUTOFPGA := autofpga
$(AUTOFPGA):

.PHONY: data
data: $(AUTOFPGA) $(DATA)
	$(AUTOFPGA) -d -o . $(DATA)

clean:
	rm -f toplevel.v main.v regdefs.h regdefs.cpp board.h board.ld
	rm -f rtl.make.inc main_tb.cpp
	rm -f dump.txt
