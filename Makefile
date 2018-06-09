################################################################################
##
## Filename:	Makefile
##
## Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
##
## Purpose:	A master project makefile.  It tries to build all targets
##		within the project, mostly by directing subdirectory makes.
##
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
.PHONY: all
all:	check-install archive datestamp autodata rtl sw sim # verilated bench
#
# Could also depend upon load, if desired, but not necessary
SIM   := `find sim -name Makefile` `find sim -name "*.cpp"` `find sim -name "*.h"` `find sim -name "*.c"`
RTL   := `find rtl -name "*.v"` `find rtl -name Makefile`
NOTES := `find . -name "*.txt"` `find . -name "*.html"`
SW    := `find sw -name "*.cpp"` `find sw -name "*.c"`	\
	`find sw -name "*.h"`	`find sw -name "*.sh"`	\
	`find sw -name "*.py"`	`find sw -name "*.pl"`	\
	`find sw -name "*.png"`	`find sw -name Makefile`
DEVSW := `find sw/board -name "*.cpp"` `find sw/board -name "*.h"` \
	`find sw/board -name Makefile`
PROJ  :=
BIN  := `find rtl -name "*.bin"`
AUTODATA := `find auto-data -name "*.txt"`
CONSTRAINTS := `find . -name "*.pcf"`
YYMMDD:=`date +%Y%m%d`
SUBMAKE:= $(MAKE) --no-print-directory -C

#
#
# Check that we have all the programs available to us that we need
#
#
.PHONY: check-install
check-install: check-perl check-autofpga check-verilator check-zip-gcc check-gpp

.PHONY: check-perl
	$(call checkif-installed,perl,,perl)

.PHONY: check-autofpga
check-autofpga:
	$(call checkif-installed,autofpga,-V,autofpga)

.PHONY: check-verilator
check-verilator:
	$(call checkif-installed,verilator,-V,verilator)

.PHONY: check-zip-gcc
check-zip-gcc:
	$(call checkif-installed,zip-gcc,-v,zip-gcc)

.PHONY: check-gpp
check-gpp:
	$(call checkif-installed,g++,-v,g++)

.PHONY: check-yosys
check-yosys:
	$(call checkif-installed,yosys,-h,yosys)

.PHONY: check-arachnepnr
check-arachnepnr:
	$(call checkif-installed,arachne-pnr,-v,arachne-pnr)

.PHONY: check-icetime
check-icetime:
	$(call checkif-installed,which,icetime,icetime)

.PHONY: check-icepack
check-icepack:
	$(call checkif-installed,which,icepack,icepack)

#
#
#
# Now that we know that all of our required components exist, we can build
# things
#
#
#
# Create a datestamp file, so that we can check for the build-date when the
# project was put together.
#
.PHONY: datestamp
datestamp: check-perl
	@bash -c 'if [ ! -e $(YYMMDD)-build.v ]; then rm -f 20??????-build.v; perl mkdatev.pl > $(YYMMDD)-build.v; rm -f rtl/icozip/builddate.v; fi'
	@bash -c 'if [ ! -e rtl/icozip/builddate.v ]; then cp $(YYMMDD)-build.v rtl/icozip/builddate.v; fi'

#
#
# Make a tar archive of this file, as a poor mans version of source code control
# (Sorry ... I've been burned too many times by files I've wiped away ...)
#
ARCHIVEFILES := $(BENCH) $(SW) $(RTL) $(NOTES) $(PROJ) $(BIN) $(CONSTRAINTS) $(AUTODATA) README.md
.PHONY: archive
archive:
	tar --transform s,^,$(YYMMDD)-ico/, -chjf $(YYMMDD)-ico.tjz $(ARCHIVEFILES)

#
#
# Build our main (and toplevel) Verilog files via autofpga
#
.PHONY: autodata
autodata: check-autofpga
	$(MAKE) --no-print-directory --directory=auto-data
	$(call copyif-changed,auto-data/toplevel.v,rtl/icozip/toplevel.v)
	$(call copyif-changed,auto-data/main.v,rtl/icozip/main.v)
	$(call copyif-changed,auto-data/regdefs.h,sw/host/regdefs.h)
	$(call copyif-changed,auto-data/regdefs.cpp,sw/host/regdefs.cpp)
	$(call copyif-changed,auto-data/board.h,sw/board/board.h)
	$(call copyif-changed,auto-data/board.ld,sw/board/board.ld)
	$(call copyif-changed,auto-data/rtl.make.inc,rtl/icozip/auto.mk)
	$(call copyif-changed,auto-data/main_tb.cpp,sim/verilated/main_tb.cpp)
	$(call copyif-changed,auto-data/testb.h,sim/verilated/testb.h)

.PHONY: doc
doc:
	$(SUBMAKE) doc

.PHONY: verilated
verilated: rtl

.PHONY: rtl
rtl: check-yosys check-arachnepnr check-icepack check-icetime datestamp autodata
	$(SUBMAKE) rtl

#
#
# Build a simulation of this entire design
#
.PHONY: sim
sim: rtl
	$(SUBMAKE) sim/verilated

#
#
# A master target to build all of the support software
#
.PHONY: sw
sw: sw-host # sw-zlib sw-board

#
#
# Build the hardware specific newlib library
#
.PHONY: sw-zlib
sw-zlib: autodata check-zip-gcc
	$(SUBMAKE) sw/zlib

#
#
# Build the board software.  This may (or may not) use the software library
#
.PHONY: sw-board
sw-board: check-zip-gcc # sw-zlib
	$(SUBMAKE) sw/board

#
#
# Build the host support software
#
.PHONY: sw-host
sw-host: rtl check-gpp
	$(SUBMAKE) sw/host

# .PHONY: sw-board
# sw-board: autodata rtl
	# $(SUBMAKE) sw/board

#
#
# Copy a file from the auto-data directory that had been created by
# autofpga, into the directory structure where it might be used.
#
define	copyif-changed
	@bash -c 'cmp $(1) $(2) >& /dev/null; if [[ $$? != 0 ]]; then echo "Copying $(1) to $(2)"; cp $(1) $(2); fi'
endef

#
#
# Check if the given program is installed
#
define	checkif-installed
	@echo "Checking whether or not $(3) is installed and in your path"
	@bash -c '$(1) $(2) < /dev/null >& /dev/null; if [[ $$? != 0 ]]; then echo "Program not found: $(1)"; exit -1; fi'
endef


.PHONY: clean
clean:
	$(SUBMAKE) auto-data     clean
	$(SUBMAKE) rtl           clean
	$(SUBMAKE) doc           clean
	$(SUBMAKE) sw/host       clean

