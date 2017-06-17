################################################################################
##
## Filename:	Makefile
##
## Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
##
## Purpose:	Simply coordinates builds in the various subdirectories of
##		rtl.
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
all:	basic uart pptest icozip # icozip
# all:	verilated sw bench bit
SUBMAKE := $(MAKE) --no-print-directory -C
#
.PHONY: basic
basic:
	$(SUBMAKE) basic

.PHONY: uart
uart:
	$(SUBMAKE) uart

.PHONY: pmodleds
pmodleds:
	$(SUBMAKE) pmodleds

.PHONY: pptest
pptest:
	$(SUBMAKE) pptest

.PHONY: icozip
icozip:
	$(SUBMAKE) icozip


.PHONY: clean
clean:	clean-basic clean-uart clean-pptest clean-pmodleds

.PHONY: clean-basic
clean-basic:
	$(SUBMAKE) basic clean

.PHONY: clean-uart
clean-uart:
	$(SUBMAKE) uart clean

.PHONY: clean-pptest
clean-pptest:
	$(SUBMAKE) pptest clean

.PHONY: clean-pmodleds
clean-pmodleds:
	$(SUBMAKE) pmodleds clean

.PHONY: clean-icozip
clean-icozip:
	$(SUBMAKE) icozip clean
