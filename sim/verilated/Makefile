################################################################################
##
## Filename:	Makefile
##
## Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
##
## Purpose:	To coordinate the build of both a cycle accurate, Verilator based,
##		simulation of the main module as well as the final ICOZIP FPGA
##	design components.  Access to both components is provided via a software
##	commands via a TCP/IP port.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2017-2018, Gisselquist Technology, LLC
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
all:
CROSS ?=
ARCH  ?= $(shell bash ../../sw/host/arch.sh)
#
all: $(ARCH)-main_tb
hostcheck:
	@echo "Architecture     : $(ARCH)"
	@echo "Compiler         : $(CROSS)gcc"
	@echo "Object directory : $(OBJDIR)"

CXX	:= $(CROSS)g++
OBJDIR  := obj-$(ARCH)
RTLD	:= ../../rtl/icozip
VERILATOR_ROOT ?= $(shell bash -c 'verilator -V|grep VERILATOR_ROOT | head -1 | sed -e " s/^.*=\s*//"')
VROOT	:= $(VERILATOR_ROOT)
VDEFS   := $(shell ./vversion.sh)
VINCD   := $(VROOT)/include
INCS	:= -I$(RTLD) -I$(RTLD)/obj-$(ARCH)/ -I$(VINCD) -I$(VINCD)/vltstd
CFLAGS	:= -Og -g -Wall $(INCS)
#
# A list of our sources and headers
#
SIMSRCS := zipelf.cpp memsim.cpp byteswap.cpp pportsim.cpp
# Not used: i2csim.cpp
VOBJDR	:= $(RTLD)/$(OBJDIR)
VOBJS   := $(OBJDIR)/verilated.o $(OBJDIR)/verilated_vcd_c.o
SIMOBJ := $(subst .cpp,.o,$(SIMSRCS))
SIMOBJS:= $(addprefix $(OBJDIR)/,$(SIMOBJ)) $(VOBJS)
SOURCES := automaster_tb.cpp $(SIMSRCS)
HEADERS := $(foreach header,$(subst .cpp,.h,$(SOURCES)),$(wildcard $(header))) \
	port.h testb.h main_tb.cpp
#
PROGRAMS := $(ARCH)-main_tb
# Now return to the "all" target, and fill in some details
all:	$(PROGRAMS)

$(OBJDIR)/%.o: %.cpp
	$(mk-objdir)
	$(CXX) $(CFLAGS) $(VDEFS) $(INCS) -c $< -o $@

$(OBJDIR)/%.o: $(VINCD)/%.cpp
	$(mk-objdir)
	$(CXX) $(CFLAGS) $(INCS) -c $< -o $@

MAINOBJS := $(OBJDIR)/automaster_tb.o

$(ARCH)-main_tb: $(MAINOBJS) $(SIMOBJS)
$(ARCH)-main_tb: $(VOBJS) $(VOBJDR)/Vmain__ALL.a
	$(CXX) $(INCS) $^ $(VOBJDR)/Vmain__ALL.a -lelf -o $@

#
# The "clean" target, removing any and all remaining build products
#
.PHONY: clean
clean:
	rm -f *.vcd
	rm -f $(PROGRAMS)
	rm -rf $(OBJDIR)/

#
# The "depends" target, to know what files things depend upon.  The depends
# file itself is kept in $(OBJDIR)/depends.txt
#
define build-depends
	$(mk-objdir)
	@echo "Building dependency file"
	@$(CXX) $(CFLAGS) $(INCS) -MM $(SOURCES) > $(OBJDIR)/xdepends.txt
	@sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt > $(OBJDIR)/depends.txt
	@rm $(OBJDIR)/xdepends.txt
endef

.PHONY: depends
depends: tags
	$(build-depends)

$(OBJDIR)/depends.txt: tags $(SOURCES)
	$(build-depends)
#
define	mk-objdir
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR); fi"
endef


#
# The "tags" target
#
tags:	$(SOURCES) $(HEADERS)
	@echo "Generating tags"
	@ctags $(SOURCES) $(HEADERS)


-include $(OBJDIR)/depends.txt
