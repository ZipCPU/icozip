################################################################################
##
## Filename:	sw/host/Makefile
##
## Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
##
## Purpose:	
## Targets:	
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2015-2017, Gisselquist Technology, LLC
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
ARCH  ?= $(shell bash ./arch.sh)
#
ifeq ($(ARCH), arm)
PROGRAMS   := wbregs netpport
else
PROGRAMS   := wbregs # netpport
endif

PREFXPPGMS := $(addprefix $(ARCH)-,$(PROGRAMS))
SCOPES :=
all: $(PROGRAMS) $(SCOPES)
hostcheck:
	@echo "Architecture     : $(ARCH)"
	@echo "Compiler         : $(CROSS)gcc"
	@echo "Object directory : $(OBJDIR)"

CXX := $(CROSS)g++
OBJDIR := obj-$(ARCH)
BUSSRCS := hexbus.cpp llcomms.cpp regdefs.cpp byteswap.cpp
SOURCES := wbregs.cpp netpport.cpp $(BUSSRCS)
# rdclocks.cpp flashdrvr.cpp		\
#	 mkedid.cpp $(BUSSRCS)	edidrxscope.cpp	edidtxscope.cpp		\
#	zipload.cpp zipstate.cpp zipdbg.cpp cpedid.cpp readhist.cpp	\
	readframe.cpp rawdscope.cpp
	# netsetup.cpp manping.cpp wbsettime.cpp
HEADERS := llcomms.h port.h hexbus.h devbus.h
OBJECTS := $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(SOURCES)))
BUSOBJS := $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(BUSSRCS)))
CFLAGS := -g -Wall -I. -I../../rtl
LIBS :=
SUBMAKE := $(MAKE) --no-print-directory

%.o: $(OBJDIR)/%.o
$(OBJDIR)/%.o: %.cpp
	$(mk-objdir)
	$(CXX) $(CFLAGS) -c $< -o $@
$(OBJDIR)/%.o: %.c
	$(mk-objdir)
	$(CXX) $(CFLAGS) -c $< -o $@

.PHONY: clean
clean:
	rm -rf $(OBJDIR)/ $(PREFXPPGMS) a.out

$(OBJDIR)/scopecls.o: scopecls.cpp scopecls.h

ifeq ($(ARCH), arm)
.PHONY: netpport pptest
netpport: $(ARCH)-netpport
$(ARCH)-netpport: $(OBJDIR)/netpport.o
	$(CXX) $(CFLAGS) $^ -lwiringPi -o $@
pptest: $(ARCH)-pptest
$(ARCH)-pptest: $(OBJDIR)/pptest.o
	$(CXX) $(CFLAGS) $^ -lwiringPi -o $@
endif
#
# Some simple programs that just depend upon the ability to talk to the FPGA,
# and little more. 
#manping: $(OBJDIR)/manping.o $(BUSOBJS)
#	$(CXX) $(CFLAGS) $^ -o $@
.PHONY: wbregs
wbregs: $(ARCH)-wbregs
$(ARCH)-wbregs: $(OBJDIR)/wbregs.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ $(LIBS) -o $@

#
# Programs that depend upon not just the bus objects, but the flash driver
# as well.
wbprogram: $(OBJDIR)/wbprogram.o $(OBJDIR)/flashdrvr.o $(BUSOBJS)
	$(CXX) -g $^ -o $@
zipload: $(OBJDIR)/zipload.o $(OBJDIR)/flashdrvr.o $(BUSOBJS) $(OBJDIR)/zipelf.o
	$(CXX) -g $^ -lelf -o $@


## SCOPES
# These depend upon the scopecls.o, the bus objects, as well as their
# main file(s).
#
# No scopes defined
#
#


#
DBGSRCS  := zopcodes.cpp twoc.cpp
DBGOBJS := $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(DBGSRCS)))
$(ARCH)-zipdbg: $(OBJDIR)/zipdbg.o $(BUSOBJS) $(DBGOBJS)
	$(CXX) -g $^ -lcurses -o $@

define	mk-objdir
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR); fi"
endef

define	build-depends
	@echo "Building dependency file(s)"
	$(mk-objdir)
	$(CXX) $(CPPFLAGS) -MM $(SOURCES) > $(OBJDIR)/xdepends.txt
	@sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt > $(OBJDIR)/depends.txt
	@rm $(OBJDIR)/xdepends.txt
endef

tags: $(SOURCES) $(HEADERS)
	@echo "Generating tags"
	@ctags $(SOURCES) $(HEADERS)

.PHONY: depends
depends: tags
	$(build-depends)

$(OBJDIR)/depends.txt: $(SOURCES) $(HEADERS)
	$(build-depends)

-include $(OBJDIR)/depends.txt
