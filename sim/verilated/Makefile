################################################################################
##
## Filename:	Makefile
##
## Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
##
## Purpose:
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
VROOT   := $(VERILATOR_ROOT)
FLAGS	:= -Wall -Og -g
VINCD   := $(VROOT)/include
INCS	:= -I$(RTLD) -I$(RTLD)/obj-$(ARCH)/ -I$(RTLD) -I$(VINCD) -I$(VINCD)/vltstd
SIMSRCS := main_tb.cpp enetctrlsim.cpp qspiflashsim.cpp zipelf.cpp \
	i2csim.cpp	\
	memsim.cpp sdspisim.cpp uartsim.cpp oledsim.cpp byteswap.cpp
SOURCES := main_tb.cpp $(SIMSRCS)
HEADERS := $(foreach header,$(subst .cpp,.h,$(SOURCES)),$(wildcard $(header))) \
	dblpipecmdr.h pipecmdr.h port.h testb.h
VOBJDR	:= $(RTLD)/obj_dir
VOBJS   := $(OBJDIR)/verilated.o $(OBJDIR)/verilated_vcd_c.o
SIMOBJ := $(subst .cpp,.o,$(SIMSRCS))
SIMOBJS:= $(addprefix $(OBJDIR)/,$(SIMOBJ))
PROGRAMS := main_tb
all:	$(OBJDIR)/ $(PROGRAMS)

$(OBJDIR)/:
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR); fi"

$(OBJDIR)/%.o: %.cpp
	$(CXX) $(FLAGS) $(INCS) -c $< -o $@

$(OBJDIR)/%.o: $(VINCD)/%.cpp
	$(CXX) $(FLAGS) $(INCS) -c $< -o $@

.PHONY: oledsim.o
oledsim.o: $(OBJDIR)/oledsim.o
$(OBJDIR)/oledsim.o: oledsim.cpp
	$(CXX) $(FLAGS) $(GFXFLAGS) -c $< -o $@

$(OBJDIR)/main_tb.o: main_tb.cpp
	$(CXX) -DFASTCLK $(FLAGS) $(GFXFLAGS) $(INCS) -c $< -o $@



main_tb: $(OBJDIR)/main_tb.o $(SIMOBJS)
main_tb: $(VOBJS) $(VOBJDR)/Vmain__ALL.a
	$(CXX) $(GFXLIBS) $(INCS) $^ $(VOBJDR)/Vmain__ALL.a $(GFXLIBS) -lelf -o $@

define build-depends
	@echo "Building dependency file(s)"
	@$(CXX) $(GFXFLAGS) $(INCS) -MM $(SOURCES) > $(OBJDIR)/xdepends.txt
	@sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt	\
		| sed -e 's/fastmaster_tb.o/main_tb.o/g' 		\
		> $(OBJDIR)/depends.txt
	@rm $(OBJDIR)/xdepends.txt
endef

tags: $(SOURCES) $(HEADERS)
	@echo "Generating tags"
	@ctags $(SOURCES) $(HEADERS)

.PHONY: clean
clean:
	rm -f *.vcd
	rm -rf $(OBJDIR)/
	rm -f $(PROGRAMS)
	# rm -f ./fastmaster_tb

.PHONY: depends
depends:
	$(build-depends)

$(OBJDIR)/depends.txt: $(OBJDIR)/ $(SOURCES) $(HEADERS)
	$(build-depends)

-include $(OBJDIR)/depends.txt
