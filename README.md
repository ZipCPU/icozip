# ICOZIP

ICO Zip is intended to be a demonstration repository, demonstrating how the
[ZipCPU](https://github.com/ZipCPU/zipcpu) may be placed onto an
[ICO board](http://www.icoboard.org).

Particular goals of this project include:
- Generate the main project files using [AutoFPGA](https://github.com/ZipCPU/autofpga)
- Demonstrate the ZipCPU running [tttt](https://github.com/ZipCPU/tttt), a 4x4x4 tic-tac-toe game

A unique feature of this project is that the
[Raspberry Pi](https://www.raspberrypi.org/products/raspberry-pi-2-model-b/)
that will host the
[ICO board](http://icoboard.org) will only have a minor role in the project. 
My intention is to use the
[Raspberry Pi](https://www.raspberrypi.org/products/raspberry-pi-2-model-b/)
only as a TCP/IP stack the provides access to 1) a command
port on the FPGA, 2) a serial port within the FPGA, and perhaps even 3) a means
of downloading new bit files to the FPGA.  If all goes well, then, one should
only need to run the [netpport](sw/host/netpport.cpp) program on the
[Raspberry Pi](https://www.raspberrypi.org/products/raspberry-pi-2-model-b/),
and after that everything should be accessable through the TCP/IP port numbers
given in [port.h](sw/host/port.h).

This actually has a *very* profound consequence.  By allowing the user to have
access to the internals of the FPGA, peripheral development may be done and
verified prior to placing the CPU into the FPGA.  Hence, by the time the CPU
is placed on board, all the parts and pieces of the design will already be
known to work, leaving the only new variable that of the CPU itself.

## Status

This project is a work in progress, but it is now close enough that if you have
an interest in it then I would welcome you to try it.

As of 20170526, the [basic](rtl/basic), [uart](rtl/uart), and
[pmodled](rtl/pmodleds) examples are fully functional.
While much work has taken place on the parallel port testing modules
(using sw/netpport)--they just aren't reliable enough (yet) to depend upon.

*UPDATE*: As of 20180731 ...
1. The simulator is now fully functional
2. The CPU test runs.  Steps to running the CPU test include:
   -- Adjusting sw/host/port.h to contain the network name of your
      [Raspberry Pi](https://www.raspberrypi.org/products/raspberry-pi-2-model-b/).
      This can be 'localhost' if you intend to do all your work on the
      [Pi](https://www.raspberrypi.org/products/raspberry-pi-2-model-b/).
   -- To build the design, you'll need to have verilator, yosys, arachne-pnr,
      icestorm, and the icotools installed.  You'll also need the ZipCPU
      toolchain and AutoFPGA installed and in your path
   -- Once the prerequisites have been installed, type 'make' from the
      main directory.
   -- Repeat the build in the sw/host directory from your [Raspberry
      Pi](https://www.raspberrypi.org/products/raspberry-pi-2-model-b/).
   -- Copy the arm-netpport program to the main directory of the
      [Pi](https://www.raspberrypi.org/products/raspberry-pi-2-model-b/).
   -- Using icoprog, load the design to the board. ```icoprog -p < icozip.bin```
   -- From the RPi, run arm-netpport
      [RPi](https://www.raspberrypi.org/products/raspberry-pi-2-model-b/),
      run [arm-netpport](sw/host/netpport.cpp).
   -- You can then interact with the FPGA using [arm-wbregs](sw/host/wbregs.cpp) from another ARM
      terminal, or [pc-wbregs](sw/host/wbregs.cpp) from a PC based host connected over the network.
      For example, ```pc-wbregs version``` will return the date of the build.
   -- To run the CPU test design, telnet into the pi at port 8364 to get access
      to the console, as in `telnet rpi 8364`.
   -- In another window, type ```pc-zipload -n rpi -r sw/board/cputest``` where
      `rpu` is the network name/address of your raspberry pi.
      [Raspberry Pi](https://www.raspberrypi.org/products/raspberry-pi-2-model-b/).
      Alternatively, you can type ```arm-zipload -r sw/board/cputest``` from a
      [Pi](https://www.raspberrypi.org/products/raspberry-pi-2-model-b/)
      PI.
   -- Look for the results of the [CPU test](sw/board/cputest.c) in the console window where you
      telnet'ed into the CPU on port 8364.

3. Building the design will also build a simulation in sim/verilated.  The
   main program file for this simulation is [automaster_tb.cpp](sim/verilated/automaster_tb.cpp).  (The [main_tb.cpp](sim/verilated/main_tb.cpp) file is created by AutoFPGA, and so [automaster_tb.cpp](sim/verilated/automaster_tb.cpp) is the actual top level program.) You
   can interact with this simulation just as you would with the CPU.  The
   name of the simulation will either be `pc-main_tb` or `arm-main_tb`
   depending on whether you are running from your host computer or the
   [Pi](https://www.raspberrypi.org/products/raspberry-pi-2-model-b/).
   `pc-main_tb` can take an argument `-t trace.vcd` to force it to create a
   trace.  It can also take the name of a ZipCPU program, which it will then
   load and automatically run.
4. I haven't tested flash based programs yet, such as the 4x4x4 tic-tac-toe
   program mentioned above.

*UPDATE*: As of 20180801 ...
1. Flash based programs now run
2. The debugger has been ported to this architecture
3. The CPU can now run "Hello, World!" using the newlib C-library, and even starting by copying the program from flash to SRAM
4. After running [cputest](sw/board/cputest.c), the following are the additional steps necessary to run [hello world](sw/board/hello.c):
  -- The default Makefile should cause a build in [sw/zlib](sw/zlib), then [sw/board](sw/board)
  -- This will build [hello][sw/board/hello.c]
  -- To run it, as before, load the board and start [arm-netpport](sim/host/netpport.cpp)
  -- To capture the output, `telnet rpi 8364`, or whatever the network address of your [Raspberry Pi](https://www.raspberrypi.org/products/raspberry-pi-2-model-b/) is.
  -- Then run `pc-zipload -r sw/board/hello` to load and run the program.
  -- Watch your telnet session to see the result
4. You can also run this in a simulation, but running either `pc-main_tb path/to/hello`, or `pc-main_tb` and then running `pc-zipload -r path/to/hello`.  You may need to add a `-n localhost` parameter to your `zipload` command, and you will need to telnet into your local simulation host, but otherwise running from simulation is the same as from the hardware.

