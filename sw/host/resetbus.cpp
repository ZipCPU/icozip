#include <stdio.h>
#include "llcomms.h"
#include "port.h"

int main(int argc, const char **argv) {
	NETCOMMS	*nc = new NETCOMMS(FPGAHOST, FPGAPORT);
	char	buf[32];

	buf[0] = 'T'+0x80;
	buf[1] = 0;
	nc->write(buf, 1);
	nc->close();
}
