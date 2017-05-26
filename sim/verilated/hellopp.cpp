#include <signal.h>
#include <time.h>
#include <ctype.h>
#include <stdint.h>
#include <stdlib.h>


#include "verilated.h"
#include "Vhellopp.h"
#define	BASECLASS	Vhellopp

#include "dblpipecmdr.h"

class	TESTBENCH : public DBLPIPECMDR<BASECLASS> {
public:
	unsigned	m_last_led;
	time_t		m_start_time;
	int		m_bomb;
	bool		m_done;

	TESTBENCH(int fpgaport, bool copy_to_stdout)
			: DBLPIPECMDR(fpgaport, copy_to_stdout)
			{

		m_start_time = time(NULL);
		m_done = false;
		m_bomb = 0;
		//
	}

	void	trace(const char *vcd_trace_file_name) {
		fprintf(stderr, "Opening TRACE(%s)\n", vcd_trace_file_name);
		opentrace(vcd_trace_file_name);
	}

	void	close(void) {
		// TESTB<BASECLASS>::closetrace();
		m_done = true;
	}

	void	tick(void) {
		if (m_done)
			return;
		if ((m_tickcount & ((1<<28)-1))==0) {
			double	ticks_per_second = m_tickcount;
			time_t	seconds_passed = time(NULL)-m_start_time;
			if (seconds_passed != 0) {
			ticks_per_second /= (double)(time(NULL) - m_start_time);
			printf(" ********   %.6f TICKS PER SECOND\n", 
				ticks_per_second);
			}
		}

		DBLPIPECMDR::tick();
	}

	bool	done(void) {
		return m_done;
	}
};

TESTBENCH	*tb;

void	usage(void) {
	puts("USAGE\n");
}

int	main(int argc, char **argv) {
	const	char *elfload = NULL,
		 *trace_file = "trace.vcd";
	bool	debug_flag = false;
	int	fpga_port = 8845; // FPGAPORT;
	int	copy_comms_to_stdout = -1;
	Verilated::commandArgs(argc, argv);

	for(int argn=1; argn < argc; argn++) {
		if (argv[argn][0] == '-') for(int j=1;
					(j<512)&&(argv[argn][j]);j++) {
			switch(tolower(argv[argn][j])) {
			case 'c': copy_comms_to_stdout = 1; break;
			case 'd': debug_flag = true;
				if (trace_file == NULL)
					trace_file = "trace.vcd";
				break;
			case 'p': fpga_port = atoi(argv[++argn]); j=1000; break;
			// case 's':serial_port=atoi(argv[++argn]);j=1000;break;
			case 't': trace_file = argv[++argn]; j=1000; break;
			case 'h': usage(); break;
			default:
				fprintf(stderr, "ERR: Unexpected flag, -%c\n\n",
					argv[argn][j]);
				usage();
				break;
			}
		} else {
			fprintf(stderr, "ERR: Unknown argument %s\n", argv[argn]);
			exit(EXIT_FAILURE);
		}
	}

	if (copy_comms_to_stdout < 0)
		copy_comms_to_stdout = 1;
	tb = new TESTBENCH(fpga_port, true);


	printf("Opening Bus-master with\n");
	printf("\tDebug Access port = %d\n", fpga_port);
	if (trace_file) {
		printf("\tVCD File         = %s\n", trace_file);
		tb->trace(trace_file);
	}

	while(!tb->done())
		tb->tick();

	exit(0);
}

