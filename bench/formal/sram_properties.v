`default_nettype	none

module	sram_properties(i_clk, i_ce_n, i_oe_n, i_we_n, i_lb, i_ub,
		i_addr, i_data, o_data);
	parameter	CLOCKRATE_HZ = 50_000_000;
	parameter	AW = 16, DW = 16;
	//
	parameter	tRC    = 12e-9;
	parameter	tAA    = 12e-9;
	parameter	tCHA   = 3e-9;
	parameter	tACE   = 12e-9;
	parameter	tDOE   = 12e-9;
	parameter	tHZOE  = 12e-9;
	parameter	tHZCE  = 3e-9;
	parameter	tLZCE  = 12e-9;
	parameter	tBA    = 6.5e-9;
	parameter	tHZB   = 6.5e-9;
	//
	parameter	tWC    = 12e-9;
	parameter	tSCE   = 9e-9;
	parameter	tAW    = 9e-9;
	parameter	tPWB   = 9e-9;
	parameter	tPWE1  = 9e-9;
	parameter	tPWE2  = 11e-9;
	parameter	tSD    = 9e-9;
	parameter	tHD    = 9e-9;
	parameter	tHZWE    = 9e-9;
	parameter	tLZWE    = 9e-9;
	//
	parameter	CK_RC    = tRC   * CLOCKRATE_HZ;
	parameter	CK_AA    = tAA   * CLOCKRATE_HZ - 1;
	parameter	CK_CHA   = tCHA  * CLOCKRATE_HZ;
	parameter	CK_ACE   = tACE  * CLOCKRATE_HZ;
	parameter	CK_DOE   = tDOE  * CLOCKRATE_HZ;
	parameter	CK_HZOE  = tHZOE * CLOCKRATE_HZ;
	parameter	CK_HZCE  = tHZCE * CLOCKRATE_HZ;
	parameter	CK_LZCE  = tLZCE * CLOCKRATE_HZ;
	parameter	CK_BA    = tBA   * CLOCKRATE_HZ;;
	parameter	CK_HZB   = tHZB  * CLOCKRATE_HZ;;
	//
	input	wire	i_clk;
	//
	input	wire	i_ce_n, i_oe_n, i_we_n;
	input	wire	i_lb, i_ub;
	//
	input	wire	[AW-1:0]	i_addr;
	input	wire	[DW-1:0]	i_data;
	output	wire	[DW-1:0]	o_data;

	reg	[DW-1:0]	mem	[0:((1<<AW)-1)];

	reg	[4:0]	clocks_since_ce_change;
	reg	[4:0]	clocks_since_oe_change;
	reg	[4:0]	clocks_since_we_change;
	reg	[4:0]	clocks_since_addr_change;


	initial	clocks_since_ce_change = 0;
	always @(posedge i_clk)
	if (i_ce_n != $past(i_ce_n))
		clocks_since_ce_change = 0;
	else if (!(&clocks_since_ce_change)
		clocks_since_ce_change <= clocks_since_ce_change+1;

	initial	clocks_since_oe_change = 0;
	always @(posedge i_clk)
	if (i_oe_n != $past(i_oe_n))
		clocks_since_oe_change = 0;
	else if (!(&clocks_since_oe_change)
		clocks_since_oe_change <= clocks_since_oe_change+1;


	initial	clocks_since_we_change = 0;
	always @(posedge i_clk)
	if (i_we_n != $past(i_we_n))
		clocks_since_we_change = 0;
	else if (!(&clocks_since_we_change)
		clocks_since_we_change <= clocks_since_we_change+1;

	initial	clocks_since_addr_change = 0;
	always @(posedge i_clk)
	if (i_addr != $past(i_addr))
		clocks_since_addr_change = 0;
	else if (!(&clocks_since_addr_change)
		clocks_since_addr_change <= clocks_since_addr_change+1;

	wire	[AW+5-1:0]	read_request;
	assign	read_request = { i_ce_n, i_oe_n, i_we_n, i_lb, i_ub };
	reg	[AW+5-1:0]	past_read_request;
	always @(posedge i_clk)
		past_read_request <= read_request;

	reg	[AW-1:0]	past_addr;
	always @(posedge i_clk)
		past_addr <= i_addr;

	wire	invalid_read_data;
	always @(*)
	begin
		invalid_data = 1'b0;
		if (read_request != past_read_request)
			invalid_data = 1'b1;
		if (clocks_since_ce_change < CK_AA)
			invalid_data = 1'b1;
		if (clocks_since_oe_change < CK_AA)
			invalid_data = 1'b1;
		if (clocks_since_addr_change < CK_AA)
			invalid_data = 1'b1;
	end

	always @(posedge i_clk)
	if ((!i_ce_n)&&(!$past(i_ce_n))
			&&(!i_oe_n)&&(!$past(i_oe_n))
			&&(invalid_data))
		assert($stable(i_addr));

	always @(posedge i_clk)
	if ((!i_ce_n)&&(!i_oe_n)&&(!i_we_n)
		&&($past((!i_ce_n)&&(!i_oe_n)&&(!i_we_n)))
		&&($past(clocks_since_addr_change < CK_RC)))
		assert($stable(read_request));
endmodule
