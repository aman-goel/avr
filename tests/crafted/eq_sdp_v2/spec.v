module spec(clk, reset, ctl_1, ctl_2, a, b, c, out);
 	output wire	out;

	input wire	clk, reset;
	input wire	ctl_1, ctl_2;
	input wire  a, b, c;

	wire  m = ctl_1 ? a + b : a - b;
	wire  n = ctl_2 ? m + c : m - c;
	assign out = n;
endmodule // mult
