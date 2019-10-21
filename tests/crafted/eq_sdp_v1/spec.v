module spec(clk, reset, ctl_1, ctl_2, a, b, c, out);
 	output wire	[7:0]	out;

	input wire	clk, reset;
	input wire	ctl_1, ctl_2;
	input wire [7:0] a, b, c;

	wire [7:0] m = ctl_1 ? a + b : a - b;
	wire [7:0] n = ctl_2 ? m + c : m - c;
	assign out = n;
endmodule // mult
