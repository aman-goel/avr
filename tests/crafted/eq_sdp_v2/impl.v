module impl(clk, reset, ctl_1, ctl_2, a, b, c, out);
 	output wire	out;

	input wire	clk, reset;
	input wire	ctl_1, ctl_2;
	input wire a, b, c;

	reg	p1_ctl_1, p1_ctl_2;
	reg p1_a, p1_b, p1_c;
	
	reg	p2_ctl_2;
	reg p2_m, p2_c;

	reg p3_n;
	
	assign out = p3_n;

	initial begin
		p1_ctl_1		= 1'b0;
		p1_ctl_2		= 1'b0;
		p1_a			= 1'd0;
		p1_b			= 1'd0;
		p1_c			= 1'd0;
		p2_ctl_2		= 1'b0;
		p2_m			= 1'd0;
		p2_c			= 1'd0;
		p3_n			= 1'd0;
	end
	
	always @(posedge clk) begin
		if (reset == 1'b1) begin
			p1_ctl_1		<= 1'b0;
			p1_ctl_2		<= 1'b0;
			p1_a			<= 1'd0;
			p1_b			<= 1'd0;
			p1_c			<= 1'd0;
			p2_ctl_2		<= 1'b0;
			p2_m			<= 1'd0;
			p2_c			<= 1'd0;
			p3_n			<= 1'd0;
		end else begin
			p1_ctl_1		<= ctl_1;
			p1_ctl_2		<= ctl_2;
			p1_a			<= a;
			p1_b			<= b;
			p1_c			<= c;
			p2_ctl_2		<= p1_ctl_2;
			p2_m			<= p1_ctl_1 ? p1_a + p1_b : p1_a - p1_b;
			p2_c			<= p1_c;
			p3_n			<= p2_ctl_2 ? p2_m + p2_c : p2_m - p2_c;
		end
	end
endmodule // mult
