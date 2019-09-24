`include "spec.v"
`include "impl.v"

module eq_sdp_v6(clk);

	input wire	clk;
	wire	reset;
	wire	ctl_a, ctl_b;
	wire [7:0] a, b, c;
	wire [7:0] s_out, i_out;
	reg [7:0] ra1, ra2, ra3;
	reg [7:0] rb1, rb2, rb3;
	reg [7:0] rc1, rc2, rc3;
	reg	ctl_a1, ctl_a2, ctl_a3;
	reg	ctl_b1, ctl_b2, ctl_b3;
	
	initial begin
		ra1 = 8'd0;
		ra2 = 8'd0;
		ra3 = 8'd0;
		rb1 = 8'd0;
		rb2 = 8'd0;
		rb3 = 8'd0;
		rc1 = 8'd0;
		rc2 = 8'd0;
		rc3 = 8'd0;
		ctl_a1 = 1'b0;
		ctl_a2 = 1'b0;
		ctl_a3 = 1'b0;
		ctl_b1 = 1'b0;
		ctl_b2 = 1'b0;
		ctl_b3 = 1'b0;
	end
	
	spec sp(clk, reset, ctl_a3, ctl_b3, ra3, rb3, rc3, s_out);
	impl im(clk, reset, ctl_a, ctl_b, a, b, c, i_out);
	
	always @(posedge clk) begin
		if (reset == 1'b1) begin
			ra1 <= 8'd0;
			ra2 <= 8'd0;
			ra3 <= 8'd0;
			rb1 <= 8'd0;
			rb2 <= 8'd0;
			rb3 <= 8'd0;
			rc1 <= 8'd0;
			rc2 <= 8'd0;
			rc3 <= 8'd0;
			ctl_a1 <= 1'b0;
			ctl_a2 <= 1'b0;
			ctl_a3 <= 1'b0;
			ctl_b1 <= 1'b0;
			ctl_b2 <= 1'b0;
			ctl_b3 <= 1'b0;
		end else begin
			ra1 <= a;
			ra2 <= ra1;
			ra3 <= ra2;
			rb1 <= b;
			rb2 <= rb1;
			rb3 <= rb2;
			rc1 <= c;
			rc2 <= rc1;
			rc3 <= rc2;
			ctl_a1 <= ctl_a;
			ctl_a2 <= ctl_a1;
			ctl_a3 <= ctl_a2;
			ctl_b1 <= ctl_b;
			ctl_b2 <= ctl_b1;
			ctl_b3 <= ctl_b2;			
		end
	end

	wire prop = (s_out == i_out);
	wire prop_neg = !prop;
	assert property ( prop );
endmodule // mult
