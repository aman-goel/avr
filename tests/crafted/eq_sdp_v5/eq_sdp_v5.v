`include "spec.v"
`include "impl.v"

module eq_sdp_v5(clk);

	input wire	clk;
	wire	reset;
	wire	ctl_1, ctl_2;
	wire [7:0] a, b, c;
	wire [7:0] s_out, i_out, buffered_s_out;
	reg [7:0] s1, s2, s3;
	
	initial begin
		s1 = 8'd0;
		s2 = 8'd0;
		s3 = 8'd0;
	end
	
	spec sp(clk, reset, ctl_1, ctl_2, a, b, c, s_out);
	impl im(clk, reset, ctl_1, ctl_2, a, b, c, i_out);
	
	always @(posedge clk) begin
		if (reset == 1'b1) begin
			s1 <= 8'd0;
			s2 <= 8'd0;
			s3 <= 8'd0;
		end else begin
			s1 <= s_out;
			s2 <= s1;
			s3 <= s2;
		end
	end

	assign buffered_s_out = s3;
	wire prop = (buffered_s_out == i_out);
	wire prop_neg = !prop;
	assert property ( prop );
endmodule // mult
