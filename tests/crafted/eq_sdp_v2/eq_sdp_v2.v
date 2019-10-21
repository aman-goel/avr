`include "spec.v"
`include "impl.v"

module eq_sdp_v2(clk);

	input wire	clk;
	wire	reset;
	wire	ctl_1, ctl_2;
	wire a, b, c;
	wire s_out, i_out, buffered_s_out;
	reg s1, s2, s3;
	
	initial begin
		s1 = 1'd0;
		s2 = 1'd0;
		s3 = 1'd0;
	end
	
	spec sp(clk, reset, ctl_1, ctl_2, a, b, c, s_out);
	impl im(clk, reset, ctl_1, ctl_2, a, b, c, i_out);
	
	always @(posedge clk) begin
		if (reset == 1'b1) begin
			s1 <= 1'd0;
			s2 <= 1'd0;
			s3 <= 1'd0;
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
