`define W 4
`define WS1 3
`define CNT_MAX 4'b1111

module cav14_example(clk);

	input wire clk;
	reg [`WS1:0] X, Y;

	initial begin
		X = `W'd1;
		Y = `W'd0;
	end

	always @(posedge clk) begin
		X <= (Y > X) ? X : ((Y == X) || (X != `CNT_MAX))? (X + `W'd1) : Y;
		Y <= (Y == X) ? (Y + `W'd1) : ((Y > X) || (X != `CNT_MAX)) ? Y : X;
	end

	wire prop = !(Y > X);
	wire prop_neg = !prop;
	assert property ( prop );
endmodule















