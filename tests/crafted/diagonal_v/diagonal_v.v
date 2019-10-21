`define W    4
`define Kmax `W'b1111

// module diagonal(clk, reset);
module diagonal(clk);

	input wire clk;
	reg [(`W - 1):0] X, Y;
// 	input wire reset;
	wire reset;

	initial begin
		X = `W'd1;
		Y = `W'd0;
	end

	always @(posedge clk) begin
		X <= (!reset && (X > Y)) ? ((`Kmax >> 1) + (X >> 1)) : (X < Y) ? X : ((Y == X) || (X != `Kmax)) ? (X + `W'd1) : Y;
		Y <= (!reset && (X > Y)) ? Y  : (!(X > Y) || (X != `Kmax)) ? (Y + `W'd1) : X;
	end

	wire prop = !(X < Y);
	wire prop_neg = !prop;
	assert property ( prop );
endmodule
