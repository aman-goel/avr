`define W    4
`define Kmax `W'b1111

module diagonal(clk, reset, X, Y);

	input wire clk;
	input wire reset;
	output reg [(`W - 1):0] X, Y;

	initial begin
		X = `W'd0;
		Y = `W'd0;
	end

	always @(posedge clk) begin
		X <= (!reset && (X > Y)) ? ((`Kmax >> `W'd1) + (X >> `W'd1)) : (X < Y) ? X : ((Y == X) || (X != `Kmax)) ? (X + `W'd1) : Y;
		Y <= (!reset && (X > Y)) ? Y  : (!(X > Y) || (X != `Kmax)) ? (Y + `W'd1) : X;
	end

	wire prop = !(X < Y);
	wire prop_neg = !prop;
	assert property ( prop );
endmodule
