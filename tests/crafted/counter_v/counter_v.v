`define W 4
`define WST 3
`define Kmax 4'b1111
module counter(clk);

	input wire clk;
	reg [`WST:0] X;
	wire en;

	initial begin
		X = `W'd1;
	end

	always @(posedge clk) begin
		X <= en ? ( (X == `Kmax) ? `W'd1 : (X + `W'd1) ) : X ;
	end

	wire prop = (X != `Kmax);
	wire prop_neg = !prop;
	assert property ( prop );
	
// 	assume property ( !en );
endmodule















