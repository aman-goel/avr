`define W 6
`define WS 5

`define Kinit `W'd0
`define Kinc  `W'd3
`define Kcond `W'd17
`define Kprop `W'd19

module sw_loop(clk);

	input wire clk;
	reg [`WS:0] X;
	reg L0, L1, L2, L3, L4, L5, L6;
	reg LoneHot;

	initial begin
		X = `Kinit;
		L0 = 1;
		L1 = 0;
		L2 = 0;
		L3 = 0;
		L4 = 0;
		L5 = 0;
		L6 = 0;
		LoneHot = 1;
	end

	always @(posedge clk) begin
		LoneHot <=  ( L0 && !L1 && !L2 && !L3 && !L4 && !L5 && !L6) || 
					(!L0 &&  L1 && !L2 && !L3 && !L4 && !L5 && !L6) ||
					(!L0 && !L1 &&  L2 && !L3 && !L4 && !L5 && !L6) ||
					(!L0 && !L1 && !L2 &&  L3 && !L4 && !L5 && !L6) ||
					(!L0 && !L1 && !L2 && !L3 &&  L4 && !L5 && !L6) ||
					(!L0 && !L1 && !L2 && !L3 && !L4 &&  L5 && !L6) ||
					(!L0 && !L1 && !L2 && !L3 && !L4 && !L5 &&  L6) ;
		
		if (LoneHot)
		begin
			X <= (L1) ? (X < `Kprop) ? (X + `Kinc) : X : X ;
			L0 <= 1'd0 ;
			L1 <= L0 || (L3 && (X < `Kcond)) ;
			L2 <= L1 && (X < `Kprop) ;
			L3 <= L2 ;
			L4 <= (L3 && !(X < `Kcond)) ;
			L5 <= L5 || (L4 && (X < `Kprop)) ;
			L6 <= L6 || (L1 && !(X < `Kprop)) || (L4 && !(X < `Kprop)) ;
		end

		else
		begin
			X  <= X ;
			L0 <= L0 ;
			L1 <= L1 ;
			L2 <= L2 ;
			L3 <= L3 ;
			L4 <= L4 ;
			L5 <= L5 ;
			L6 <= L6 ;
		end
	end

	wire prop = !L6 ;
	wire prop_neg = !prop;
	assert property ( prop );
endmodule















