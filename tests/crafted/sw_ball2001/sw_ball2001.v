`define W 3
`define WS 2

`define K0 `W'd0
`define K1 `W'd1

module ball2001(clk);

	input wire clk;
	reg [`WS:0] X, Y, Z, W;
	reg L0, L1, L2, L3, L4, L5, L6, L7, L8;
	reg LoneHot;

	initial begin
		L0 = 1;
		L1 = 0;
		L2 = 0;
		L3 = 0;
		L4 = 0;
		L5 = 0;
		L6 = 0;
		L7 = 0;
		L8 = 0;
		LoneHot = 1;
	end

	always @(posedge clk) begin
		LoneHot <=  ( L0 && !L1 && !L2 && !L3 && !L4 && !L5 && !L6 && !L7 && !L8) || 
                            (!L0 &&  L1 && !L2 && !L3 && !L4 && !L5 && !L6 && !L7 && !L8) || 
                            (!L0 && !L1 &&  L2 && !L3 && !L4 && !L5 && !L6 && !L7 && !L8) || 
                            (!L0 && !L1 && !L2 &&  L3 && !L4 && !L5 && !L6 && !L7 && !L8) || 
                            (!L0 && !L1 && !L2 && !L3 &&  L4 && !L5 && !L6 && !L7 && !L8) || 
                            (!L0 && !L1 && !L2 && !L3 && !L4 &&  L5 && !L6 && !L7 && !L8) || 
                            (!L0 && !L1 && !L2 && !L3 && !L4 && !L5 &&  L6 && !L7 && !L8) || 
                            (!L0 && !L1 && !L2 && !L3 && !L4 && !L5 && !L6 &&  L7 && !L8) || 
                            (!L0 && !L1 && !L2 && !L3 && !L4 && !L5 && !L6 && !L7 &&  L8); 
		
		if (LoneHot)
		begin
			X <= (L1) ? Y : ((L2) ? ((W != `K0) ? (X + `K1) : X) : X) ;
//			Y <= (L0) ? (Y + 3'd1) : Y ;
			Y  <= Y ;
			Z <= (L0) ? `K0 : (L3) ? `K1 : ((L5) ? ((X != Y) ? `K0 : Z) : Z) ;
			W <= W ;
			
			L0 <= 1'd0 ;
			L1 <= L0 || (L5 && (X != Y)) ;
			L2 <= L1 ;
			L3 <= L2 && (W != `K0) ;
			L4 <= L3 ;
			L5 <= L4 || (L2 && (W == `K0)) ;
			L6 <= L5 && (X == Y) ;
			L7 <= L7 || (L6 && (Z != `K0)) ;
			L8 <= L8 || (L6 && (Z == `K0)) ;
		end

		else
		begin
			X  <= X ;
			Y  <= Y ;
			Z  <= Z ;
			W  <= W ;

			L0 <= L0 ;
			L1 <= L1 ;
			L2 <= L2 ;
			L3 <= L3 ;
			L4 <= L4 ;
			L5 <= L5 ;
			L6 <= L6 ;
			L7 <= L7 ;
			L8 <= L8 ;
		end
	end

	wire prop = !L7 ;
	wire prop_neg = !prop;
	assert property ( prop );
endmodule















