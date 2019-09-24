`define W 3
`define WS 2

module ball2004_1(clk);

	input wire clk;
	reg [`WS:0] X, Y, Z;
	reg L0, L1, L2, L3, L4;
	reg LoneHot;

	initial begin
		L0 = 1;
		L1 = 0;
		L2 = 0;
		L3 = 0;
		L4 = 0;
		LoneHot = 1;
	end

	always @(posedge clk) begin
		LoneHot <=  ( L0 && !L1 && !L2 && !L3 && !L4) || 
                            (!L0 &&  L1 && !L2 && !L3 && !L4) ||
                            (!L0 && !L1 &&  L2 && !L3 && !L4) ||
                            (!L0 && !L1 && !L2 &&  L3 && !L4) ||
                            (!L0 && !L1 && !L2 && !L3 &&  L4) ;
		
                
                X <= X ;
                Y <= Y ;
                Z <= Z ;

		if (LoneHot)
		begin
                    L0 <= 0 ;
                    L1 <= (L0 && (X < Y)) ;
                    L2 <= (L1 && (Y < Z)) ;
                    L3 <= L3 || (L2 && !(X < Z)) ;
                    L4 <= L4 || (L0 && !(X < Y)) || (L1 && !(Y < Z)) || (L2 && (X < Z)) ;
		end

		else
		begin
                        L0 <= L0 ;
			L1 <= L1 ;
			L2 <= L2 ;
			L3 <= L3 ;
			L4 <= L4 ;
		end
	end

	wire prop = !L3 ;
	wire prop_neg = !prop;
	assert property ( prop );
endmodule















