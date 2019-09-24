`define W 8
`define WS 7

module sym_ex(clk, a, b, c);

	input wire clk;
	reg [`WS:0] X, Y, Z;
        input wire  [`WS:0]  a, b, c ;
        reg L0, L1, L2, L3, L4, L5, L6, L7;
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
                X  = `W'd0;
                Y  = `W'd0;
                Z  = `W'd0;
		LoneHot = 1;
	end

	always @(posedge clk) begin
		LoneHot <=  ( L0 && !L1 && !L2 && !L3 && !L4 && !L5 && !L6 && !L7) || 
                            (!L0 &&  L1 && !L2 && !L3 && !L4 && !L5 && !L6 && !L7) || 
                            (!L0 && !L1 &&  L2 && !L3 && !L4 && !L5 && !L6 && !L7) || 
                            (!L0 && !L1 && !L2 &&  L3 && !L4 && !L5 && !L6 && !L7) || 
                            (!L0 && !L1 && !L2 && !L3 &&  L4 && !L5 && !L6 && !L7) || 
                            (!L0 && !L1 && !L2 && !L3 && !L4 &&  L5 && !L6 && !L7) || 
                            (!L0 && !L1 && !L2 && !L3 && !L4 && !L5 &&  L6 && !L7) || 
                            (!L0 && !L1 && !L2 && !L3 && !L4 && !L5 && !L6 &&  L7) ;
		
		if (LoneHot)
		begin
                    X <= (L1) ? (a != `W'd0) ? `W'd3 : X : X ;
                    Y <= (L3) ? ((a == `W'd0) && (c != `W'd0)) ? `W'd2 : Y : Y ;
                    Z <= (L4) ? `W'd2 : Z ;
                    
                    L0 <= 1'd0 ;
                    L1 <= L0 ;
                    L2 <= L1 ;
                    L3 <= (L2 && (b < `W'd5)) ;
                    L4 <= L3 ;
                    L5 <= L4 || (L2 && !(b < `W'd5));
                    L6 <= (L6 || (L5 && ((X + Y) != `W'd4))) ;
                    L7 <= (L7 || (L5 && ((X + Y) == `W'd4))) ;
		end

		else
		begin
			X  <= X ;
			Y  <= Y ;
			Z  <= Z ;

			L0 <= L0 ;
			L1 <= L1 ;
			L2 <= L2 ;
			L3 <= L3 ;
			L4 <= L4 ;
			L5 <= L5 ;
			L6 <= L6 ;
			L7 <= L7 ;
		end
	end

	wire prop = !L7 ;
	wire prop_neg = !prop;
	assert property ( prop );
endmodule















