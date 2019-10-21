`define W 8
`define WS 7

module ball2004_2(clk);

	input wire clk;
	reg [`WS:0] X, Y, Z, A, B;
	reg L0, L1, L2, L3, L4, L5, L1w, L11, L12;
        reg t1;
	reg LoneHot;

	initial begin
		t1 = 0;

		L0 = 1;
		L1 = 0;
		L2 = 0;
		L3 = 0;
		L4 = 0;
		L5 = 0;
		L1w = 0;
		L11 = 0;
		L12 = 0;
		LoneHot = 1;
	end

	always @(posedge clk) 
	begin
		LoneHot <=  ( L0 && !L1 && !L2 && !L3 && !L4 && !L5 && !L1w && !L11 && !L12) || 
                            (!L0 &&  L1 && !L2 && !L3 && !L4 && !L5 && !L1w && !L11 && !L12) || 
                            (!L0 && !L1 &&  L2 && !L3 && !L4 && !L5 && !L1w && !L11 && !L12) || 
                            (!L0 && !L1 && !L2 &&  L3 && !L4 && !L5 && !L1w && !L11 && !L12) || 
                            (!L0 && !L1 && !L2 && !L3 &&  L4 && !L5 && !L1w && !L11 && !L12) || 
                            (!L0 && !L1 && !L2 && !L3 && !L4 &&  L5 && !L1w && !L11 && !L12) || 
                            (!L0 && !L1 && !L2 && !L3 && !L4 && !L5 &&  L1w &&  L11 && !L12) || 
                            (!L0 && !L1 && !L2 && !L3 && !L4 && !L5 &&  L1w && !L11 &&  L12) || 
                            (!L0 && !L1 && !L2 && !L3 && !L4 && !L5 &&  L1w && !L11 && !L12) ;
		
		if (LoneHot)
		begin
                    X <= X ;
                    Y <= Y ;
                    Z <= (L12) ? B : Z ;
                    B <= B ;
                    A <= L2 ? Y : A ;
                    t1 <= (L12) ? 1'd1 : t1 ;

                    L0 <= 1'd0 ;
                    L1 <= L0 ;
                    L2 <= (L1 && (X < Y)) ;
                    L3 <= (L1w && t1) ;
                    L4 <= L4 || (L3 && !(X < Z)) ;
                    L5 <= L5 || (L1 && !(X < Y)) || (L3 && (X < Z)) || (L11 && !(A < B)) ;

                    L1w <= L2 || L12 || (L1w && !t1) ;
                    L11 <= L2 ;
                    L12 <= (L11 && (A < B)) ;
		end

		else
		begin
                    X <= X ;
                    Y <= Y ;
                    Z <= Z ;
                    B <= B ;
                    A <= A ;
                    t1 <= t1 ;

                    L0 <= L0 ;
                    L1 <= L1 ;
                    L2 <= L2 ;
                    L3 <= L3 ;
                    L4 <= L4 ;
                    L5 <= L5 ;
                    L1w <= L1w ;
                    L11 <= L11 ;
                    L12 <= L12 ;
		end
	end

	wire prop = !L4 ;
	wire prop_neg = !prop;
	assert property ( prop );
endmodule















