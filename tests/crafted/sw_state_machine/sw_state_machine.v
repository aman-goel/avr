`define W 32
`define WS 31

`define K0 `W'd0
`define K1 `W'd1
`define K2 `W'd2

module sw_state_machine(clk);

	input wire clk;
	reg [`WS:0] S;
	reg X;
	wire inp;
	reg L1, L3, L4, L5, L6, L7, L8, L9, L10;
	reg LoneHot;

	initial begin
		S = `K0;
		X = 0;
		L1 = 1;
		L3 = 0;
		L4 = 0;
		L5 = 0;
		L6 = 0;
		L7 = 0;
		L8 = 0;
		L9 = 0;
		L10 = 0;
		LoneHot = 1;
	end

	always @(posedge clk) begin
		LoneHot <=  ( L1 && !L3 && !L4 && !L5 && !L6 && !L7 && !L8 && !L9 && !L10) || 
                            (!L1 &&  L3 && !L4 && !L5 && !L6 && !L7 && !L8 && !L9 && !L10) || 		
                            (!L1 && !L3 &&  L4 && !L5 && !L6 && !L7 && !L8 && !L9 && !L10) || 		
                            (!L1 && !L3 && !L4 &&  L5 && !L6 && !L7 && !L8 && !L9 && !L10) || 		
                            (!L1 && !L3 && !L4 && !L5 &&  L6 && !L7 && !L8 && !L9 && !L10) || 		
                            (!L1 && !L3 && !L4 && !L5 && !L6 &&  L7 && !L8 && !L9 && !L10) || 		
                            (!L1 && !L3 && !L4 && !L5 && !L6 && !L7 &&  L8 && !L9 && !L10) || 		
                            (!L1 && !L3 && !L4 && !L5 && !L6 && !L7 && !L8 &&  L9 && !L10) || 		
                            (!L1 && !L3 && !L4 && !L5 && !L6 && !L7 && !L8 && !L9 &&  L10) ; 		
		if (LoneHot)
		begin
			S <= (L6) ? (((S == `K0) && X) ? `K1 : S) : (L8) ? (((S == `K1) && !X) ? `K2 : S) : S ;
			X <= (L4) ? ((S < `K2) ? inp : X) : X ;

			L1 <= 1'd0 ;
			L3 <= L1 || L7 || (L8 && !((S == `K1) && !X)) || L9 ;
			L4 <= L3 && (S != `K2 || !X);
			L5 <= L4 && (S < `K2);
			L6 <= L5 || (L4 && !(S < `K2));
			L7 <= L6 && (S == `K0 && X);
			L8 <= L6 && !(S == `K0 && X);
			L9 <= L8 && (S == `K1 && !X);
			L10 <= L10 || (L3 && !(S != `K2 || !X));
		end

		else
		begin
			S  <= S ;
			X  <= X ;
			L1 <= L1 ;
			L3 <= L3 ;
			L4 <= L4 ;
			L5 <= L5 ;
			L6 <= L6 ;
			L7 <= L7 ;
			L8 <= L8 ;
			L9 <= L9 ;
			L10 <= L10 ;
		end
	end

	wire prop = !L10 ;
	wire prop_neg = !prop;
	assert property ( prop );
endmodule















