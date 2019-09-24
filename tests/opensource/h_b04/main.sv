// Verilog translation of the original b04 circuit from the ITC99
// benchmark set.

// Author: Fabio Somenzi <Fabio@Colorado.EDU>

module main(RESTART, AVERAGE, ENABLE, DATA_IN, DATA_OUT, CLOCK);
    input        RESTART;
    input 	 AVERAGE;
    input 	 ENABLE;
    input [7:0]  DATA_IN;
    output [7:0] DATA_OUT;
    input 	 CLOCK;

    parameter sA = 0;
    parameter sB = 1;
    parameter sC = 2;

    reg    stato;
    reg [7:0] 	 DATA_OUT;
    reg [7:0] 	 RMAX, RMIN, RLAST, REG1, REG2, REG3, REG4;
    wire [7:0] 	 REGD;
    wire [8:0] 	 temp;

    initial begin
	stato = sA;
      	RMAX = 0;
      	RMIN = 0;
      	RLAST = 0;
      	REG1 = 0;
      	REG2 = 0;
      	REG3 = 0;
      	REG4 = 0;
      	DATA_OUT = 0;
    end

    // Compute the two's complement of an integer.
    function [7:0] tc;
	input [7:0] x;
	begin: _tc
	    tc = (~x) + 8'b1;
	end
    endfunction // tc

    function [7:0] avg;
	input [7:0] x;
	input [7:0] y;
	reg [8:0] tmp;
	reg [7:0] tmp2;
	begin: _avg
	    tmp = {x[7],x} + {y[7],y};
	    tmp2 = tc({1'b0,tmp[6:0]});
	    if (tmp[8])
	      avg = tc({tmp2[7],tmp2[7:1]});
	    else
	      avg = {2'b0,tmp[6:1]};
	end
    endfunction // avg

    // Determine whether x > y assuming the two operands are two's complement
    // integers.
    function signGt;
	input [7:0] x;
	input [7:0] y;
	begin: _signGt;
	    if (!x[7] && y[7])
	      signGt = 1;
	    else if (x[7] && !y[7])
	      signGt = 0;
	    else
	      signGt = x[6:0] > y[6:0];
	end
    endfunction // signGt

    always @ (posedge CLOCK) begin
	case (stato)
	  sA: stato = sB;
	  sB: begin
	      RMAX = DATA_IN;
	      RMIN = DATA_IN;
	      REG1 = 0;
	      REG2 = 0;
	      REG3 = 0;
	      REG4 = 0;
	      RLAST = 0;
	      DATA_OUT = 0;
	      stato = sC;
	  end // case: sB
	  sC: begin
	      if (ENABLE) begin
		  RLAST = DATA_IN;
	      end
	      if (RESTART) begin
		  DATA_OUT = avg(RMAX, RMIN);
	      end else if (ENABLE) begin
		  if (AVERAGE)
		    DATA_OUT = REG4;
		  else
		    DATA_OUT = avg(DATA_IN, REG4);
	      end else begin
		  DATA_OUT = RLAST;
	      end
	      if (signGt(DATA_IN, RMAX)) begin
		  RMAX = DATA_IN;
	      end else if (signGt(RMIN, DATA_IN)) begin
		  RMIN = DATA_IN;
	      end
	      REG4 = REG3;
	      REG3 = REG2;
	      REG2 = REG1;
	      REG1 = DATA_IN;
	      stato = sC;
	  end // case: sC
	endcase // case(stato)
    end // always @ (posedge CLOCK)
//   assert property (RMAX[7]==1 |-> RMIN[7]==1);
//   assert property (!(RMAX[7]==1) || (RMIN[7]==1));
wire prop = (!(RMAX[7]==1) || (RMIN[7]==1));
wire prop_neg = !prop;
assert property ( prop );
endmodule // b04
