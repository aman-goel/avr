// Model of a heap.
//
// The heap holds WORDS keys, each of BITS bits ordered in ascending order.
// Keys may repeat.  The key in first position is always a minimum key.
//
// The heap supports 4 operations:
//
// - NOOP: remain idle
// - PUSH: add a key to the heap if it is not full
// - POP : remove the first element from the heap if it is not empty
// - TEST: check the heap property
//
// When ready is asserted, dout gives the minimum value of the keys held
// in the heap.  Commands are accepted only when ready is asserted.
//
// The number of bits in a key is the logarithm of the number
// of slots in the heap, so that all keys may be distinct.

// Author: Fabio Somenzi <Fabio@Colorado.EDU>

//typedef enum {NOOP, PUSH, POP, TEST} Op;
//typedef enum {IDLE, PUSH1, PUSH2, POP1, POP2, POP3, TEST1, TEST2} State;

module main(clock,cmd,din,dout,ready,full,empty,error);
    parameter      BITS = 2;
    parameter 	   WORDS = 4;
    parameter 	   MSW = WORDS-1;
    parameter 	   MSB = BITS-1;
    input 	   clock;
    input [1:0]	   cmd;
    input [MSB:0]  din;
    output [MSB:0] dout;
    output 	   ready;
    output 	   full;
    output 	   empty;
    output 	   error;

    wire [1:0] cmd;
  
  parameter NOOP = 0;
  parameter PUSH = 1;
  parameter POP = 2;
  parameter TEST = 3;
  parameter IDLE = 0;
  parameter PUSH1 = 1;
  parameter PUSH2 = 2;
  parameter POP1 = 3;
  parameter POP2 = 4;
  parameter POP3 = 5;
  parameter TEST1 = 6;
  parameter TEST2 = 7; 

    reg [BITS:0]   nitems, posn;
    reg [MSB:0]    h0, h1, h2;
    reg [MSB:0]    h [0:MSW];
    reg [2:0]     state;
    reg 	   error;
    //reg [BITS:0]  prnt, lft, rght;
    wire [BITS:0]  prnt, lft, rght;
    integer 	   j;

 initial begin
 	state = IDLE;
 	nitems = 0;
	posn = 0;
	h0 = 0;
	h1 = 0;
	h2 = 0;
	error = 0;
	for (j = 0; j < WORDS; j = j+1)
	  h[j] = 0;
 end

    assign dout = h[0];
    assign ready = state == IDLE;
    assign full = nitems == WORDS;
    assign empty = nitems == 0;

    always @ (posedge clock) begin
	case (state)
	  IDLE:
	    case (cmd)
	      PUSH: if (full == 0) begin
		  posn = nitems;
		  h0 = din;
		  nitems = nitems + 1;
		  state = PUSH1;
	      end
	      POP: if (empty == 0) begin
		  nitems = nitems - 1;
		  posn = 0;
		  h0 = h[nitems]; // watch out for the extra bit!
		  h[0] = h0;
		  state = POP1;
	      end
	      TEST: begin
		  posn = 1;
		  error = 0;
		  state = TEST1;
	      end

	      NOOP: ;

	    endcase // case(cmd)

	  PUSH1: begin
	      h1 = h[prnt];
	      state = PUSH2;
	  end

          PUSH2: if (posn == 0 || h1 <= h0) begin
	      h[posn] = h0;
	      state = IDLE;
	  end else begin
	      h[posn] = h1;
	      posn = prnt;
	      state = PUSH1;
	  end

	  POP1: begin
	      h1 = h[lft];
	      state = POP2;
	  end

	  POP2: begin
	      h2 = h[rght];
	      state = POP3;
	  end

	  POP3: begin
	      if (lft < nitems && h1 < h0 &&
		  (rght >= nitems || h1 <= h2)) begin
		  h[posn] = h1;
		  posn = lft;
		  state = POP1;
	      end else if (rght < nitems && h2 < h0) begin
		  h[posn] = h2;
		  posn = rght;
		  state = POP1;
	      end else begin
		  h[posn] = h0;
		  state = IDLE;
	      end
	  end

	  TEST1: if (posn >= nitems) begin
	      state = IDLE;
	  end else begin
	      h1 = h[prnt];
	      state = TEST2;
	  end

	  TEST2: if (h[posn] < h1) begin
	      error = 1;
	      state = IDLE;
	  end else begin
	      posn = posn + 1;
	      state = TEST1;
	  end

	endcase // case(state)
    end
    
    wire [BITS:0] tmp=posn-1;
    assign prnt = {1'b0, tmp[BITS:1]};

    assign lft = {posn[BITS-1:0],1'b0}+1;

    wire [BITS:0] tmp1=posn+1;
    assign rght = {tmp1[BITS-1:0],1'b0};

//#PASS: The heap property is never violated.
//  assert property (error==0);

//#PASS: the number of items is always between 0 and 4.
//  assert property (nitems[2]==0 || nitems[1:0]==0);

wire prop_1 = (error==0);
wire prop_2 = (nitems[2]==0 || nitems[1:0]==0);
wire prop = prop_1 && prop_2;
wire prop_neg = !prop;
assert property ( prop );
endmodule // heap
