// Vending machine that dispenses one item in exchange for 25c.
// The machine accepts nickels, dimes, and quarters.  It gives change if
// it can; otherwise, it returns the coins that were deposited.
//
// Author: Fabio Somenzi <Fabio@Colorado.EDU>

//typedef enum {NONE, NICKEL, DIME, QUARTER} Coin;
//typedef enum {ACCEPTING, CHANGE, REFUND, BEVERAGE} State;

// Generates a random input coin if enable is asserted; otherwise,
// no coin.
module main(clock);
    parameter BITS = 4;

    input 	 clock;
    wire [4:0] balance;

    wire [1:0]   change, nd;
    reg [1:0]    deposit;
    wire 	 beverage, enable;
	wire vending_prop;
   // initial deposit = nd;

    vending #(BITS) v(clock,deposit,change,beverage,enable, vending_prop);

    monitor m(clock,deposit,beverage,change,balance);

    //assign nd = $ND(NONE, NICKEL, DIME, QUARTER);

    always @ (posedge clock) begin
	if (enable)
	  deposit = nd;
	else
	  deposit = NONE;
    end

// Invariant properties
// assert property (v.total[3]==0 || v.total[2:1]==0);
// assert property (v.total[3:0]==8 |-> !(v.l5[2:0]==0));
// assert property (v.total[3:0]==7 |-> (!v.l5[2:0]==0 || !(v.l10[1:0]==0)));

//#PASS: The balance is never negative and never reaches 75c.
//assert property (balance[4]==0 && !balance[4:0]==15);

//#PASS: No more than 45c can be deposited during a transaction.
// assert property (v.total[3]==0 || v.total[2:1]==0);

//#PASS: If in the CHANGE state the total is not 30c or there is at least
//#      one nickel, then a beverage will be released.
//assert property ((v.state==CHANGE && !(v.total[3:0]==6 && v.t5[3:0] == 0)) |-> ##[0:$] v.state==BEVERAGE);

//#PASS: If in the CHANGE state the total is 35c or more, then either a
//#      nickel or a dime has been deposited in the current transaction.
// assert property ((v.state==CHANGE && v.total[3:0]==7 || v.total[3] == 1) |-> !(v.l5[2:0]==0 && v.l10[1:0]==0));

//#PASS: In the REFUND state we have no quarters from this transaction,
//#      and no nickels at all.
// assert property (v.state==REFUND |-> (v.l25[0]==0 && v.l5[2:0]==0 && v.t5[3:0]==0));

//#PASS: On entry to REFUND, we have exactly three dimes from this transaction.
// assert property(!v.state==REFUND |-> ##1(!v.state==REFUND || v.l10[1:0]==3));

/*
#PASS: In the BEVERAGE state we have exactly 25c from this transaction.
#      However, total is not up to date if we borrowed a nickel from the
#      total count to give change out of three dimes.  Hence, total may
#      read either 25c or 30c.*/
// assert property (v.state==BEVERAGE |-> (v.total[3:2]==1 && (v.total[1:0]==1 || v.total[1:0]==2)));

//#PASS: On entry to ACCEPTING, we have no money from this transaction.
//assert property (!v.state==ACCEPTING |-> ##1 (!(v.state==ACCEPTING) || v.total[3:0]==0));


//#PASS: The balance is never negative and never reaches 75c.
// assert property (balance[4]==0 && !balance[4:0]==15);
wire prop = vending_prop;
wire prop_neg = !prop;
assert property ( prop );

endmodule // environment


module vending(clock,deposit,change,beverage,enable, vending_prop);
    parameter      BITS = 4;

    parameter NONE = 2'd0;
    
    parameter ACCEPTING = 2'd0;
    parameter CHANGE = 2'd1;
    parameter REFUND = 2'd2;
    parameter BEVERAGE = 2'd3; 
    
    input 	   clock;
    input  [1:0]	   deposit;	// input coin
    output [1:0] 	   change;	// output coin (change or refund)
    output 	   beverage;	// causes beverage to be released
    output 	   enable;	// coins are only accepted when enable==1

    wire [1:0]     deposit;
    reg [1:0]      change;

    reg [1:0]     state;
    // Total numbers of nickels, dimes, and quarters deposited since reset.
    reg [BITS-1:0] t5, t10, t25;
    // Numbers of nickels, dimes, and quarters deposited in this transaction.
    reg [2:0] 	   l5;
    reg [1:0] 	   l10;
    reg [0:0] 	   l25;

    // Number of nickel-equivalents deposited so far during the
    // current transaction.
    wire [3:0] 	   total;
    
    output vending_prop;

    // #(nickels) + 2 #(dimes) + 5 #(quarters)
    assign total = {1'b0,l5} + {1'b0,l10,1'b0} + {1'b0,l25,1'b0,l25};

    //  Initially the machine has no money and is ready to start a
    // transaction.
    initial begin
	t5 = BITS'd0;
	t10 = BITS'd0;
	t25 = BITS'd0;
	l5 = 3'd0;
	l10 = 2'd0;
	l25 = 1'd0;
	state = ACCEPTING;
	change = NONE;
    end

    assign beverage = (state == BEVERAGE);
    assign enable = (state == ACCEPTING && total < 4'd5);

    always @ (posedge clock) begin
	case (state)
	  ACCEPTING: begin
	      if (total >= 4'd5) begin
		  change = deposit;
		  state = CHANGE;
	      end else begin
		  case (deposit)
		    NICKEL: begin
			if (t5 == {BITS{1'b1}}) begin
			    change = NICKEL;
			end else begin
			    change = NONE;
			    t5 = t5 + BITS'd1;
			    l5 = l5 + 3'd1;
			end
		    end
		    DIME: begin
			if (t10 == {BITS{1'b1}}) begin
			    change = DIME;
			end else begin
			    change = NONE;
			    t10 = t10 + BITS'd1;
			    l10 = l10 + 2'd1;
			end
		    end
		    QUARTER: begin
			if (t25 == {BITS{1'b1}}) begin
			    change = QUARTER;
			end else begin
			    change = NONE;
			    t25 = t25 + BITS'd1;
			    l25 = l25 + 1'd1;
			end
		    end
		    NONE: begin
			change = NONE;
		    end
		  endcase
	      end
	  end
	  // On entry to this state we have between 25c and 45c from the
	  // current transaction.  If we have more than 30c, then we have
	  // at least one quarter, in which case we know we can always
	  // give change.
	  CHANGE: begin
	      if (total == 4'd5) begin
		  change = NONE;
		  state = BEVERAGE;
	      end else if (total == 4'd6) begin
		  if (t5 > BITS'd0) begin
		      change = NICKEL;
		      t5 = t5 - BITS'd1;
		      // Updating l5 here is not strictly necessary because
		      // we are going to reset it in the next state, and in
		      // any case, we do not guarantee that total will be
		      // up to date.
		      state = BEVERAGE;
		  end else begin
		      change = NONE;
		      state = REFUND;
		  end
	      end else begin	// at least 35c
		  if (l10 > 2'd0) begin
		      change = DIME;
		      t10 = t10 - BITS'd1;
		      l10 = l10 - 2'd1;
		  end else begin
		      change = NICKEL;
		      t5 = t5 - BITS'd1;
		      l5 = l5 - 2'd1;
		  end
	      end
	  end
	  BEVERAGE: begin
	      change = NONE;
	      l5 = 3'd0;
	      l10 = 2'd0;
	      l25 = 1'd0;
	      state = ACCEPTING;
	  end
	  // On entry to this state, we have exactly three dimes from
	  // the current transaction, and no nickels at all.
	  REFUND: begin
	      if (l10 > 2'd0) begin
		  l10 = l10 - 2'd1;
		  t10 = t10 - BITS'd1;
		  change = DIME;
	      end else begin
		  state = ACCEPTING;
		  change = NONE;
	      end
	  end
	endcase // case(state)
    end // always @ (posedge clock)

	// Invariant properties
//#PASS: No more than 45c can be deposited during a transaction.
// assert property (total[3]==0 || total[2:1]==0);
// assert property (!(total[3:0]==8) || !(l5[2:0]==0));
// assert property (!(total[3:0]==7) || (!l5[2:0]==0 || !(l10[1:0]==0)));


//#PASS: If in the CHANGE state the total is not 30c or there is at least
//#      one nickel, then a beverage will be released.
//assert property ((v.state==CHANGE && !(v.total[3:0]==6 && v.t5[3:0] == 0)) |-> ##[0:$] v.state==BEVERAGE);

//#PASS: If in the CHANGE state the total is 35c or more, then either a
//#      nickel or a dime has been deposited in the current transaction.
// assert property (!((state==CHANGE && total[3:0]==7 || total[3] == 1)) || !(l5[2:0]==0 && l10[1:0]==0));

//#PASS: In the REFUND state we have no quarters from this transaction,
//#      and no nickels at all.
// assert property (!(state==REFUND) || (l25[0]==0 && l5[2:0]==0 && t5[3:0]==0));

//#PASS: On entry to REFUND, we have exactly three dimes from this transaction.
// assert property(!v.state==REFUND |-> ##1(!v.state==REFUND || v.l10[1:0]==3));

/*
#PASS: In the BEVERAGE state we have exactly 25c from this transaction.
#      However, total is not up to date if we borrowed a nickel from the
#      total count to give change out of three dimes.  Hence, total may
#      read either 25c or 30c.*/
// assert property (!(state==BEVERAGE) || (total[3:2]==1 && (total[1:0]==1 || total[1:0]==2)));

//#PASS: On entry to ACCEPTING, we have no money from this transaction.
//assert property (!v.state==ACCEPTING |-> ##1 (!(v.state==ACCEPTING) || v.total[3:0]==0));

wire prop_1 = (total[3]==1'd0 || total[2:1]==2'd0);
wire prop_2 = (!(total[3:0]==4'd8) || !(l5[2:0]==3'd0));
wire prop_3 = (!(total[3:0]==4'd7) || (!(l5[2:0]==3'd0) || !(l10[1:0]==2'd0)));
wire prop_4 = (!((state==CHANGE && total[3:0]==4'd7 || total[3] == 1'd1)) || !(l5[2:0]==3'd0 && l10[1:0]==2'd0));
wire prop_5 = (!(state==REFUND) || (l25[0]==1'd0 && l5[2:0]==3'd0 && t5[3:0]==4'd0));
wire prop_6 = (!(state==BEVERAGE) || (total[3:2]==2'd1 && (total[1:0]==2'd1 || total[1:0]==2'd2)));
assign vending_prop = prop_1 && prop_2 && prop_3 && prop_4 && prop_5 && prop_6;

endmodule // vending


// This module monitors the balance, that is, the difference between the
// net amount deposited in the machine and the value of the goods received.
module monitor (clock,deposit,beverage,change,balance);
    parameter NICKEL = 2'd1;
    parameter DIME = 2'd2;
    parameter QUARTER = 2'd3;

    input        clock;
    input [1:0]	 deposit;
    input 	     beverage;
    input [1:0]	 change;
    output [4:0] balance;	// from -16 to 15

    wire [1:0]   deposit, change;

    reg [4:0] 	 balance;

    wire [4:0] 	 valD, valC, valB;

    assign valD = (deposit == QUARTER) ? 5'd5 :
	   (deposit == DIME) ? 5'd2 :
	   (deposit == NICKEL) ? 5'd1 : 5'd0;

    assign valC = (change == QUARTER) ? 5'd5 :
	   (change == DIME) ? 5'd2 :
	   (change == NICKEL) ? 5'd1 : 5'd0;

    assign valB = (beverage == 1'd1) ? 5'd5 : 5'd0;

    initial balance = 5'd0;

    always @ (posedge clock) begin
	balance = balance + valD - (valC + valB);
    end

endmodule // monitor
