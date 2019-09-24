// This model of a tic-tac-toe player accepts moves on input "imove," and,
// if they are legal, executes them.  A move is legal if it specifies an empty
// cell of the game board.  There are two players, X and O.  Initially, X
// moves.Every time a legal move is executed, the turn passes to the other
// player.  Once the game is finished, either with a win ora tie, no further
// moves are allowed.
//
// Author: Fabio Somenzi <Fabio@Colorado.EDU>
// Modified by: Rajdeep Mukherjee <rajdeep.mukherjee@cs.ox.ac.uk>

//typedef enum {EMPTY, X, O} content;

module main(clock,imove,winX,winO,finished);
    input       clock;
    input [3:0] imove;
    output 	winX, winO, finished;

    //                  0 | 1 | 2
    //                 ---+---+---
    // The game board:  3 | 4 | 5
    //                 ---+---+---
    //                  6 | 7 | 8

    parameter EMPTY = 2'd0;
    parameter X = 2'd1;
    parameter O = 2'd2;

    reg [1:0] b[0:8];
    reg [1:0] turn;
    reg [3:0]	move;
    integer 	i;

    initial begin
	for (i = 0; i < 9; i = i + 1)
	  b[i] = EMPTY;
	turn = X;
	move = 4'd0;
    end

    always @ (posedge clock) begin
	move = (imove < 4'd9) ? imove : 4'd0;
	if (!finished && b[move] == EMPTY) begin
	    b[move] = turn;
	    turn = (turn == X) ? 2'd0 : X;
	end
    end

    assign winX = b[0]==X & (b[1]==X & b[2]==X | b[3]==X & b[6]==X) |
	   b[8]==X & (b[7]==X & b[6]==X | b[5]==X & b[2]==X) |
	   b[4]==X & (b[0]==X & b[8]==X | b[2]==X & b[6]==X |
		      b[1]==X & b[7]==X | b[3]==X & b[5]==X);

    assign winO = b[0]==O & (b[1]==O & b[2]==O | b[3]==O & b[6]==O) |
	   b[8]==O & (b[7]==O & b[6]==O | b[5]==O & b[2]==O) |
	   b[4]==O & (b[0]==O & b[8]==O | b[2]==O & b[6]==O |
		      b[1]==O & b[7]==O | b[3]==O & b[5]==O);

    assign finished = winX | winO |
	   b[0]!=EMPTY & b[1]!=EMPTY & b[2]!=EMPTY &
	   b[3]!=EMPTY & b[4]!=EMPTY & b[5]!=EMPTY &
	   b[6]!=EMPTY & b[7]!=EMPTY & b[8]!=EMPTY;

// assert property ((move[3]==0) || (move[2:0]==0));
// assert property (!(winX==1 && winO==1));
// assert property (!(b[0]==X && b[1]==X && b[2]==X) || (winX==1)); // top row
// assert property (!(b[0]==O && b[1]==O && b[2]==O) || (winO==1));
// assert property (!(b[3]==X && b[4]==X && b[5]==X) || (winX==1)); // middle row
// assert property (!(b[3]==O && b[4]==O && b[5]==O) || (winO==1)); 
// assert property (!(b[6]==X && b[7]==X && b[8]==X) || (winX==1)); // bottom row
// assert property (!(b[6]==O && b[7]==O && b[8]==O) || (winO==1)); 
 
wire prop_1 = ((move[3]==1'd0) || (move[2:0]==3'd0));
wire prop_2 = (!(winX==1'd1 && winO==1'd1));
wire prop_3 = (!(b[0]==X && b[1]==X && b[2]==X) || (winX==1'd1)); // top row
wire prop_4 = (!(b[0]==O && b[1]==O && b[2]==O) || (winO==1'd1));
wire prop_5 = (!(b[3]==X && b[4]==X && b[5]==X) || (winX==1'd1)); // middle row
wire prop_6 = (!(b[3]==O && b[4]==O && b[5]==O) || (winO==1'd1)); 
wire prop_7 = (!(b[6]==X && b[7]==X && b[8]==X) || (winX==1'd1)); // bottom row
wire prop_8 = (!(b[6]==O && b[7]==O && b[8]==O) || (winO==1'd1)); 

wire prop = prop_1 && prop_2 && prop_3 && prop_4 && prop_5 && prop_6 && prop_7 && prop_8;
wire prop_neg = !prop;
assert property ( prop );
endmodule // ticTacToe
