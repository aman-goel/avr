// Model of connected Huffman encoder and decoder.
// The alphabet consists of the uppercase letters and the space.
// The Huffman tree used by encoder and decoder is shown below.
// All left branches are labeled 0, and all right branches are labeled 1.
//
//                       +-------------( )---------------+
//                       |                               |
//                       |                               |
//              +-------( )------+               +------( )-----+
//              |                |               |              |
//              |                |               |              |
//        +----( )----+         ( )          +--( )--+         ( )
//        |           |         / \          |       |         / \
//        |           |        |   |         |       |        |   |
//    +--( )--+      ( )      [E] ( )       ( )     ( )      [ ] ( )
//    |       |      / \          / \       / \     / \          / \
//    |       |     |   |        |   |     |   |   |   |        |   |
//   ( )     ( )   [S] ( )      ( ) [A]   [I] [O] [R] [N]      ( ) [T]
//   / \     / \       / \      / \                            / \
//  |   |   |   |     |   |    |   |                          |   |
// [U] [P] [F] [C]   ( ) [L]  [H] ( )                        [D] ( )
//                   / \          / \                            / \
//                  |   |        |   |                          |   |
//            +----( ) [W]      [G] [Y]                        ( ) [M]
//            |      \                                         / \
//            |       |                                       |   |
//           ( )     ( )                                     [B] [V]
//           / \     / \
//          |   |   |   |
//         [Q] ( ) [K] [X]
//             / \
//            |   |
//           [Z] [J]
//
// As an example, the code of W is 001101.
//
// This tree is based on the following assumed frequencies.
//
//  E 130  T 93  N 78  R 77  I 74  O 74  A 73  S 63  D 44
//  H  35  L 35  C 30  F 28  P 27  U 27  M 25  Y 19  G 16
//  W  16  V 13  B  9  X  5  K  3  Q  3  J  2  Z  1
//
// That is, it is assumed that there are 130 Es for every thousand letters.
// It is further assumed that there are 182 spaces for every 1000 letters.
//
// The encoder retrieves the code for each symbol from a map, and shifts it
// out one bit at the time.  The decoder is a finite state machine whose
// state transition graph is obtained from the tree by adding acs from the
// leaves back to the top of the tree.  (To the second level nodes to be
// precise.)  Each node uses ten bits for its encoding.  The code of the root
// is 0.  If a state is not a leaf of the tree, and its encoding is n, then
// the encodings of its two children are 2n+1 and 2n+2.

// Author: Fabio Somenzi <Fabio@Colorado.EDU>
// Modified by: Rajdeep Mukherjee <rajdeep.mukherjee@cs.ox.ac.uk> 
module main(clk, addr);
    input clk;
    input [4:0] addr;

    wire  cipher;
    wire [7:0] character;
    wire [7:0] plain;
    huffmanEnc encoder (clk, addr, cipher, character);

    huffmanDec decoder (clk, cipher, plain);

    // Latch data that we want to refer to in properties.
    reg        ci;
    reg [7:0]  ch;

    initial begin
	ci = 0;
	ch = 0;
    end

    always @ (posedge clk) begin
	ci = cipher;
	ch = character;
    end
    
    
endmodule // main


module huffmanEnc (clk, addr, cipher, character);
    input        clk;
    input [4:0]  addr;
    output 	 cipher;
    output [7:0] character;

    reg [7:0] 	 character;
    reg [9:0] shiftreg;

    always @ (posedge clk) begin
	if (shiftreg[9:1] == 1) begin
	    character = addr < 26 ? 
	      65 + {3'b0, addr} : 32;
	    shiftreg = (character == 69)? 10'b0000001010: 
	      character == 32 ? 10'b0000001011: // space
	      character == 83 ? 10'b0000010100: // S
	      character == 65 ? 10'b0000011110:
	      character == 73 ? 10'b0000010001: 
	      character == 79 ? 10'b0000011001:
	      character == 82 ? 10'b0000010101: // R
	      character == 78 ? 10'b0000011101:
        character == 84 ? 10'b0000011111:
	      character == 85 ? 10'b0000100000:
	      character == 80 ? 10'b0000110000:
	      character == 70 ? 10'b0000101000:
	      character == 67 ? 10'b0000111000: // C
	      character == 76 ? 10'b0000111100: // L
	      character == 72 ? 10'b0000100110: // H
	      character == 68 ? 10'b0000100111: // D
	      character == 87 ? 10'b0001101100: // W
	      character == 71 ? 10'b0001010110: // G
	      character == 89 ? 10'b0001110110: // Y
	      character == 77 ? 10'b0001110111: // M
	      character == 66 ? 10'b0010010111: // B
	      character == 86 ? 10'b0011010111: // V
	      character == 81 ? 10'b0100001100: // Q
	      character == 75 ? 10'b0101001100: // K
	      character == 88 ? 10'b0111001100: // X
	      character == 90 ? 10'b1010001100: // Z
	      character == 74 ? 10'b1110001100: // J
	      10'b0;
	end else begin
	    shiftreg = {1'b0, shiftreg[9:1]}; // shift right
	end
    end
    assign cipher = shiftreg[0];
/*
######################################################################
# Properties of the encoder.
######################################################################

####################################################
#### Pass: The encoder shift register is never zero.
#################################################### */

//assert property (!shiftreg[9:0] == 0 |-> !(shiftreg[9:0]==0));
// assert property ((shiftreg[9:0] == 0) || (!(shiftreg[9:0]==0)));

wire prop = ((shiftreg[9:0] == 0) || (!(shiftreg[9:0]==0)));
wire prop_neg = !prop;
assert property ( prop );

endmodule // huffmanEnc


// The output plain is 0 except for one clock cycle when a character has
// been decoded.
module huffmanDec (clk,cipher,plain);
    input        clk;
    input 	 cipher;
    output [7:0] plain;
    reg [9:0] 	 state;
	    
    wire 	 leaf;
    wire [7:0] 	 character;

    initial state = 0;

    // This function maps states to characters.  All non-leaf states are
    // mapped to NUL.  The leaf states are mapped to the ASCII code of the
    // corresponding symbol.
 /*   function [7:0] map;
	input [9:0] state;
	begin: _map
	    case (state)
	        9: map = 69; // E
	       13: map = 32; // space
	       17: map = 83; // S
	       22: map = 65; // A
	       23: map = 73; // I
	       24: map = 79; // O
	       25: map = 82; // R
	       26: map = 78; // N
               30: map = 84; // T
	       31: map = 85; // U
	       32: map = 80; // P
	       33: map = 70; // F
	       34: map = 67; // C
	       38: map = 76; // L
	       43: map = 72; // H
	       59: map = 68; // D
	       76: map = 87; // W
	       89: map = 71; // G
	       90: map = 89; // Y
	      122: map = 77; // M
	      243: map = 66; // B
	      244: map = 86; // V
	      303: map = 81; // Q
	      305: map = 75; // K
	      306: map = 88; // X
	      609: map = 90; // Z
	      610: map = 74; // J
	      default: map = 0;
	    endcase // case(state)
	end // block: _map
    endfunction // map
 */
    assign plain = (state == 9)?69: (state==13)?32: (state==17)?83: (state==22)?65:
    (state==23)?73: (state==24)?79: (state==25)?82: (state==26)?78: (state==30)?84:
    (state==31)?85: (state==32)?80: (state==33)?70: (state==34)?67: (state==38)?76:
    (state==43)?72: (state==59)?68: (state==76)?87: (state==89)?71: (state==90)?89:
    (state==122)?77: (state==243)?66: (state==244)?86: (state==303)?81: (state==305)?75:
    (state==306)?88: (state==609)?90: (state==610)?74:0;
    
    assign leaf = plain != 0;

    always @ (posedge clk) begin
	state = (leaf ? 0 : {state[8:0],1'b0}) + (cipher ? 2 : 1);
    end
/*  
######################################################################
# Properties of the decoder.
######################################################################
*/
//#PASS: The all-zero state is never re-entered.
//assert property  (state[9:0] == 0 |-> ##1 !(state[9:0]==0));
/* #####################################
#### Pass: The outputs is never 255.
###################################### */
// assert property (!(plain[7:0]==255));

endmodule // huffmanDec
