
/* A simple 4 bit non pipelined microprocessor                       */
/* by Adnan Aziz Nov 1995                                            */
/*                                                                   */
/* 8 registers, program is in stored in ROM                          */
/*                                                                   */
/* Instructions are of two type - alu operation and conditional jump */
/* The first kind look like OP src_reg1, src_reg2, destn_reg         */
/* The second are like JMP r1 r2: if the contents of r1 is zero,     */
/* set the pc to the contents of r2                                  */
/*                                                                   */
/* In this way the instruction is 11 bits wide - 2 for the opcode,   */
/* 3 for src_reg1, 3 for src_reg2, and 3 for destn_reg               */
/*                                                                   */
/* As you might expect, programming such a processor is a royal pain */
/* Perhaps we will write an assembler for it someday.                */
/*                                                                   */
/* Possible extensions - pipeline and add bypass/stall logic, add    */
/* operands.                                                         */

// Modified by Rajdeep Mukherjee <rajdeep.mukherjee@cs.ox.ac.uk>

// `define ADD 0
// `define JMP 1
// `define AND 2
// `define XOR 3
`define ADD 0
`define JMP 4
`define AND 2
`define XOR 6

`define INSTR 11
`define OPCODE 2
`define DATA_ADDR 2
`define PROG_ADDR 2
`define DATA 4

module main( clk );
input clk;

// wire[0:`DATA] aluOut;
// wire[0:`DATA] memOut1;
// wire[0:`DATA] memOut2;
// wire[0:`DATA_ADDR] readLoc1;
// wire[0:`DATA_ADDR] readLoc2;
// wire[0:`INSTR] instruction;
// wire[0:`OPCODE] opcode;
// wire [0:`DATA_ADDR] writeLoc;
// wire [0:`PROG_ADDR] progCntr;
wire[`DATA:0] aluOut;
wire[`DATA:0] memOut1;
wire[`DATA:0] memOut2;
wire[`DATA_ADDR:0] readLoc1;
wire[`DATA_ADDR:0] readLoc2;
wire[`INSTR:0] instruction;
wire[`OPCODE:0] opcode;
wire [`DATA_ADDR:0] writeLoc;
wire [`PROG_ADDR:0] progCntr;


	memory M( clk, opcode, readLoc1, readLoc2, writeLoc, aluOut, memOut1, memOut2 );
	program P( clk, progCntr, instruction );

	decodeOpcd Opcode( clk, instruction, opcode );
	decodeLoc1 Loc1( clk, instruction, readLoc1 );
	decodeLoc2 Loc2( clk, instruction, readLoc2 );
	decodeLoc3 Loc3( clk, instruction, writeLoc );

	alu ALU( clk, opcode, memOut1, memOut2, aluOut );

 	pc PC( clk, opcode, memOut1, memOut2, progCntr );

//   assert property	(!((opcode == `JMP) && (memOut1 == 0)) && (progCntr == memOut2[0:2]));
// wire prop =	(!((opcode == `JMP) && (memOut1 == 0)) && (progCntr == memOut2[0:2]));
wire prop =	(!((opcode == `JMP) && (memOut1 == 0)) && (progCntr == memOut2[2:0]));
wire prop_neg = !prop;
assert property ( prop );
endmodule

/* reg  file */

module 
memory( clk, opcode, readLoc1, readLoc2, writeLoc, data, memOut1, memOut2 );
     
input clk;
// input[0:`OPCODE]  opcode;
// input[0:`DATA_ADDR]    readLoc1;
// input[0:`DATA_ADDR]    readLoc2;
// input[0:`DATA_ADDR]    writeLoc;
// input[0:`DATA]    data;
// output[0:`DATA]   memOut1;
// output[0:`DATA]   memOut2;
// 
// wire [0:`DATA] memOut1;
// wire [0:`DATA] memOut2;
// 
// reg [0:`DATA] m0;
// reg [0:`DATA] m1;
// reg [0:`DATA] m2;
// reg [0:`DATA] m3;
// reg [0:`DATA] m4;
// reg [0:`DATA] m5;
// reg [0:`DATA] m6;
// reg [0:`DATA] m7;
input[`OPCODE:0]  opcode;
input[`DATA_ADDR:0]    readLoc1;
input[`DATA_ADDR:0]    readLoc2;
input[`DATA_ADDR:0]    writeLoc;
input[`DATA:0]    data;
output[`DATA:0]   memOut1;
output[`DATA:0]   memOut2;

wire [`DATA:0] memOut1;
wire [`DATA:0] memOut2;

reg [`DATA:0] m0;
reg [`DATA:0] m1;
reg [`DATA:0] m2;
reg [`DATA:0] m3;
reg [`DATA:0] m4;
reg [`DATA:0] m5;
reg [`DATA:0] m6;
reg [`DATA:0] m7;

initial begin m0 = 1; end
initial begin m1 = 0; end
initial begin m2 = 0; end
initial begin m3 = 0; end
initial begin m4 = 0; end
initial begin m5 = 0; end
initial begin m6 = 0; end
initial begin m7 = 0; end

assign memOut1 = (readLoc1 == 0) ? m0 :
				  (readLoc1 == 1) ? m1 :
				   (readLoc1 == 2) ? m2 :
				    (readLoc1 == 3) ? m3 :
				     (readLoc1 == 4) ? m5 :
				      (readLoc1 == 5) ? m5 :
				       (readLoc1 == 6) ? m6 : m7;

assign memOut2 = (readLoc2 == 0) ? m0 :
				  (readLoc2 == 1) ? m1 :
				   (readLoc2 == 2) ? m2 :
				    (readLoc2 == 3) ? m3 :
				     (readLoc2 == 4) ? m5 :
				      (readLoc2 == 5) ? m5 :
				       (readLoc2 == 6) ? m6 : m7;
				   
     always @(posedge clk) 
          begin
            if (opcode != `JMP)
              begin
				if (writeLoc == 0 )
				  begin
					m0 = data;
				  end
				if (writeLoc == 1 )
				  begin
					m1 = data;
				  end
				if (writeLoc == 2 )
				  begin
					m2 = data;
				  end
				if (writeLoc == 3 )
				  begin
					m3 = data;
				  end
				if (writeLoc == 4 )
				  begin
					m4 = data;
				  end
				if (writeLoc == 5 )
				  begin
					m5 = data;
				  end
				if (writeLoc == 6 )
				  begin
					m6 = data;
				  end
				if (writeLoc == 7 )
				  begin
					m7 = data;
				  end
			  end
          end

endmodule               
   
/* rom containing program */

module 
program( clk, progCntr, instruction );

     input  clk;
//      input[0:`PROG_ADDR] progCntr;
//      output[0:`INSTR] instruction;
// 
// 	 wire[0:`INSTR] instr0;
// 	 wire[0:`INSTR] instr1;
// 	 wire[0:`INSTR] instr2;
// 	 wire[0:`INSTR] instr3;
// 	 wire[0:`INSTR] instr4;
// 	 wire[0:`INSTR] instr5;
// 	 wire[0:`INSTR] instr6;
// 	 wire[0:`INSTR] instr7;
     input[`PROG_ADDR:0] progCntr;
     output[`INSTR:0] instruction;

	 wire[`INSTR:0] instr0;
	 wire[`INSTR:0] instr1;
	 wire[`INSTR:0] instr2;
	 wire[`INSTR:0] instr3;
	 wire[`INSTR:0] instr4;
	 wire[`INSTR:0] instr5;
	 wire[`INSTR:0] instr6;
	 wire[`INSTR:0] instr7;

// 	 // assign instr0 = 12'b001_001_000_000;
// 	 assign instr0 = 576;
// 	 //assign instr1 = 12'b010_010_000_000;
// 	 assign instr1 = 1152;
// 	 //assign instr2 = 12'b011_011_000_000;
// 	 assign instr2 = 1728;
// 	 //assign instr3 = 12'b100_100_000_000;
// 	 assign instr3 = 2304;
// 	 //assign instr4 = 12'b000_011_111_001;
// 	 assign instr4 = 505;
// 	 //assign instr5 = 12'b001_001_000_000;
// 	 assign instr5 = 0;
// 	 //assign instr6 = 12'b000_000_100_100;
// 	 assign instr6 = 0;
// 	 //assign instr7 = 12'b000_000_100_100;
// 	 assign instr7 = 0;

// 	 // assign instr0 = 12'b000_000_100_100;
// 	 assign instr0 = 36;
// 	 //assign instr1 = 12'b000_000_010_010;
// 	 assign instr1 = 18;
// 	 //assign instr2 = 12'b000_000_110_110;
// 	 assign instr2 = 54;
// 	 //assign instr3 = 12'b000_000_001_001;
// 	 assign instr3 = 9;
// 	 //assign instr4 = 12'b100_111_111_000;
// 	 assign instr4 = 2552;
// 	 //assign instr5 = 12'b000_000_000_000;
// 	 assign instr5 = 0;
// 	 //assign instr6 = 12'b000_000_000_000;
// 	 assign instr6 = 0;
// 	 //assign instr7 = 12'b000_000_000_000;
// 	 assign instr7 = 0;
	 
	 // assign instr0 = 12'b000_000_100_100;
	 assign instr0 = 36;
	 //assign instr1 = 12'b000_000_010_010;
	 assign instr1 = 18;
	 //assign instr2 = 12'b000_000_110_110;
	 assign instr2 = 54;
	 //assign instr3 = 12'b000_000_001_001;
	 assign instr3 = 9;
	 //assign instr4 = 12'b100_111_110_000;
	 assign instr4 = 2544;
	 //assign instr5 = 12'b000_000_100_100;
	 assign instr5 = 36;
	 //assign instr6 = 12'b001_001_000_000;
	 assign instr6 = 576;
	 //assign instr7 = 12'b001_001_000_000;
	 assign instr7 = 576;
	 
	 assign instruction =  (progCntr == 0) ? instr0 :
							(progCntr == 1) ? instr1 :
							 (progCntr == 2) ? instr2 :
							  (progCntr == 3) ? instr3 :
							   (progCntr == 4) ? instr4 :
								(progCntr == 5) ? instr5 :
								 (progCntr == 6) ? instr6 : instr7;

endmodule

/* split instruction; this gets opcode */
module 
decodeOpcd( clk, instruction, opcode );
	
	input  clk;
// 	input[0:`INSTR] instruction;
// 	output[0:`OPCODE] opcode;
	input[`INSTR:0] instruction;
	output[`OPCODE:0] opcode;

// 	assign opcode = instruction[0:2];
	assign opcode = instruction[2:0];

endmodule


/* split instruction; this gets src_reg1 */
module 
decodeLoc1( clk, instruction, readLoc1 );
	
	input  clk;
// 	input[0:`INSTR] instruction;
// 	output[0:`DATA_ADDR] readLoc1;
	input[`INSTR:0] instruction;
	output[`DATA_ADDR:0] readLoc1;

// 	assign readLoc1 = instruction[3:5];
	assign readLoc1 = instruction[5:3];

endmodule

/* split instruction; this gets src_reg2 */
module 
decodeLoc2( clk, instruction, readLoc2 );
	
	input  clk;
// 	input[0:`INSTR] instruction;
// 	output[0:`DATA_ADDR] readLoc2;
	input[`INSTR:0] instruction;
	output[`DATA_ADDR:0] readLoc2;

// 	assign readLoc2 = instruction[6:8];
	assign readLoc2 = instruction[8:6];

endmodule

/* split instruction; this gets destn_reg1 */
module 
decodeLoc3( clk, instruction, writeLoc );
	
	input  clk;
// 	input[0:`INSTR] instruction;
// 	output[0:`DATA_ADDR] writeLoc;
	input[`INSTR:0] instruction;
	output[`DATA_ADDR:0] writeLoc;

// 	assign writeLoc = instruction[9:11];
	assign writeLoc = instruction[11:9];

endmodule

/* 4 instruction alu */
module
alu( clk, opcode, operand1, operand2, aluOut );

	input clk;
// 	input[0:`OPCODE] opcode;
// 	input[0:`DATA] operand1;
// 	input[0:`DATA] operand2;
// 	output[0:`DATA] aluOut;
	input[`OPCODE:0] opcode;
	input[`DATA:0] operand1;
	input[`DATA:0] operand2;
	output[`DATA:0] aluOut;

assign aluOut = (opcode == `ADD) ? (operand1 + operand2) :
                 (opcode == `XOR) ? (operand1^operand2) :
				  (opcode == `AND) ? (operand1 & operand2) : 0;
endmodule

/* program counter - increment by one unless jmp */
module 
pc( clk, opcode, operand1, operand2, progCntr );
  
	input clk;
// 	input[0:`OPCODE] opcode;
// 	input[0:`DATA]  operand1;
// 	input[0:`DATA]  operand2;
// 	output[0:`PROG_ADDR] progCntr;
// 
// 	reg[0:`PROG_ADDR] progCntr;
	input[`OPCODE:0] opcode;
	input[`DATA:0]  operand1;
	input[`DATA:0]  operand2;
	output[`PROG_ADDR:0] progCntr;

	reg[`PROG_ADDR:0] progCntr;
	initial
	  begin 
		progCntr = 0;
	  end
	
    always @(posedge clk) 
	  begin
		if ( (opcode == `JMP) && (operand1 == 0) )
		  begin 
// 		    progCntr = operand2[0:2];
		    progCntr = operand2[2:0];
          end
		else 
		  begin
			progCntr = progCntr + 1;
		  end
	  end

endmodule

