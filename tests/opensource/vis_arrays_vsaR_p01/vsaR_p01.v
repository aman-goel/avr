/*
*
*	Taken from VIS Benchmarks <ftp://vlsi.colorado.edu/pub/vis/vis-verilog-models-1.3.tar.gz>
*	Modified for YOSYS BTOR Backend <http://www.clifford.at/yosys/>
*	Modified by Ahmed Irfan <irfan@fbk.eu>
*
*/
// Very Simple Architecture 12-bit. Revision A.
//
// Author: Fabio Somenzi <Fabio@Colorado.EDU>

// This very simple microprocessor is vaguely inspired to Hennessy and
// Patterson's DLX. It has been further simplified to make it amenable
// to reachability analysis.
//
// This processor has no pipelining and no interrupts.
// The instruction sets consists of a handful of must-have:
//     LW
//     SW
//     BEQZ
//     ADD(I)  [i.e., both ADD and ADDI]
//     SUB(I)
//     AND
//     OR
//     XOR
//     NOT
//     SRL
//     SRA
//
// All instructions are 12 bits and they have one of two formats (width of
// the fields in parentheses):
//
// R-format: opcode (3) source1 (2) source2 (2) destination (2) function (3)
// I-format: opcode (3) source1 (2) destination (2) immediate (5)
//
// The R-format instructions are: ADD, SUB, AND, OR, XOR, NOT, SRL, and SRA.
// The other instructions are I-format.
//
// There are 3 general-purpose 5-bit registers (R1, R2, R3) that can act as
// source or destinations for the various instructions. R0 is always 0.
//
// All instructions execute in exactly 5 clock cycles.
// The program counter has only 5 bits to reduce the sequential depth
// of the FSM.

module main(clock,PC,instruction,ALUOutput,datain,dataout,wr);
    input	  clock;		// master clock
    output [4:0]  PC;			// instruction cache address
    input [11:0]  instruction;		// intruction cache data
    output [4:0]  ALUOutput;		// data cache address
    input [4:0]   datain;		// data input bus
    output [4:0]  dataout;		// data output bus
    output	  wr;			// memory write

    reg [4:0]	  Registers[0:3];	// register file
    reg [4:0]	  PC;			// program counter
    reg [4:0]	  NPC;			// next program counter
    reg [11:0]	  IR;			// instruction register
    reg [4:0]	  A;			// first ALU operand
    reg [4:0]	  B;			// second ALU operand
    reg [4:0]	  ALUOutput;		// ALU output register
    reg		  Cond;			// comparison result
    reg [4:0]	  LMD;			// load memory data register
    reg [2:0]	  State;		// state for non-pipelined unit
    integer	  i;			// loop index

    // Interesting fields of the instruction register.
    wire [2:0]	  opcode = IR[11:9];
    wire [1:0]	  adFld1 = IR[8:7];
    wire [1:0]	  adFld2 = IR[6:5];
    wire [1:0]	  adFld3 = IR[4:3];
    wire [2:0]	  funFld = IR[2:0];
    wire [4:0]	  immFld = IR[4:0];

    // Control states.
    parameter	  IF = 3'd0,		// instruction fetch
		  ID = 3'd1,		// instruction decode
		  EX = 3'd2,		// execution
		  MEM = 3'd3,		// memory access
		  WB = 3'd4;		// write-back

    // Opcodes.
    parameter	  LW    = 3'd0,
		  SW    = 3'd1,
		  BEQZ  = 3'd2,
		  ALUop = 3'd3,
		  ADDI  = 3'd4,
		  SUBI  = 3'd5;

    // ALU function codes.
    parameter	  ADD = 3'd0,
		  SUB = 3'd1,
		  AND = 3'd2,
		  OR  = 3'd3,
		  XOR = 3'd4,
		  NOT = 3'd5,
		  SRL = 3'd6,
		  SRA = 3'd7;

    // Decoding of the instruction type.
    wire	  memRef = opcode == LW || opcode == SW;
    wire	  regRegALU = opcode == ALUop;
    wire	  regImmALU = opcode == ADDI || opcode == SUBI;
    wire	  branch = opcode == BEQZ;
    // Immediate operand with sign extension.
    wire [4:0]	  Imm = immFld;

    // Combinational outputs.
    assign dataout = B;
    assign wr = (State == MEM) & (opcode == SW);

    // Initial state: all zero.
    initial begin
         for (i = 0; i < 4; i = i + 1)
	    Registers[i] = 0;
	PC = 0;
	NPC = 0;
	IR = 0;
	A = 0;
	B = 0;
	ALUOutput = 0;
	Cond = 0;
	LMD = 0;
        State = 3'd0;
        //State = IF;
    end // initial begin

    always @ (posedge clock) begin
	case (State)
	  IF: begin
	      NPC <= PC + 5'd2;
	      IR <= instruction;
	  end // case: IF
	  ID: begin
	      A <= Registers[adFld1];
	      B <= Registers[adFld2];
	  end // case: ID
	  EX: begin
	      if (memRef) begin
		  ALUOutput <= A + Imm;
	      end // if (memRef)
	      else if (regRegALU) begin
		  if (funFld == ADD)
		      ALUOutput <= A + B;
		  else if (funFld == SUB)
		      ALUOutput <= A - B;
		  else if (funFld == AND)
		      ALUOutput <= A & B;
		  else if (funFld == OR)
		      ALUOutput <= A | B;
		  else if (funFld == XOR)
		      ALUOutput <= A ^ B;
		  else if (funFld == NOT)
		      ALUOutput <= ~A;
		  else if (funFld == SRL)
		      ALUOutput <= {1'd0,A[4:1]};
		  else if (funFld == SRA)
		      ALUOutput <= {A[4],A[4:1]};
	      end // if (regRegALU)
	      else if (regImmALU) begin
		  if (opcode == ADDI)
		      ALUOutput <= A + Imm;
		  else if (opcode == SUBI)
		      ALUOutput <= A - Imm;
	      end // if (regImmALU)
	      else if (branch) begin
		  ALUOutput <= NPC + {Imm[3:0],1'b0};
		  Cond <= A == 0;
	      end // if (branch)
	  end // case: EX
	  MEM: begin
	      if (memRef) begin
		  if (opcode == LW)
		      LMD <= datain;
	      end // if (memRef)
	      if (branch) begin
		  if (Cond)
		      PC <= ALUOutput;
		  else
		      PC <= NPC;
	      end else begin
		  PC <= NPC;
	      end // else: !if(branch)
	  end // case: MEM
	  WB: begin
	      if (regRegALU) begin
		  if (adFld3 != 0)
		      Registers[adFld3] <= ALUOutput;
	      end else if (regImmALU) begin
		  if (adFld2 != 0)
		      Registers[adFld2] <= ALUOutput;
	      end else if (opcode == LW) begin
		  if (adFld2 != 0)
		      Registers[adFld2] <= LMD;
	      end
	  end // case: WB
	endcase // case (State)
	// State update.
	if (State == 3'd4)
	    State <= 3'd0;
	else
	    State <= State + 3'd1;
    end // always @ (posedge clock)

// 	wire IF	= State[2:0]==3'd0;
// 	wire ID	= State[2:0]==3'd1;
// 	wire EXE = State[2:0]==3'd2;
// 	wire MEM = State[2:0]==3'd3;
// 	wire WB	= State[2:0]==3'd4;
	wire R0eqR1 =	Registers[0]==Registers[1];
	wire R0eqR2 =	Registers[0]==Registers[2];
	wire R0eqR3 =	Registers[0]==Registers[3];
	wire R1eqR2 =	Registers[1]==Registers[2];
	wire R1eqR3 =	Registers[1]==Registers[3];
	wire R2eqR3 =	Registers[2]==Registers[3];
	wire AeqR0 =	A[4:0]==Registers[0];
	wire AeqR1 =	A[4:0]==Registers[1];
	wire AeqR2 =	A[4:0]==Registers[2];
	wire AeqR3 =	A[4:0]==Registers[3];
	wire BeqR0 =	B[4:0]==Registers[0];
	wire BeqR1 =	B[4:0]==Registers[1];
	wire BeqR2 =	B[4:0]==Registers[2];
	wire BeqR3 =	B[4:0]==Registers[3];
	wire AeqB =	A[4:0]==B[4:0];

//invariant #FAIL: !(Registers<*1*>[4:2]=3 * Registers<*2*>[4:2]=2 * Registers<*3*>[4:2]=1 *  LMD[4:0]=0 * ALUOutput[4:0]=0 * PC[4:0]=30);
//always begin
wire prop = (	((Registers[1]>=12 && Registers[1]<=15)) &&
				((Registers[2]>=8 && Registers[2]<=11 )) &&
				((Registers[3]>=4 && Registers[3]<=7  )) &&
				LMD==5'd0 && ALUOutput==5'd0 && PC==5'd0			);
//end

	wire prop_neg = !prop;
	assert property ( prop );
// //property: #PASS: The program counter is always aligned on a half-word boundary.
// //G(PC[0]=0 * NPC[0]=0);
// //	assert property (	PC[0]==1'b0 && NPC[0]==1'b0	);
// //property: #PASS: Register R0 is never written.
// //G(Registers<*0*>[4:0]=0);
// //	assert property (	Registers[0]==5'd0	);
// //property : #PASS: The state is between 0 and 4.
// //G(State[2]=0 + State[1:0]=0);
// //	assert property (	State[2]==1'd0 || State[1:0]==2'd0	);
// //property : #PASS: If the two source fields are the same, the ALU input registers
// //# will hold the same value during the EXE, MEM, and WB states.
// //G(adFld1[1:0]==adFld2[1:0] -> (State[2:1]=0 + A[4:0]==B[4:0]));
// //	assert property (	adFld1[1:0]!=adFld2[1:0] || (State[2:1]==2'd0 || A[4:0]==B[4:0])	);
// //property: #PASS: In case of branch, Cond is consistent with A in the MEM and WB states.
// //G(branch=1 * State[2]=1 -> ((Cond=1 -> A[4:0]=0) * (A[4:0]=0 -> Cond=1)));
// //	assert property (	!(branch && State[2]) || ((!Cond || A[4:0]==5'd0) && (A[4:0]!=5'd0 || Cond))	);
// //#PASS: a XOR a = 0.
// //G(regRegALU=1 * funFld[2:0]=b100 * adFld1[1:0]==adFld2[1:0] ->  (State[2]=1 -> ALUOutput[4:0]=0));
// //	assert property (	!(regRegALU && funFld[2:0]==3'b100 && adFld1[1:0]==adFld2[1:0]) || (!State[2] || ALUOutput[4:0]==5'd0)	);
// //property: #PASS: XOR is performed correctly.
// /*G(regRegALU=1 * funFld[2:0]=b100 * 
//   (State[2]=1 + State[1:0]=0 + State[1:0]=3) ->
//    (A[4]==B[4] -> ALUOutput[4]=0) * (ALUOutput[4]=0 -> A[4]==B[4]) *
//    (A[3]==B[3] -> ALUOutput[3]=0) * (ALUOutput[3]=0 -> A[3]==B[3]) *
//    (A[2]==B[2] -> ALUOutput[2]=0) * (ALUOutput[2]=0 -> A[2]==B[2]) *
//    (A[1]==B[1] -> ALUOutput[1]=0) * (ALUOutput[1]=0 -> A[1]==B[1]) *
//    (A[0]==B[0] -> ALUOutput[0]=0) * (ALUOutput[0]=0 -> A[0]==B[0]));*/
// /*	assert property (	!(regRegALU && funFld[2:0]==3'b100 && (State[2]==1'b1 || State[1:0]==2'd0 || State[1:0]==2'd3)) || 
// 				(	(A[4]!=B[4] || ALUOutput[4]==1'b0) && (ALUOutput[4]!=1'b0 || A[4]==B[4]) &&
// 					(A[3]!=B[3] || ALUOutput[3]==1'b0) && (ALUOutput[3]!=1'b0 || A[3]==B[3]) &&
// 					(A[2]!=B[2] || ALUOutput[2]==1'b0) && (ALUOutput[2]!=1'b0 || A[2]==B[2]) &&
// 					(A[1]!=B[1] || ALUOutput[1]==1'b0) && (ALUOutput[1]!=1'b0 || A[1]==B[1]) &&
// 					(A[0]!=B[0] || ALUOutput[0]==1'b0) && (ALUOutput[0]!=1'b0 || A[0]==B[0]) 	)	);
// *///property: #PASS: a OR a = a AND a = a.
// //G(regRegALU=1 * funFld[2:1]=b01 * adFld1[1:0]==adFld2[1:0] ->  (State[2]=1 -> ALUOutput[4:0]==A[4:0]));
// //	assert property (	!(regRegALU && funFld[2:1]==2'b01 && adFld1[1:0]==adFld2[1:0]) || (!State[2] || ALUOutput[4:0]==A[4:0])	);
// //property: #PASS: AND is performed correctly.
// /*G(regRegALU=1 * funFld[2:0]=b010 * 
//   (State[2]=1 + State[1:0]=0 + State[1:0]=3) ->
//    (A[4]=1 * B[4]=1 -> ALUOutput[4]=1) * (ALUOutput[4]=1 -> A[4]=1 * B[4]=1) *
//    (A[3]=1 * B[3]=1 -> ALUOutput[3]=1) * (ALUOutput[3]=1 -> A[3]=1 * B[3]=1) *
//    (A[2]=1 * B[2]=1 -> ALUOutput[2]=1) * (ALUOutput[2]=1 -> A[2]=1 * B[2]=1) *
//    (A[1]=1 * B[1]=1 -> ALUOutput[1]=1) * (ALUOutput[1]=1 -> A[1]=1 * B[1]=1) *
//    (A[0]=1 * B[0]=1 -> ALUOutput[0]=1) * (ALUOutput[0]=1 -> A[0]=1 * B[0]=1));*/
// /*	assert property (	!(regRegALU && funFld[2:0]==3'b010 && (State[2]==1'd1 || State[1:0]==2'd0 || State[1:0]==2'd3)) ||
// 				(	(!(A[4]==1'd1 && B[4]==1'd1) || ALUOutput[4]==1'd1) && (ALUOutput[4]==1'd0 || (A[4]==1'd1 && B[4]==1'd1)) &&
// 					(!(A[3]==1'd1 && B[3]==1'd1) || ALUOutput[3]==1'd1) && (ALUOutput[3]==1'd0 || (A[3]==1'd1 && B[3]==1'd1)) &&
// 					(!(A[2]==1'd1 && B[2]==1'd1) || ALUOutput[2]==1'd1) && (ALUOutput[2]==1'd0 || (A[2]==1'd1 && B[2]==1'd1)) &&
// 					(!(A[1]==1'd1 && B[1]==1'd1) || ALUOutput[1]==1'd1) && (ALUOutput[1]==1'd0 || (A[1]==1'd1 && B[1]==1'd1)) &&
// 					(!(A[0]==1'd1 && B[0]==1'd1) || ALUOutput[0]==1'd1) && (ALUOutput[0]==1'd0 || (A[0]==1'd1 && B[0]==1'd1)) 	)	);
// *///property: #PASS: OR is performed correctly.
// /*G(regRegALU=1 * funFld[2:0]=b011 * 
//   (State[2]=1 + State[1:0]=0 + State[1:0]=3) ->
//    (A[4]=0 * B[4]=0 -> ALUOutput[4]=0) * (ALUOutput[4]=0 -> A[4]=0 * B[4]=0) *
//    (A[3]=0 * B[3]=0 -> ALUOutput[3]=0) * (ALUOutput[3]=0 -> A[3]=0 * B[3]=0) *
//    (A[2]=0 * B[2]=0 -> ALUOutput[2]=0) * (ALUOutput[2]=0 -> A[2]=0 * B[2]=0) *
//    (A[1]=0 * B[1]=0 -> ALUOutput[1]=0) * (ALUOutput[1]=0 -> A[1]=0 * B[1]=0) *
//    (A[0]=0 * B[0]=0 -> ALUOutput[0]=0) * (ALUOutput[0]=0 -> A[0]=0 * B[0]=0));*/
// /*	assert property (	!(regRegALU && funFld[2:0]==3'b011 && (State[2]==1'd1 || State[1:0]==2'd0 || State[1:0]==2'd3)) ||
// 				(	(!(A[4]==1'd0 && B[4]==1'd0) || ALUOutput[4]==1'd0) && (ALUOutput[4]==1'd1 || (A[4]==1'd0 && B[4]==1'd0)) &&
// 					(!(A[3]==1'd0 && B[3]==1'd0) || ALUOutput[3]==1'd0) && (ALUOutput[3]==1'd1 || (A[3]==1'd0 && B[3]==1'd0)) &&
// 					(!(A[2]==1'd0 && B[2]==1'd0) || ALUOutput[2]==1'd0) && (ALUOutput[2]==1'd1 || (A[2]==1'd0 && B[2]==1'd0)) &&
// 					(!(A[1]==1'd0 && B[1]==1'd0) || ALUOutput[1]==1'd0) && (ALUOutput[1]==1'd1 || (A[1]==1'd0 && B[1]==1'd0)) &&
// 					(!(A[0]==1'd0 && B[0]==1'd0) || ALUOutput[0]==1'd0) && (ALUOutput[0]==1'd1 || (A[0]==1'd0 && B[0]==1'd0)) 	)	);
// *///#PASS: a - a = 0.
// //G(regRegALU=1 * funFld[2:0]=b001 * adFld1[1:0]==adFld2[1:0] ->  (State[2]=1 -> ALUOutput[4:0]=0));
// //	assert property (	!(regRegALU && funFld[2:0]==3'b001 && adFld1[1:0]==adFld2[1:0]) || (State[2]==1'd0 || ALUOutput[4:0]==5'd0)	);
// //property: #PASS: In the decode, execute, and memory access states, PC and NPC differ
// /*# exactly by 2.  Hence, if the bit next to the MSB of PC is 0, then the MSBs
// # of PC and NPC must be the same, etc..
// G(State[0]=1 + State[1]=1 ->
//   (PC[1]=0 -> (NPC[4:2]==PC[4:2]) *
//    PC[2]=0 -> (NPC[4:3]==PC[4:3]) *
//    PC[3]=0 -> (NPC[4]==PC[4])));*/
// //	assert property (	!(State[0] || State[1]) || ( (PC[1] || NPC[4:2]==PC[4:2]) && (PC[2] || NPC[4:3]==PC[4:3]) && (PC[3] || NPC[4]==PC[4]) )	);
// //property: #PASS: In case of a taken branch, ALUOutput ends up in the PC.
// //G(State[2]=1 * branch=1 * Cond=1 * !(ALUOutput[4:0]==NPC[4:0]) ->  !(PC[4:0]==NPC[4:0]));
// //	assert property (	!(State[2] && branch && Cond && !(ALUOutput[4:0]==NPC[4:0])) || !(PC[4:0]==NPC[4:0])	);
// //property: #PASS: If no branch is taken, PC and NPC are the same in the WB state.
// //G(State[2]=1 * (branch=0 + Cond=0) -> PC[4:0]==NPC[4:0]);
// //	assert property (	!(State[2] && (!branch || !Cond)) || PC[4:0]==NPC[4:0]	);
// //property: #PASS: Choosing R0 as branch register always leads to a taken branch.
// //G(\WB * branch=1 * adFld1[1:0]=0 -> PC[4:0]==ALUOutput[4:0]);
// //	assert property (	!(WB && branch && adFld1[1:0]==2'd0) || PC[4:0]==ALUOutput[4:0]	);
// //property: #PASS: Since A and B come from the register file, they cannot both be
// /*# different from all registers and different among themselves, because
// # only one of the registers may have been updated since they were fetched.
// #!EF(Registers<*1*>[4:3]=3 * Registers<*2*>[4:3]=2 * Registers<*3*>[4:3]=1 *
// #    A[4:0]=1 * B[4:0]=2);
// G(\R0eqR1 + \R0eqR2 + \R0eqR3 + \R1eqR2 + \R1eqR3 + \R2eqR3 + \AeqR0 +
//   \AeqR1 + \AeqR2 + \AeqR3 + \BeqR0 + \BeqR1 + \BeqR2 + \BeqR3 + \AeqB);*/
// //	assert property (	R0eqR1 || R0eqR2 || R0eqR3 || R1eqR2 || R1eqR3 || R2eqR3 || AeqR0 || AeqR1 || AeqR2 || AeqR3 || BeqR0 || BeqR1 || BeqR2 || BeqR3 || AeqB	);

endmodule // vsaR
