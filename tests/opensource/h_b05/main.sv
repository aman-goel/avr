// Verilog translation of the original b05 circuit from the ITC99
// benchmark set.

// Author: Fabio Somenzi <Fabio@Colorado.EDU>

module main(CLOCK, START, SIGN, DISPMAX1, DISPMAX2, DISPMAX3,
	   DISPNUM1, DISPNUM2);
    input        CLOCK;
    input 	 START;
    output 	 SIGN;
    output [6:0] DISPMAX1, DISPMAX2, DISPMAX3;
    output [6:0] DISPNUM1, DISPNUM2;

    parameter st0 = 3'd0;
    parameter st1 = 3'd1;
    parameter st2 = 3'd2;
    parameter st3 = 3'd3;
    parameter st4 = 3'd4;
    reg [2:0]   STATO;
    wire [8:0] 	 mem_mar, AC1, AC2;
    reg [4:0] 	 MAR, NUM;
    reg [8:0] 	 TEMP, MAX;
    reg 	 FLAG, EN_DISP, RES_DISP;
    wire 	 MAG1, MAG2, MIN1;

    function [8:0] MEM;
	input [4:0] a;
	begin: _MEM
	    if      (a ==  0) MEM =  50;
	    else if (a ==  1) MEM =  40;
	    else if (a ==  2) MEM =   0;
	    else if (a ==  3) MEM = 229;
	    else if (a ==  4) MEM = 502; // -10
	    else if (a ==  5) MEM =  75;
	    else if (a ==  6) MEM = 229;
	    else if (a ==  7) MEM = 181;
	    else if (a ==  8) MEM = 186;
	    else if (a ==  9) MEM = 229;
	    else if (a == 10) MEM = 186;
	    else if (a == 11) MEM = 501; // -11
	    else if (a == 12) MEM =   0;
	    else if (a == 13) MEM =  40;
	    else if (a == 14) MEM =  50;
	    else if (a == 15) MEM = 483; // -29
	    else if (a == 16) MEM = 494; // -18
	    else if (a == 17) MEM = 229;
	    else if (a == 18) MEM = 229;
	    else if (a == 19) MEM = 151;
	    else if (a == 20) MEM = 229;
	    else if (a == 21) MEM = 100;
	    else if (a == 22) MEM = 125;
	    else if (a == 23) MEM =  10;
	    else if (a == 24) MEM =  75;
	    else if (a == 25) MEM = 462; // -50
	    else if (a == 26) MEM =   0;
	    else if (a == 27) MEM = 490; // -22
	    else if (a == 28) MEM =   0;
	    else if (a == 29) MEM =  40;
	    else if (a == 30) MEM =  50;
	    else              MEM =  50;
	end
    endfunction // MEM

    initial begin
	STATO = st0;
	RES_DISP = 0;
	EN_DISP = 0;
	NUM = 0;
	MAR = 0;
	TEMP = 0;
	MAX = 0;
	FLAG = 0;
    end

    assign mem_mar = MEM(MAR);
    assign AC1 = mem_mar - TEMP;
    assign AC2 = mem_mar - MAX;
    assign MIN1 = AC1[8];
    assign MAG1 = !AC1[8] && (AC1[7:0] != 0);
    assign MAG2 = AC2[8];
    assign SIGN = ~EN_DISP && (~RES_DISP || MAX[8]);
    assign DISPMAX1 = cDISPMAX1(EN_DISP, RES_DISP, MAX);
    assign DISPMAX2 = cDISPMAX2(EN_DISP, RES_DISP, MAX);
    assign DISPMAX3 = cDISPMAX3(EN_DISP, RES_DISP, MAX);
    assign DISPNUM1 = cDISPNUM1(EN_DISP, RES_DISP, NUM);
    assign DISPNUM2 = cDISPNUM2(EN_DISP, RES_DISP, NUM);

    function [6:0] cDISPMAX1;
	input EN_DISP, RES_DISP;
	input [8:0] MAX;
	reg [8:0] TM;
	begin: _cDISPMAX1
	    if (MAX[8])
	      TM = {4'b1111, -MAX[4:0]};
	    else
	      TM = {4'b0, MAX[4:0]};
	    if (EN_DISP)
	      cDISPMAX1 = 0;
            else if (!RES_DISP)
	      cDISPMAX1 = 7'b1000000;
	    else if (TM[8] == 0 && TM > 99)
	      cDISPMAX1 = 7'b0011000;
	    else
	      cDISPMAX1 = 7'b0111111;
        end
    endfunction // cDISPMAX1

    function [6:0] cDISPMAX2;
	input EN_DISP, RES_DISP;
	input [8:0] MAX;
	reg [8:0] TM;
	begin: _cDISPMAX2
	    if (MAX[8])
	      TM = {4'b1111, -MAX[4:0]};
	    else
	      TM = {4'b0, MAX[4:0]};
	    if (TM[8] == 0 && TM > 99)
	      TM = TM - 100;
	    if (EN_DISP)
	      cDISPMAX2 = 0;
            else if (!RES_DISP)
	      cDISPMAX2 = 7'b1000000;
	    else if (TM[8] == 0 && TM > 89)
	      cDISPMAX2 = 7'b1111110;
	    else if (TM[8] == 0 && TM > 79)
	      cDISPMAX2 = 7'b1111111;
	    else if (TM[8] == 0 && TM > 69)
	      cDISPMAX2 = 7'b0011100;
	    else if (TM[8] == 0 && TM > 59)
	      cDISPMAX2 = 7'b1110111;
	    else if (TM[8] == 0 && TM > 49)
	      cDISPMAX2 = 7'b1110110;
	    else if (TM[8] == 0 && TM > 39)
	      cDISPMAX2 = 7'b1011010;
	    else if (TM[8] == 0 && TM > 29)
	      cDISPMAX2 = 7'b1111001;
	    else if (TM[8] == 0 && TM > 19)
	      cDISPMAX2 = 7'b1101100;
	    else if (TM[8] == 0 && TM > 9)
	      cDISPMAX2 = 7'b0011000;
	    else
	      cDISPMAX2 = 7'b0111111;
        end
    endfunction // cDISPMAX2

    function [6:0] cDISPMAX3;
	input EN_DISP, RES_DISP;
	input [8:0] MAX;
	reg [8:0] TM;
	begin: _cDISPMAX3
	    if (MAX[8])
              TM = {4'b1111, -MAX[4:0]};
	    else
              TM = {4'b0, MAX[4:0]};
	    if (TM[8] == 0 && TM > 99)
              TM = TM - 100;
	    else if (TM[8] == 0 && TM > 89)
              TM = TM - 90;
	    else if (TM[8] == 0 && TM > 79)
	      TM = TM - 80;
	    else if (TM[8] == 0 && TM > 69)
	      TM = TM - 70;
	    else if (TM[8] == 0 && TM > 59)
	      TM = TM - 60;
	    else if (TM[8] == 0 && TM > 49)
	      TM = TM - 50;
	    else if (TM[8] == 0 && TM > 39)
	      TM = TM - 40;
	    else if (TM[8] == 0 && TM > 29)
	      TM = TM - 30;
	    else if (TM[8] == 0 && TM > 19)
	      TM = TM - 20;
	    else if (TM[8] == 0 && TM > 9)
	      TM = TM - 10;
	    if (EN_DISP)
	      cDISPMAX3 = 0;
            else if (!RES_DISP)
	      cDISPMAX3 = 7'b1000000;
            else if (TM[8] == 0 && TM > 8)
              cDISPMAX3 = 7'b1111110;
	    else if (TM[8] == 0 && TM > 7)
	      cDISPMAX3 = 7'b1111111;
            else if (TM[8] == 0 && TM > 6)
	      cDISPMAX3 = 7'b0011100;
	    else if (TM[8] == 0 && TM > 5)
	      cDISPMAX3 = 7'b1110111;
	    else if (TM[8] == 0 && TM > 4)
	      cDISPMAX3 = 7'b1110110;
	    else if (TM[8] == 0 && TM > 3)
	      cDISPMAX3 = 7'b1011010;
	    else if (TM[8] == 0 && TM > 2)
	      cDISPMAX3 = 7'b1111001;
	    else if (TM[8] == 0 && TM > 1)
	      cDISPMAX3 = 7'b1101100;
	    else if (TM[8] == 0 && TM > 0)
	      cDISPMAX3 = 7'b0011000;
	    else
	      cDISPMAX3 = 7'b0111111;
        end
    endfunction // cDISPMAX3

    function [6:0] cDISPNUM1;
	input EN_DISP, RES_DISP;
	input [4:0] NUM;
	begin: _cDISPNUM1
	    if (EN_DISP)
	      cDISPNUM1 = 0;
            else if (!RES_DISP)
	      cDISPNUM1 = 7'b1000000;
	    else if (NUM > 9)
	      cDISPNUM1 = 7'b0011000;
	    else
	      cDISPNUM1 = 7'b0111111;
	end
    endfunction // cDISPNUM1

    function [6:0] cDISPNUM2;
	input EN_DISP, RES_DISP;
	input [4:0] NUM;
	reg [4:0] TN;
	begin: _cDISPNUM2
	    if (NUM > 9)
              TN = NUM - 10;
	    else
	      TN = NUM;
	    if (EN_DISP)
              cDISPNUM2 = 0;
	    else if (!RES_DISP)
	      cDISPNUM2 = 7'b1000000;
	    else if (TN > 8)
              cDISPNUM2 = 7'b1111110;
	    else if (TN > 7)
	      cDISPNUM2 = 7'b1111111;
            else if (TN > 6)
	      cDISPNUM2 = 7'b0011100;
	    else if (TN > 5)
	      cDISPNUM2 = 7'b1110111;
	    else if (TN > 4)
	      cDISPNUM2 = 7'b1110110;
	    else if (TN > 3)
	      cDISPNUM2 = 7'b1011010;
	    else if (TN > 2)
	      cDISPNUM2 = 7'b1111001;
	    else if (TN > 1)
	      cDISPNUM2 = 7'b1101100;
	    else if (TN > 0)
	      cDISPNUM2 = 7'b0011000;
	    else
	      cDISPNUM2 = 7'b0111111;
        end
    endfunction // cDISPNUM2

    always @ (posedge CLOCK) begin
	case (STATO)
          st0: begin
              RES_DISP = 0;
              EN_DISP = 0;
              STATO = st1;
	  end
          st1: begin
              if (START) begin
                  NUM = 0;
                  MAR = 0;
                  FLAG = 0;
                  EN_DISP = 1;
                  RES_DISP = 1;
                  STATO = st2;
              end else begin
                  STATO = st1;
              end
	  end
          st2: begin
              MAX = mem_mar;
              TEMP = mem_mar;
              STATO = st3;
	  end
          st3: begin
              if (MIN1) begin
                  if (FLAG) begin
                      FLAG = 0;
                      NUM = NUM+1;
                  end
              end else begin
                  if (MAG1) begin
                      if (MAG2) begin
                          MAX = mem_mar;
                      end
                      FLAG = 1;
                  end
              end
              TEMP = mem_mar;
              STATO = st4;
	  end
          st4: begin
              if (MAR == 31) begin
                  if (START)
                    STATO = st4;
                  else
                    STATO = st1;
                  EN_DISP = 0;
              end else begin
                  MAR = MAR+1;
                  STATO = st3;
              end
	  end
	endcase
    end

//  assert property (true |-> ##1 STATO!=st0);
//  assert property (STATO==st2 |-> RES_DISP==1);
//  assert property (STATO==st3 |-> MAX[8:0]==TEMP[8:0]);

//  assert property (!(STATO==st2) || (RES_DISP==1));
//  assert property (!(STATO==st3) || (MAX[8:0]==TEMP[8:0]));
wire prop_1 = (!(STATO==st2) || (RES_DISP==1));
wire prop_2 = (!(STATO==st3) || (MAX[8:0]==TEMP[8:0]));
wire prop = prop_1 && prop_2;
wire prop_neg = !prop;
assert property ( prop );
endmodule // b05
