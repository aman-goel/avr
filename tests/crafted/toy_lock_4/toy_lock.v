`define NUM_NODES   4

`define EPOCH_WIDTH 8
`define SHORT_WIDTH 2						// should be sufficient to express NUM_NODES

`define EPOCH_TYPE [(`EPOCH_WIDTH - 1):0]
`define NODE_TYPE  [(`NUM_NODES - 1):0]
`define SHORT_TYPE [(`SHORT_WIDTH - 1):0]
`define NODE_RTYPE [0:(`NUM_NODES - 1)]

`define TRUE  1'd1
`define FALSE 1'd0
`define ZERO      `EPOCH_WIDTH'd0
`define NON_ZERO  `EPOCH_WIDTH'd1

module toy_lock(clk, grantN1, grantN2, grantE, acceptN, acceptE, unknown);
	input clk;
	input unknown;
	
	input `SHORT_TYPE grantN1;
	input `SHORT_TYPE grantN2;
	input `EPOCH_TYPE grantE;
	
	input `SHORT_TYPE acceptN;
	input `EPOCH_TYPE acceptE;
	
	reg             held_0;
	reg             held_1;
	reg             held_2;
	reg             held_3;
	reg `EPOCH_TYPE ep_0;
	reg `EPOCH_TYPE ep_1;
	reg `EPOCH_TYPE ep_2;
	reg `EPOCH_TYPE ep_3;
	reg `EPOCH_TYPE transfer_0;
	reg `EPOCH_TYPE transfer_1;
	reg `EPOCH_TYPE transfer_2;
	reg `EPOCH_TYPE transfer_3;
	reg `EPOCH_TYPE locked_0;
	reg `EPOCH_TYPE locked_1;
	reg `EPOCH_TYPE locked_2;
	reg `EPOCH_TYPE locked_3;

	initial
	begin
		held_0 = `TRUE;
		held_1 = `FALSE;
		held_2 = `FALSE;
		held_3 = `FALSE;
		
		ep_0 = `NON_ZERO;
		ep_1 = `ZERO;
		ep_2 = `ZERO;
		ep_3 = `ZERO;
		
		transfer_0 = `ZERO;
		transfer_1 = `ZERO;
		transfer_2 = `ZERO;
		transfer_3 = `ZERO;
		
		locked_0 = `ZERO;
		locked_1 = `ZERO;
		locked_2 = `ZERO;
		locked_3 = `ZERO;
	end
	
	always @(posedge clk)
	begin
		if (grantN1 == `SHORT_WIDTH'd0)
			if (held_0)
			begin
				if (!(grantE <= ep_0))
				begin
					case(grantN2)
					`SHORT_WIDTH'd0 : transfer_0 <= grantE;
					`SHORT_WIDTH'd1 : transfer_1 <= grantE;
					`SHORT_WIDTH'd2 : transfer_2 <= grantE;
					`SHORT_WIDTH'd3 : transfer_3 <= grantE;
					endcase
					held_0 <= `FALSE;
				end
			end
		if (acceptN == `SHORT_WIDTH'd0)
			if (transfer_0 == acceptE)
			begin
				transfer_0 <= unknown ? `ZERO : transfer_0;
				if (!(acceptE <= ep_0))
				begin
					held_0 <= `TRUE;
					ep_0 <= acceptE;
					locked_0 <= acceptE;
				end
			end
			
		if (grantN1 == `SHORT_WIDTH'd1)
			if (held_1)
			begin
				if (!(grantE <= ep_1))
				begin
					case(grantN2)
					`SHORT_WIDTH'd0 : transfer_0 <= grantE;
					`SHORT_WIDTH'd1 : transfer_1 <= grantE;
					`SHORT_WIDTH'd2 : transfer_2 <= grantE;
					`SHORT_WIDTH'd3 : transfer_3 <= grantE;
					endcase
					held_1 <= `FALSE;
				end
			end
		if (acceptN == `SHORT_WIDTH'd1)
			if (transfer_1 == acceptE)
			begin
				transfer_1 <= unknown ? `ZERO : transfer_1;
				if (!(acceptE <= ep_1))
				begin
					held_1 <= `TRUE;
					ep_1 <= acceptE;
					locked_1 <= acceptE;
				end
			end

		if (grantN1 == `SHORT_WIDTH'd2)
			if (held_2)
			begin
				if (!(grantE <= ep_2))
				begin
					case(grantN2)
					`SHORT_WIDTH'd0 : transfer_0 <= grantE;
					`SHORT_WIDTH'd1 : transfer_1 <= grantE;
					`SHORT_WIDTH'd2 : transfer_2 <= grantE;
					`SHORT_WIDTH'd3 : transfer_3 <= grantE;
					endcase
					held_2 <= `FALSE;
				end
			end
		if (acceptN == `SHORT_WIDTH'd2)
			if (transfer_2 == acceptE)
			begin
				transfer_2 <= unknown ? `ZERO : transfer_2;
				if (!(acceptE <= ep_2))
				begin
					held_2 <= `TRUE;
					ep_2 <= acceptE;
					locked_2 <= acceptE;
				end
			end
			
		if (grantN1 == `SHORT_WIDTH'd3)
			if (held_3)
			begin
				if (!(grantE <= ep_3))
				begin
					case(grantN2)
					`SHORT_WIDTH'd0 : transfer_0 <= grantE;
					`SHORT_WIDTH'd1 : transfer_1 <= grantE;
					`SHORT_WIDTH'd2 : transfer_2 <= grantE;
					`SHORT_WIDTH'd3 : transfer_3 <= grantE;
					endcase
					held_3 <= `FALSE;
				end
			end
		if (acceptN == `SHORT_WIDTH'd3)
			if (transfer_3 == acceptE)
			begin
				transfer_3 <= unknown ? `ZERO : transfer_3;
				if (!(acceptE <= ep_3))
				begin
					held_3 <= `TRUE;
					ep_3 <= acceptE;
					locked_3 <= acceptE;
				end
			end
	end

	wire prop = 
				((locked_0 == `ZERO) || (locked_0 != locked_1)) &&
				((locked_0 == `ZERO) || (locked_0 != locked_2)) &&
				((locked_0 == `ZERO) || (locked_0 != locked_3)) &&
				((locked_1 == `ZERO) || (locked_1 != locked_2)) &&
				((locked_1 == `ZERO) || (locked_1 != locked_3)) &&
				((locked_2 == `ZERO) || (locked_2 != locked_3)) ;

	wire prop_neg = !prop;
	assert property (prop);
endmodule
