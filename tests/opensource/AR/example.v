module main (clk);
input clk;
reg [250:0] a,b;	
	
initial a = 1;
initial b = 0;


always @ (posedge clock) begin
	if (a<100) 
	   a<=b+a;

	b <=a;
end

// assert property (a < 200);
wire prop = (a < 200);
wire prop_neg = !prop;
assert property ( prop );

endmodule
