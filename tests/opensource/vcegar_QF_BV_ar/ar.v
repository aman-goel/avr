module main (clk);
input clk;
reg [2500:0] a,b;	
	
initial a = 1;
initial b = 0;


always @ (posedge clk) begin
	if (a<100) 
	   a<=b+a;

	b <=a;
end

//always begin

//always begin
   wire prop = (a<200);
//end

	wire prop_neg = !prop;
	assert property ( prop );
   
//end

endmodule
