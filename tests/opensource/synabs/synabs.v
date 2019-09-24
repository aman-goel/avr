module main (i, clock);
input i,clock;
reg [4:0]a,b,c,t;

initial a = 4'd1;
initial b = 4'd5;
initial c = 4'd7;
initial t = 4'd11;

always @ (posedge clock) begin

	if (b == 4'd5)
		a <= 4'd5;
	else if (c == 4'd1)	
		a <= 4'd7;
	else if (b == 4'd1)	
		a <= 4'd3;
	else a<= t;

	b <= c;
	c <= a;
	t <= t + 4'd2;

end

// assert property (~(a ==  2));
wire prop = (~(a ==  4'd2));
wire prop_neg = !prop;
assert property ( prop );
endmodule
