module main (i, clock);
input i,clock;
reg [19:0]a,b,c;

initial a = 100;
initial b = 200;

always @ (posedge clock) begin
	a <= b;	
	b <= a;
end

// assert property (a == 100 || a == 200);
wire prop = (a == 100 || a == 200);
wire prop_neg = !prop;
assert property ( prop );
endmodule
