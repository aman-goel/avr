`define NUM_CLIENT 4

`define SHORT_WIDTH 5						// should be sufficient to express NUM_CLIENT

`define CLIENT_TYPE  [(`NUM_CLIENT - 1):0]
`define SHORT_TYPE   [(`SHORT_WIDTH - 1):0]

`define TRUE  1'd1
`define FALSE 1'd0

module client_server(clk, connect_client, disconnect_client);
	input clk;
	
	input `SHORT_TYPE connect_client;
	input `SHORT_TYPE disconnect_client;
	
	reg link       `CLIENT_TYPE;
	reg semaphore;
	
	initial
	begin
		semaphore = `TRUE;
		link[0]   = `FALSE;
		link[1]   = `FALSE;
		link[2]   = `FALSE;
		link[3]   = `FALSE;
	end
	
	always @ (posedge clk)
	begin
		// connect
		if (semaphore)
		begin
			link[connect_client] <= `TRUE;
			semaphore <= `FALSE;
		end
		
		// disconnect
		if (link[disconnect_client])
		begin
			link[disconnect_client] <= `FALSE;
			semaphore <= `TRUE;
		end
	end
	
	wire prop =
// 		!((semaphore && !((!link[0] && !link[1] && !link[2] && !link[3] && semaphore))))	&&
		
// 		!(link[0] && semaphore) &&
// 		!(link[1] && semaphore) &&
// 		!(link[2] && semaphore) &&
// 		!(link[3] && semaphore) &&
		
		!(link[0] && link[1])	&&
		!(link[0] && link[2])	&&
		!(link[0] && link[3])	&&
		!(link[1] && link[2])	&&
		!(link[1] && link[3])	&&
		!(link[2] && link[3])	;
	
	wire prop_neg = !prop;
	assert property ( prop );
	
endmodule
