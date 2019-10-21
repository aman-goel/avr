`define MODE_8BIT
`ifdef MODE_2BIT
	`define W 2
	`define WS1 1
	`define CNT_MAX 2'b11
`else
	`ifdef MODE_3BIT
		`define W 3
		`define WS1 2
		`define CNT_MAX 3'b111
	`else
		`ifdef MODE_4BIT
			`define W 4
			`define WS1 3
			`define CNT_MAX 4'b1111
		`else
			`ifdef MODE_8BIT
				`define W 8
				`define WS1 7
				`define CNT_MAX 8'b11111111
			`else
				`ifdef MODE_16BIT
					`define W 16
					`define WS1 15
					`define CNT_MAX 16'b1111111111111111
				`else
					`ifdef MODE_24BIT
						`define W 24
						`define WS1 23
						`define CNT_MAX 24'b111111111111111111111111
					`else
						`ifdef MODE_32BIT
							`define W 32
							`define WS1 31
							`define CNT_MAX 32'b11111111111111111111111111111111
						`else
							`ifdef MODE_40BIT
								`define W 40
								`define WS1 39
								`define CNT_MAX 40'b1111111111111111111111111111111111111111
							`else
								`ifdef MODE_48BIT
									`define W 48
									`define WS1 47
									`define CNT_MAX 48'b111111111111111111111111111111111111111111111111
								`else
									`ifdef MODE_56BIT
										`define W 56
										`define WS1 55
										`define CNT_MAX 56'b11111111111111111111111111111111111111111111111111111111
									`else
										`ifdef MODE_64BIT
											`define W 64
											`define WS1 63
											`define CNT_MAX 64'b1111111111111111111111111111111111111111111111111111111111111111
										`else
										`endif
									`endif
								`endif
							`endif
						`endif
					`endif
				`endif
			`endif		
		`endif	
	`endif
`endif
module paper_v3(clk);

	input wire	clk;
	reg [`WS1:0] x, y;
	
	initial begin
		x = `W'd0;
		y = `W'd0;
	end

	always @(posedge clk) begin
		x <= (y > x) ? x : ((y == x) || (x != `CNT_MAX)) ? x + `W'd1 : y;
		y <= (y == x) ? y + `W'd1 : ((y > x) || (x != `CNT_MAX)) ? y : x;

// 		x <= (y == x) ? x + `W'd1 : (y > x) ? x : (x != `CNT_MAX) ? x + `W'd1 : y;
// 		y <= (y == x) ? y + `W'd1 : (y > x) ? y : (x != `CNT_MAX) ? y : x;
	end

	wire prop = !(y > x);
	wire prop_neg = !prop;
	assert property ( prop );
endmodule // mult















