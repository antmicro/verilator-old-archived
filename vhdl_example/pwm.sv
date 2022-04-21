module pwm #( parameter int size = 12)
(
    input logic clk,
    input [size-1 : 0] duty,
    output logic o
);
    logic [size-1:0] counter;
    always@(posedge clk) begin
	counter = counter + 1;
	if(counter < duty)
	    o = 1;
	else
	    o = 0;
    end
endmodule
