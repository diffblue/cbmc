module top(input clk);

  reg [3:0] counter;

  initial counter=0;

  always @(posedge clk)
    counter=counter+1;

endmodule
