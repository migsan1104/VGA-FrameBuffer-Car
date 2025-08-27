


module Pulse_Sync #(
    parameter int data_w = 1
)(  
    input logic clk,
    input logic rst,
    input logic [data_w - 1: 0] data_in,
    
    output logic [data_w - 1:0] out

    );
    logic [data_w - 1:0]  sync_out,ff_out;
    assign out =( ff_out ^ sync_out);
    Synch2ff  #(.Data_w(data_w)) synch(.clk(clk),.rst(rst),.Data_synch(data_in),.Out_synch(sync_out));
    
    always_ff @( posedge clk) begin
        if(rst) ff_out <= 0;
        else 
            ff_out <= sync_out;   
    end
    
endmodule
