`timescale 1ns / 1ps

module Synch2FF #(
    parameter int Data_W = 1
)(
    input logic [Data_W - 1: 0] Data_asynch,
    input logic clk,
    input logic rst,
    output logic [Data_W - 1:0] Out_synch
);
    logic [Data_W - 1:0] meta;
    always_ff @(posedge clk or posedge rst) begin
        if(rst) begin
            meta <= 0;
            Out_synch <= 0;
        end
        else begin
            meta <= Data_asynch;
            Out_synch <= meta;
        end
    
    end
endmodule