`timescale 1ns / 1ps

// Horizontal_Counter for vga controller by default 640x480
module Horizontal_Counter #(
    parameter H_VISIBLE     = 640,   // visible pixels
    parameter H_FRONT_PORCH = 16,    // front porch
    parameter H_SYNC_PULSE  = 96,    // sync pulse
    parameter H_BACK_PORCH  = 48     // back porch
)(
    input  logic clk,        // pixel clock
    input  logic rst,        // reset
    output logic [$clog2(H_VISIBLE+H_FRONT_PORCH+H_SYNC_PULSE+H_BACK_PORCH)-1:0] h_count, // current pixel position
    output logic h_sync,     // horizontal sync signal, active low 
    output logic end_of_line // high when counter finishes a full line
);

    // total amount of pixels per line
    localparam H_TOTAL = H_VISIBLE + H_FRONT_PORCH + H_SYNC_PULSE + H_BACK_PORCH;

    // horizontal counter
    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            h_count <= 0;
        else if (h_count == H_TOTAL-1)
            h_count <= 0;
        else
            h_count <= h_count + 1;
    end

    // generate hsync (active low in VGA)
    always_comb begin
        if (h_count >= (H_VISIBLE + H_FRONT_PORCH) &&
            h_count <  (H_VISIBLE + H_FRONT_PORCH + H_SYNC_PULSE))
            h_sync = 1'b0;  // sync pulse
        else
            h_sync = 1'b1;
    end

    // flag for end of line
    assign end_of_line = (h_count == H_TOTAL-1);

endmodule

