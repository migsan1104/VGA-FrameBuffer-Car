`timescale 1ns / 1ps



module Debounce_Level #(
  //  COUNT_MAX = 250_000 → 2.5 ms @ 100 MHz
  parameter int COUNT_MAX = 250_000
)(
  input  logic clk, rst,     // we are in the  clk_sys domain
  input  logic in,      
  output logic level         // debounced level: 1 while held, 0 when released
);

  int unsigned cnt;          // counts how long input has stayed the same

  always_ff @(posedge clk) begin
    if (rst) begin
      level <= 1'b0;
      cnt   <= 0;
    end else begin
      // if input differs from current level, start/continue counting, this applies to rising edge and falling edge of button
      if (in != level) begin
        if (cnt >= COUNT_MAX) begin
          level <= in;  // accept the change after the specified stable period
          cnt   <= 0;
        end else begin
          cnt <= cnt + 1;
        end
      end else begin
        // input equals current level → reset counter
        cnt <= 0;
      end
    end
  end
endmodule

