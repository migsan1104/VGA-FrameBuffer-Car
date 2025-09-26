
module Clock_Gen #(
  parameter int DIV_PIX = 4   // divider must be even
)(
  input  logic clk_in,         // e.g., 100 MHz board clock
  input  logic rst,    // active-low

  output logic clk_sys,        // system clock (pass-through)
  output logic pix_clk,        // pixel clock (clk_in / DIV_PIX)
  output logic pll_locked      // "clocks stable" flag
);
  // Pass-through system clock
  assign clk_sys = clk_in;

  // Simple even divider for pix_clk
  localparam int HALF = DIV_PIX/2;

  //counter for lock and clock divider
  logic [15:0] cnt_pix;   
  logic [7:0]  lock_cnt;

  always_ff @(posedge clk_in or negedge rst) begin
    if (!rst) begin
      cnt_pix    <= '0;
      pix_clk    <= 1'b0;
      lock_cnt   <= '0;
      pll_locked <= 1'b0;
    end else begin
      
      if (cnt_pix == HALF-1) begin
        cnt_pix <= '0;
        pix_clk <= ~pix_clk;
      end else begin
        cnt_pix <= cnt_pix + 16'd1;
      end

      // slock after a given amount of cycles to ensure the clock is safe
      if (!pll_locked) begin
        lock_cnt   <= lock_cnt + 8'd1;
        if (&lock_cnt) pll_locked <= 1'b1;  // goes high after ~256 sys cycles
      end
    end
  end
endmodule
