

module FrameSwap_ctr
   (
  input  logic clk_sys,         // this module exists in the system domain
  input  logic srst,            // active-high, clk_sys domain

  input  logic swap,   // 1-cycle pulse 
  input  logic render_idle,     // Renderer reports idle, we can now right

  output logic front_sel_sys,   // sent to frame swap combinational
  output logic did_swap,        // 1-cycle pulse when swap happens
  output logic start_render     // 1-cycle pulse that tells the renderer to change states and begin writting
);
  always_ff @(posedge clk_sys or posedge srst) begin
    if (srst) begin
      front_sel_sys <= 0;
      did_swap      <= 1'b0;
      start_render  <= 1'b0;
    end else begin
      did_swap     <= 1'b0;
      start_render <= 1'b0;

      // Swap only at VBLANK start, and only if renderer is idle.
      if (swap && render_idle) begin
        front_sel_sys <= ~front_sel_sys;
        did_swap      <= 1'b1;
        start_render  <= 1'b1;   // kick renderer to fill the new back buffer
      end
    end
  end
endmodule
