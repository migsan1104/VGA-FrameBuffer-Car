// Vertical Counter that updates once every line is complete, also ouputs Vsync signal
module Vertical_Counter #(
  // 640x480 @ 60 Hz vertical timings by default
  parameter int V_ACTIVE = 480,
  parameter int V_FP     = 10,
  parameter int V_SYNC   = 2,
  parameter int V_BP     = 33
)(
  input  logic pix_clk,     // pixel clock (25.17 MHz)
  input  logic rst,       // async active-high reset
  input  logic eol,         // 1-cycle pulse at end of each line (from h_counter)

  output logic [9:0] v_cnt, // 0 .. V_TOTAL-1  
  output logic       vsync, // active-low VSYNC
  output logic       v_visible, // 1 when v_cnt is in visible frame region 
  output logic       eof,     // 1-cycle pulse at end of frame
  output logic       vblank_start, // 1-cycle pulse for end of visible area
  output logic       vblank_toggle
);
// setting the total v_count to indiciate one fram is complete
  localparam int V_TOTAL = V_ACTIVE + V_FP + V_SYNC + V_BP;

  
  always_ff @(posedge pix_clk or posedge rst) begin
    if (rst) begin
      v_cnt <= '0;
    end else if (eol) begin
      if (v_cnt == V_TOTAL-1) v_cnt <= '0;
      else                    v_cnt <= v_cnt + 10'd1;
    end
  end

  // Visible window
  assign v_visible = (v_cnt < V_ACTIVE);

  // VSYNC (active low): low during the sync lines
  assign vsync = ~((v_cnt >= (V_ACTIVE + V_FP)) &&
                   (v_cnt <  (V_ACTIVE + V_FP + V_SYNC)));

  // single-cycle pulse on the last line's eol, drives eof and eof toggle
  
 // pulses for EOF and VBLANK start 
  wire last_line_eol         = eol && (v_cnt == V_TOTAL-1);
  wire last_visible_line_eol = eol && (v_cnt == V_ACTIVE-1);

   
  // EOF pulse logic 
  always_ff @(posedge pix_clk or posedge rst) begin
    if (rst) eof <= 1'b0;
    else        eof <= last_line_eol;
  end

  // VBLANK start pulse + toggle for cdc
  always_ff @(posedge pix_clk or posedge rst) begin
    if (rst) begin
      vblank_start  <= 1'b0;
      vblank_toggle <= 1'b0;
    end else begin
      vblank_start <= last_visible_line_eol;          // 1-cycle pulse
      if (last_visible_line_eol) vblank_toggle <= ~vblank_toggle;  // toggle of vblank used for cdc
    end
  end

endmodule
