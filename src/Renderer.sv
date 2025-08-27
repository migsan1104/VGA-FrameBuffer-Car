

module Renderer #(
  // Framebuffer dimensions
  parameter int W         = 320,
  parameter int H         = 240,

  // Car bounding box (centered at X0+dx, Y0+dy)
  parameter int WB        = 88,
  parameter int HB        = 44,

  // Pixel format and color
  parameter int  PIX_BITS = 16,                 // 4 bits per color, 4 x 3 = 12 total bits per pixel. Pad with 4 bits
  parameter logic [PIX_BITS-1:0] CAR_COLOR = 16'h0F22, // red by default

  // Wait-state pacing cycles between sections, by default there is none, will be implemented later
  parameter int WAIT_GAP_CYCLES = 0
)(
  // Clocks & control
  input  logic                      clk,
  input  logic                      rst,
  input  logic                      start,      

  // Displacement from screen center
  input  logic signed [11:0]        dx,
  input  logic signed [11:0]        dy,

  
  output logic                      fb_we,
  output logic [17:0]               fb_addr,    // linear: y*W + x
  output logic [PIX_BITS-1:0]       fb_wdata,   // pixel data to write

  // Status
  output logic                      busy,       // 1 while rendering
  output logic                      done        // 1-cycle pulse when finished
);
      localparam int X0 = W/2;
  localparam int Y0 = H/2;

  localparam logic [PIX_BITS-1:0] COL_BLACK = '0;         // RGB444 black
  localparam logic [PIX_BITS-1:0] COL_RED   = CAR_COLOR;  // RGB444 red

  function automatic [17:0] addr_xy(input int x, input int y);
    return y*W + x;
  endfunction

  // === FSM ===
  typedef enum logic [1:0] {IDLE, RUN} state_t;
  state_t state, next_state;
  
    // Current pixel that is being written to
  int pixel_x, pixel_y;

  // Car bbox top-left 
  int x0, y0;

  // Busy/done
  assign busy     = (state != IDLE);
  // combinational logic for next state, by default next_state = state.
  always_comb begin
    next_state = state;
    case (state) 
        IDLE: begin
            if(start) next_state = RUN;
        end
        RUN: begin
            if( pixel_y == H) next_state = IDLE;
        end
    
        default: next_state = state;
       
    endcase
    
  end
  always_ff @(posedge clk or posedge rst) begin
  if (rst) begin
    state    <= IDLE;
    pixel_x  <= 0;
    pixel_y  <= 0;
    x0       <= 0;
    y0       <= 0;
    done     <= 1'b0;
  end else begin
    state <= next_state;
    done  <= 1'b0; // default

    unique case (state)
      IDLE: begin
        if (start) begin
          x0 <= X0 - (WB/2) + dx;
          y0 <= Y0 - (HB/2) + dy;
          pixel_x <= 0;
          pixel_y <= 0;
        end
      end

      RUN: begin
        // advance raster
        if (pixel_y < H) begin
          if (pixel_x == W-1) begin
            pixel_x <= 0;
            pixel_y <= pixel_y + 1;
          end else begin
            pixel_x <= pixel_x + 1;
          end
        end

        // Pulse goes high for one cycle after last pixel is done
        if (pixel_y == H) begin
          done <= 1'b1;
        end
      end
    endcase
  end
end

// Combinational write control
always_comb begin
// by defaultt we do not write
  fb_we    = 1'b0;
  fb_addr  = '0;
  fb_wdata = COL_BLACK;
    // if in the run state we write
  if (state == RUN && pixel_y < H) begin
    fb_we    = 1'b1;
    fb_addr  = addr_xy(pixel_x, pixel_y);
    // if in car section we draw red, if not we draw black
    fb_wdata = ((pixel_x >= x0) && (pixel_x < x0 + WB) &&
                (pixel_y >= y0) && (pixel_y < y0 + HB))
               ? COL_RED : COL_BLACK;
  end
end

endmodule

