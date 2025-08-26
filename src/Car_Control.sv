
module Car_Control #(
  parameter int W    = 320,
  parameter int H    = 240,
  parameter int WB   = 88,        // car width  (~1/20 screen area with HB)
  parameter int HB   = 44,        // car height
  parameter int STEP = 1,         // pixels per allowed update
  parameter int SCREEN_COUNT = 5  // move once every N frames
)(
  input  logic clk, rst,                  // clk_sys domain
  input  logic frame_tick,                // 1-cycle pulse each frame (pix→sys)
  input  logic up_held, down_held, left_held, right_held,
  input  logic center_reset,              // debounced (level or pulse)
  output logic signed [11:0] dx, dy       // displacement from center
);

  
  localparam int X0 = W/2, Y0 = H/2;
  localparam int DX_MIN = -(X0 - (WB/2));
  localparam int DX_MAX =  (X0 - (WB/2));
  localparam int DY_MIN = -(Y0 - (HB/2));
  localparam int DY_MAX =  (Y0 - (HB/2));

 
  logic [$clog2(SCREEN_COUNT)-1:0] frame_cnt;
  wire  move_en_now = (frame_cnt == (SCREEN_COUNT-1)); 
// function used to clamp values so that the car does not go out of bounds
  function automatic signed [11:0] clamp(
    input signed [11:0] v, input signed [11:0] mn, input signed [11:0] mx
  );
    if (v < mn) return mn;
    else if (v > mx) return mx;
    else return v;
  endfunction

  always_ff @(posedge clk) begin
    if (rst) begin
      dx <= '0;
      dy <= '0;
      frame_cnt <= '0;
    end else if (frame_tick) begin
      if (center_reset) begin
        dx <= '0;
        dy <= '0;
        frame_cnt <= '0;                      // reset pacing on recenter
      end else begin
        // Move only every Nth frame, by default it is 5
        if (move_en_now) begin
          automatic logic signed [11:0] ndx = dx;
          automatic logic signed [11:0] ndy = dy;

          
          if (left_held  && !right_held) ndx = ndx - STEP;
          else if (right_held && !left_held) ndx = ndx + STEP;

          if (up_held    && !down_held)  ndy = ndy - STEP;
          else if (down_held  && !up_held)  ndy = ndy + STEP;
            // run the clamping function to ensure the car is in the valid range
          dx <= clamp(ndx, DX_MIN, DX_MAX);
          dy <= clamp(ndy, DY_MIN, DY_MAX);
        end

        
        frame_cnt <= move_en_now ? '0 : (frame_cnt + 1'b1);
      end
    end
    
  end
endmodule

 
