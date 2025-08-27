module Pixel_Path #(
// width visible are and height visible area
  parameter int W_VIS  = 640,  
  parameter int H_VIS  = 480,
  // params for blank area
  parameter int V_FP = 10, V_SYNC = 2, V_BP = 33,
  parameter int H_FRONT_PORCH = 16, H_SYNC_PULSE = 96, H_BACK_PORCH = 48,
  parameter int W_FB   = 320,  
  parameter int H_FB   = 240,
  parameter int ADDR_W = 17   
)(
  input  logic              pix_clk,
  input  logic              prst,

  // From your counters
  input  logic [$clog2(W_VIS + H_FRONT_PORCH + H_SYNC_PULSE + H_BACK_PORCH)-1:0] h_cnt, 
  input  logic [$clog2(H_VIS+V_FP + V_SYNC + V_BP)-1:0]  v_cnt,   
  input  logic                         h_sync,
  input  logic                         v_sync,
    
  
  //from bram
  input  logic [15:0]                  rd_data_pix,  
  // Sent to front frame buffer
  output logic [ADDR_W-1:0]            rd_addr_pix,
  output logic                         rd_en_pix,
 

  // VGA pins
  output logic                         vga_hsync,
  output logic                         vga_vsync,
  output logic [11:0]                  vga_rgb
);
  // Because the bram is half the size of the visible area , each pixel is a 2x2 block
  logic [9:0] fb_x;  // 0..319
  logic [8:0] fb_y;  // 0..239
  
  // used to determine if we are in visible range
  logic video_active;

  // pipelined by one cycle 
  logic video_active_q;
  logic [11:0] rd_data_q;
  logic [ADDR_W - 1 :0 ] addr;
  
  // all comb logic 
    always_comb begin
    // visible window (correct pairing)
    video_active = (h_cnt < W_VIS) && (v_cnt < H_VIS);

    // 2x upscale mapping: divide by 2
    fb_x = h_cnt[9:1];     // 0..319
    fb_y = v_cnt[8:1];     // 0..239

    // linear address y*W_FB + x (keeps params flexible)
    addr = fb_y * W_FB + fb_x;

    // BRAM enable only during visible region
    
  end
  
  always_ff @(posedge pix_clk or posedge prst) begin
    if (prst) begin
     
      rd_addr_pix<= '0;
      rd_en_pix  <= 1'b0;
      vga_rgb    <= 12'h000;
      vga_hsync  <= 1'b1;
      vga_vsync  <= 1'b1;
      
      video_active_q <= 1'b0;
      rd_data_q <= 12'b0;
    end else begin
      // syncs are passed straight through
      vga_hsync <= h_sync;
      vga_vsync <= v_sync;
       
      rd_addr_pix     <= addr;
      rd_en_pix       <= video_active;

      // pipelined data
      video_active_q  <= video_active;
      rd_data_q       <= rd_data_pix[11:0];

      // drive RGB with pipelined data; black during blanking/porches
      vga_rgb      <= video_active_q ? rd_data_q : 12'h000;
      end
    end
  
endmodule

