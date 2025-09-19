// Top Level for project, by default display 640x480 @ 60fps

module VGA_Controller #(
  // VGA 640x480@~60Hz timing
  parameter int W_VIS   = 640,
  parameter int H_VIS   = 480,
  parameter int H_FP    = 16,
  parameter int H_SYNC  = 96,
  parameter int H_BP    = 48,
  parameter int V_FP    = 10,
  parameter int V_SYNC  = 2,
  parameter int V_BP    = 33,

  // Framebuffer: 320x240, 16b pixels (lower 12b are RGB444)
  parameter int W_FB      = 320,
  parameter int H_FB      = 240,
  parameter int FB_ADDR_W = 17,   // 320*240=76800 < 2^17
  parameter int FB_DATA_W = 16
)(
  input  logic       clk_100,
  input  logic       btn_reset_n,   // active-low

  input  logic       btn_up,
  input  logic       btn_down,
  input  logic       btn_left,
  input  logic       btn_right,
  input  logic       btn_center,

  output logic       vga_hsync,
  output logic       vga_vsync,
  output logic [3:0] vga_r,
  output logic [3:0] vga_g,
  output logic [3:0] vga_b
);

  //Clock and reset gen
  logic clk_sys, clk_pix, pll_locked;

  Clock_Gen #(.DIV_PIX(4)) u_clkgen (
    .clk_in     (clk_100),
    .rst        (btn_reset_n),  // active-low
    .clk_sys    (clk_sys),
    .pix_clk    (clk_pix),
    .pll_locked (pll_locked)
  );
  
  logic srst_sys;   // active-high, sync to clk_sys
  logic prst_pix;   // active-high, sync to clk_pix

  ResetGen u_resetgen (
    .clk_sys     (clk_sys),
    .pix_clk     (clk_pix),
    .ext_reset_n (btn_reset_n),
    .pll_locked  (pll_locked),
    .srst        (srst_sys),
    .prst        (prst_pix)
  );

  //Frame Buffers
  
  // BRAM A
  logic [FB_DATA_W-1:0] fbA_dout_a;
  Frame_Buffer #(
    .W(W_FB), .H(H_FB),
    .DATA_W(FB_DATA_W), .ADDR_W(FB_ADDR_W)
  ) u_fbA (
    // Port A: pixel read
    .clk_a  (clk_pix),
    .en_a   (ena_A_pix),
    .addr_a (addra_A),
    .dout_a (fbA_dout_a),
    // Port B: system write
    .clk_b  (clk_sys),
    .en_b   (enb_A),
    .we_b   (web_A),
    .addr_b (addrb_A),
    .din_b  (dinb_A)
  );

  // BRAM B
  logic [FB_DATA_W-1:0] fbB_dout_a;
  Frame_Buffer #(
    .W(W_FB), .H(H_FB),
    .DATA_W(FB_DATA_W), .ADDR_W(FB_ADDR_W)
  ) u_fbB (
    // Port A: pixel read
    .clk_a  (clk_pix),
    .en_a   (ena_B_pix),
    .addr_a (addra_B),
    .dout_a (fbB_dout_a),
    // Port B: system write
    .clk_b  (clk_sys),
    .en_b   (enb_B),
    .we_b   (web_B),
    .addr_b (addrb_B),
    .din_b  (dinb_B)
  );

  // Wires between Pixel_Path / Renderer and FrameSwap_Comb
  logic                  rd_en_pix;
  logic [FB_ADDR_W-1:0]  rd_addr_pix;
  logic [FB_DATA_W-1:0]  rd_data_mux;   

  // Write side from Renderer, in system domain
  logic                  ren_fb_we;
  logic [FB_ADDR_W-1:0]  ren_fb_addr;
  logic [FB_DATA_W-1:0]  ren_fb_wdata;

  // Steering to BRAMs
  logic [FB_ADDR_W-1:0]  addra_A, addra_B;
  logic                  ena_A_pix, ena_B_pix;

  logic                  enb_A, enb_B;
  logic                  web_A, web_B;
  logic [FB_ADDR_W-1:0]  addrb_A, addrb_B;
  logic [FB_DATA_W-1:0]  dinb_A,  dinb_B;

  // Combinational part of frame swap logic, handles cdc
  logic front_sel_sys;      
  logic did_swap_pulse;      

  FrameSwap_Comb #(
    .ADDR_W(FB_ADDR_W),
    .DATA_W(FB_DATA_W),
    .MASK_WR_ON_SWAP(1'b1)   
  ) u_swap_comb (
    
    .clk_pix        (clk_pix),
    .prst           (prst_pix),

    
    .front_sel_sys  (front_sel_sys),
    .swap_tick_sys  (did_swap_pulse),

    
    .rd_addr_pix    (rd_addr_pix),
    .rd_en_pix      (rd_en_pix),
    .rd_data_pix_A  (fbA_dout_a),
    .rd_data_pix_B  (fbB_dout_a),
    .rd_data_mux    (rd_data_mux),
    .addra_A        (addra_A),
    .addra_B        (addra_B),
    .ena_A_pix      (ena_A_pix),
    .ena_B_pix      (ena_B_pix),

    
    .wr_en_sys      (ren_fb_we),
    .wr_addr_sys    (ren_fb_addr),
    .wr_data_sys    (ren_fb_wdata),
    .enb_A          (enb_A),
    .enb_B          (enb_B),
    .web_A          (web_A),
    .web_B          (web_B),
    .addrb_A        (addrb_A),
    .addrb_B        (addrb_B),
    .dinb_A         (dinb_A),
    .dinb_B         (dinb_B)
  );

// Pixel domain 
  logic [$clog2(W_VIS+H_FP+H_SYNC+H_BP)-1:0] h_count;
  logic hsync_n, eol;

  Horizontal_Counter #(
    .H_VISIBLE     (W_VIS),
    .H_FRONT_PORCH (H_FP),
    .H_SYNC_PULSE  (H_SYNC),
    .H_BACK_PORCH  (H_BP)
  ) u_hctr (
    .clk         (clk_pix),
    .rst         (prst_pix),
    .h_count     (h_count),
    .h_sync      (hsync_n),
    .end_of_line (eol)
  );

  
  logic vsync_n, v_visible, eof_pulse_pix, vblank_start_pix, vblank_toggle_pix;
  logic [9:0] v_count;
  Vertical_Counter #(
    .V_ACTIVE (H_VIS),
    .V_FP     (V_FP),
    .V_SYNC   (V_SYNC),
    .V_BP     (V_BP)
  ) u_vctr (
    .pix_clk       (clk_pix),
    .rst        (prst_pix),
    .eol           (eol),
    .v_cnt         (v_count),
    .vsync         (vsync_n),
    .v_visible     (v_visible),
    .eof           (eof_pulse_pix),
    .vblank_start  (vblank_start_pix),
    .vblank_toggle (vblank_toggle_pix)
  );

  logic [11:0] vga_rgb12;
  Pixel_Path #(
    .W_VIS         (W_VIS),
    .H_VIS         (H_VIS),
    .V_FP          (V_FP), .V_SYNC(V_SYNC), .V_BP(V_BP),
    .H_FRONT_PORCH (H_FP), .H_SYNC_PULSE(H_SYNC), .H_BACK_PORCH(H_BP),
    .W_FB          (W_FB),
    .H_FB          (H_FB),
    .ADDR_W        (FB_ADDR_W)
  ) u_pixpath (
    .pix_clk     (clk_pix),
    .prst        (prst_pix),

    .h_cnt       (h_count),
    .v_cnt       (v_count),
    .h_sync      (hsync_n),
    .v_sync      (vsync_n),

   
    .rd_data_pix (rd_data_mux),
    .rd_addr_pix (rd_addr_pix),
    .rd_en_pix   (rd_en_pix),

    // VGA out
    .vga_hsync   (vga_hsync),
    .vga_vsync   (vga_vsync),
    .vga_rgb     (vga_rgb12)
  );

  assign vga_r = vga_rgb12[11:8];
  assign vga_g = vga_rgb12[7:4];
  assign vga_b = vga_rgb12[3:0];

 // System domain
  // Debounce buttons
  logic up_held, down_held, left_held, right_held, center_level;
  Debounce_Level u_db_up     (.clk(clk_sys), .rst(srst_sys), .in(btn_up),     .level(up_held));
  Debounce_Level u_db_down   (.clk(clk_sys), .rst(srst_sys), .in(btn_down),   .level(down_held));
  Debounce_Level u_db_left   (.clk(clk_sys), .rst(srst_sys), .in(btn_left),   .level(left_held));
  Debounce_Level u_db_right  (.clk(clk_sys), .rst(srst_sys), .in(btn_right),  .level(right_held));
  Debounce_Level u_db_center (.clk(clk_sys), .rst(srst_sys), .in(btn_center), .level(center_level));

  
 // Frame tick in system domain via vblank_toggle CDC using pulse synch module
logic frame_tick_sys;

Pulse_Sync #(.data_w(1)) u_frame_tick_sync (
  .clk     (clk_sys),
  .rst     (srst_sys),
  .data_in (vblank_toggle_pix), 
  .out     (frame_tick_sys)     
);


  // Car control
  logic signed [11:0] dx, dy;
  Car_Control #(
    .W(W_FB), .H(H_FB), .WB(88), .HB(44),
    .STEP(1), .SCREEN_COUNT(5)
  ) u_car (
    .clk          (clk_sys),
    .rst          (srst_sys),
    .frame_tick   (frame_tick_sys),
    .up_held      (up_held),
    .down_held    (down_held),
    .left_held    (left_held),
    .right_held   (right_held),
    .center_reset (center_level),
    .dx           (dx),
    .dy           (dy)
  );

  // Renderer 
  logic ren_busy, ren_done, start_render_pulse;
  Renderer #(
    .W(W_FB), .H(H_FB), .WB(88), .HB(44),
    .PIX_BITS(FB_DATA_W), .ADDR_W(FB_ADDR_W)
  ) u_renderer (
    .clk      (clk_sys),
    .rst      (srst_sys),
    .start    (start_render_pulse),
    .dx       (dx),
    .dy       (dy),
    .fb_we    (ren_fb_we),
    .fb_addr  (ren_fb_addr),
    .fb_wdata (ren_fb_wdata),
    .busy     (ren_busy),
    .done     (ren_done)
  );

  // Frame swap controller
  FrameSwap_ctr u_swap (
    .clk_sys       (clk_sys),
    .srst          (srst_sys),
    .swap          (frame_tick_sys),    
    .render_idle   (~ren_busy),
    .front_sel_sys (front_sel_sys),     
    .did_swap      (did_swap_pulse),    
    .start_render  (start_render_pulse) 
  );

endmodule
