
module FrameSwap_Comb #(
  parameter int ADDR_W = 17,
  parameter int DATA_W = 16,
  parameter bit MASK_WR_ON_SWAP = 1'b0   // used to mask write enable
)(
  // Clk and reset needed for cdc 2ffsync
  input  logic clk_pix,
  input  logic prst,            // active-high (pix domain)
 

  // Control from FrameSwapCtrl 
  input  logic front_sel_sys,   // 0:A front, 1:B front
  input  logic swap_tick_sys,   //  1 cycle pulse for when we need to swap, comes from the controller

  // Sent from and to pixel domain
  input  logic [ADDR_W-1:0] rd_addr_pix,   // from Pixel_Path
  input  logic              rd_en_pix,     // from Pixel_Path
  input  logic [DATA_W-1:0] rd_data_pix_A, // VRAM_A.douta
  input  logic [DATA_W-1:0] rd_data_pix_B, // VRAM_B.douta
  output logic [DATA_W-1:0] rd_data_mux,   // to Pixel_Path
  output logic [ADDR_W-1:0] addra_A,       // to VRAM_A.addra
  output logic [ADDR_W-1:0] addra_B,       // to VRAM_B.addra
  output logic              ena_A_pix,     // to VRAM_A.ena
  output logic              ena_B_pix,     // to VRAM_B.ena

  // Sent from and to system domain
  input  logic              wr_en_sys,     // from Renderer
  input  logic [ADDR_W-1:0] wr_addr_sys,   // from Renderer
  input  logic [DATA_W-1:0] wr_data_sys,   // from Renderer
  output logic              enb_A,         // to VRAM_A.enb
  output logic              enb_B,         // to VRAM_B.enb
  output logic              web_A,         // to VRAM_A.web
  output logic              web_B,         // to VRAM_B.web
  output logic [ADDR_W-1:0] addrb_A,       // to VRAM_A.addrb
  output logic [ADDR_W-1:0] addrb_B,       // to VRAM_B.addrb
  output logic [DATA_W-1:0] dinb_A,        // to VRAM_A.dinb
  output logic [DATA_W-1:0] dinb_B         // to VRAM_B.dinb
);
  // sys -> pix cdc for front sel
  logic front_sel_pix;
  Synch2FF #(.Data_W(1)) u_fs_sync_to_pix (
    .clk        (clk_pix),
    .rst        (prst),
    .Data_asynch (front_sel_sys),
    .Out_synch  (front_sel_pix)
  );

  // Back buffer in sys domain
  logic back_sel_sys;
  assign back_sel_sys = ~front_sel_sys;

  // Bit mask used to protect write enable when we swap
  logic wr_safe;
  always_comb begin
    if (MASK_WR_ON_SWAP)
      wr_safe = wr_en_sys & ~swap_tick_sys;
    else
      wr_safe = wr_en_sys;
  end

  //Comb logic for data path, in both domains.
  always_comb begin
    // Pixel domain logic 
    addra_A   = rd_addr_pix;
    addra_B   = rd_addr_pix;
    ena_A_pix = rd_en_pix & (front_sel_pix == 1'b0);
    ena_B_pix = rd_en_pix & (front_sel_pix == 1'b1);
    rd_data_mux = (front_sel_pix == 1'b0) ? rd_data_pix_A : rd_data_pix_B;

    //  System domain logic
    addrb_A = wr_addr_sys;
    addrb_B = wr_addr_sys;
    dinb_A  = wr_data_sys;
    dinb_B  = wr_data_sys;

    enb_A = (back_sel_sys == 1'b0);
    enb_B = (back_sel_sys == 1'b1);

    web_A = enb_A & wr_safe;
    web_B = enb_B & wr_safe;
  end
endmodule

