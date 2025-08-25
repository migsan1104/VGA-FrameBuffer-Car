
module Frame_Buffer #(
  parameter W = 320,
  parameter H = 240,
  parameter DATA_W = 16,
  parameter ADDR_W = 17  
)(
  // ── Port A : Read @ pixel clock domain (VGA)
  input  logic               clk_a,     // clk_pix, we are only reading in the pixel domain
  input  logic               en_a,      // read enable
  input  logic [ADDR_W-1:0]  addr_a,    // address for port A
  output logic [DATA_W-1:0]  dout_a,    // pixel data (front buffer)

  // ── Port B : Write @ system clock domain (Renderer)
  input  logic               clk_b,     // clk_sys
  input  logic               en_b,      // port enable
  input  logic               we_b,      // write enable (byte/word write = 1)
  input  logic [ADDR_W-1:0]  addr_b,    // address for port B
  input  logic [DATA_W-1:0]  din_b     // data from renderer to write into frame buffer
 
);
    // Instruct Vivado to use Block RAMs
  (* ram_style = "block", cascade_height = "auto" *);
  localparam int DEPTH = W * H;
  logic [DATA_W-1:0] mem [0:DEPTH-1];

  // Optional preload (uncomment if you have a hex)
  // initial $readmemh("fb_init.hex", mem);

  // Port A: synchronous READ in pixel domain
  always_ff @(posedge clk_a) begin
    if (en_a) begin
      dout_a <= mem[addr_a];     // reading the 16 bit word on next clock cycle
    end
  end

 // Port B: synchronous WRITE in system clock
  always_ff @(posedge clk_b) begin
    if (en_b && we_b) begin
      mem[addr_b] <= din_b;      // write 16 bit word
    end
  end
endmodule
