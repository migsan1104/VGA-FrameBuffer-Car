`timescale 1ns / 1ps

module Vertical_Counter_tb;
// inputs
logic clk_pix;
logic rst_pix;


//outputs
logic [9:0] v_count;
logic vsync_n;
logic v_visible;
logic eof_pulse_pix;
logic vblank_start_pix;
logic vblank_toggle_pix;
logic [9:0] h_count;   // 0..799 → needs 10 bits
logic hsync_n;
logic eol;


//initiralizing the device under testing
Vertical_Counter 
 DUT_V (
    .pix_clk       (clk_pix),
    .rst          (rst_pix),
    .eol           (eol),
    .v_cnt         (v_count),
    .vsync         (vsync_n),
    .v_visible     (v_visible),
    .eof           (eof_pulse_pix),
    .vblank_start  (vblank_start_pix),
    .vblank_toggle (vblank_toggle_pix)
  );
Horizontal_Counter DUT_H (
    .clk         (clk_pix),
    .rst         (rst_pix),
    .h_count     (h_count),
    .h_sync      (hsync_n),
    .end_of_line (eol)
  );
  
// clock starts low and has a frequency of 25mhz, simulating the clock on board
initial clk_pix = 0;
always #20 clk_pix = ~clk_pix;
// horizontal assertions
// h_count always in range
// creating a register for eol to simulate how it will be used in the actual circui
logic reg_eol;
always_ff@(posedge clk_pix or posedge rst_pix)begin
    if(rst_pix) reg_eol <= 0;
    else reg_eol <= eol;
end

assert property (@(posedge clk_pix) disable iff (rst_pix)
  h_count < 800
) else $fatal(1,"h_count out of range");

// h_count increments by 1 each cycle except wrap
assert property (@(posedge clk_pix) disable iff (rst_pix)
  (h_count < 798) |=> (h_count == $past(h_count)+1)
) else $fatal(1,"h_count failed to increment");

// h_count wraps
assert property (@(posedge clk_pix) disable iff (rst_pix)
  (h_count == 799) |=> (h_count == 0)
) else $fatal(1,"h_count failed to wrap");

// eol pulse: high for exactly 1 cycle at last count
assert property (@(posedge clk_pix) disable iff (rst_pix)
  (h_count == 799) |-> (eol ##1 !eol)
) else $fatal(1,"eol pulse error");

// hsync low only during [656..751]
assert property (@(posedge clk_pix) disable iff (rst_pix)
  (h_count inside {[656:751]}) |-> (hsync_n == 0)
) else $fatal(1,"hsync_n not low in sync window");

assert property (@(posedge clk_pix) disable iff (rst_pix)
  !(h_count inside {[656:751]}) |-> (hsync_n == 1)
) else $fatal(1,"hsync_n not high outside sync window");

// vertical assertions
// v_count always in range
assert property (@(posedge clk_pix) disable iff (rst_pix)
  v_count < 525
) else $fatal(1,"v_count out of range");

// v_count increments only on eol
assert property (@(posedge clk_pix) disable iff (rst_pix)
  !reg_eol |-> (v_count == $past(v_count))
) else $fatal(1,"v_count changed without eol");

// v_count increments by 1 on eol except wrap
assert property (@(posedge clk_pix) disable iff (rst_pix)
  (eol && $past(v_count) != 524) |=> (v_count == $past(v_count)+1)
) else $fatal(1,"v_count increment error");

// v_count wraps at end of frame
assert property (@(posedge clk_pix) disable iff (rst_pix)
  (eol && $past(v_count) == 524) |=> (v_count == 0)
) else $fatal(1,"v_count failed to wrap");

// v_visible is true when v_count < 480
assert property (@(posedge clk_pix) disable iff (rst_pix)
  v_visible == (v_count < 480)
) else $fatal(1,"v_visible mismatch");

// vsync low only during [490..491]
assert property (@(posedge clk_pix) disable iff (rst_pix)
  (v_count inside {[490:491]}) |-> (vsync_n == 0)
) else $fatal(1,"vsync_n not low in sync window");

assert property (@(posedge clk_pix) disable iff (rst_pix)
  !(v_count inside {[490:491]}) |-> (vsync_n == 1)
) else $fatal(1,"vsync_n not high outside sync window");

// eof pulse at last line's eol
assert property (@(posedge clk_pix) disable iff (rst_pix)
  (eol && v_count == 524) |=> (eof_pulse_pix ##1 !eof_pulse_pix)
) else $fatal(1,"eof pulse error");

// vblank_start pulses at line 479's eol
assert property (@(posedge clk_pix) disable iff (rst_pix)
  (eol && v_count == 479) |=> (vblank_start_pix ##1 !vblank_start_pix)
) else $fatal(1,"vblank_start pulse error");

// vblank_toggle toggles exactly at line 479's eol
assert property (@(posedge clk_pix) disable iff (rst_pix)
  (eol && v_count == 479) |=> (vblank_toggle_pix != $past(vblank_toggle_pix))
) else $fatal(1,"vblank_toggle did not toggle");

// vblank_toggle holds otherwise
assert property (@(posedge clk_pix) disable iff (rst_pix)
  !(eol && v_count == 479) |=> (vblank_toggle_pix == $past(vblank_toggle_pix))
) else $fatal(1,"vblank_toggle changed unexpectedly");


initial begin
    rst_pix = 1;
    #40 rst_pix = 0;
    
    // run long enough for 2 full frames
    repeat (2 * 800 * 525) @(posedge clk_pix);
    $display("Simulation Complete");
    $finish;
    
end
endmodule

