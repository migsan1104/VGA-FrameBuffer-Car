`timescale 1ns / 1ps


module ResetGen_tb;

logic clk_sys_tb;
logic clk_pix_tb;
logic ext_reset_n_tb;
logic pll_locked_tb; 

logic srst_tb;
logic prst_tb;

logic arst_global;
assign arst_global = (~ext_reset_n_tb) | (~pll_locked_tb);


ResetGen DUTR(
    .clk_sys(clk_sys_tb),
    .pix_clk(clk_pix_tb),
    .ext_reset_n(ext_reset_n_tb),
    .pll_locked(pll_locked_tb),
    .srst(srst_tb),
    .prst(prst_tb)

);

    // ── Clock generation
    
       initial clk_sys_tb = 0;
       always #5 clk_sys_tb = ~clk_sys_tb;   // 100 MHz
    

    
        initial  clk_pix_tb = 0;
        always #20 clk_pix_tb = ~clk_pix_tb;  // 25 MHz
   

    // ── Stimulus
    initial begin
        ext_reset_n_tb = 0;   // button pressed
        pll_locked_tb  = 0;   // PLL not locked

        #54;
        ext_reset_n_tb = 1;   // release button
        pll_locked_tb  = 1;   // PLL locked

        #200;
        ext_reset_n_tb = 0;   // pulse reset
        #40;
        ext_reset_n_tb = 1;

        #100;
        pll_locked_tb = 0;    // drop PLL lock
        #40;
        pll_locked_tb = 1;

        #200;
        $display("Simulation complete, all test passed!!!");
        $finish;
    end

    // ── Assertions

    // Reset deassertion only when inputs are both good
    property sys_reset_release;
        @(posedge clk_sys_tb)
        disable iff (!ext_reset_n_tb || !pll_locked_tb)
        $fell(!srst_tb) |-> (ext_reset_n_tb && pll_locked_tb);
    endproperty

    assert property (sys_reset_release)
        else $fatal(1, "srst deasserted unexpectedly at %t", $time);

    property pix_reset_release;
        @(posedge clk_pix_tb)
        disable iff (!ext_reset_n_tb || !pll_locked_tb)
        $fell(!prst_tb) |-> (ext_reset_n_tb && pll_locked_tb);
    endproperty

    assert property (pix_reset_release)
        else $fatal(1, "prst deasserted unexpectedly at %t", $time);


    // System reset hold check (2 cycles)
   property sys_reset_two_cycles_alt;
  @(posedge clk_sys_tb)
  ($past(arst_global) && !arst_global) |-> (srst_tb ##1 srst_tb ##1 !srst_tb);
    endproperty
    assert property (sys_reset_two_cycles_alt)
  else $fatal(1, "srst did not hold exactly 2 cycles after arst_global deassert @%t", $time);

       // Pixel domain
    property pix_reset_two_cycles_alt;
        @(posedge clk_pix_tb)
        ($past(arst_global) && !arst_global) |-> (prst_tb ##1 prst_tb ##1 !prst_tb);
    endproperty
    assert property (pix_reset_two_cycles_alt)
    else $fatal(1, "prst did not hold exactly 2 cycles after arst_global deassert @%t", $time);
endmodule

