module ResetGen (
    input  logic clk_sys,
    input  logic pix_clk,
    input  logic ext_reset_n,  // external reset button, active-low
    input  logic pll_locked,   // from PLL/MMCM

    output logic srst,         // active-high, sync to clk_sys
    output logic prst          // active-high, sync to pix_clk
);
    // global async reset: asserted if button pressed or PLL not locked
    logic arst_global;
    assign arst_global = (~ext_reset_n) | (~pll_locked);

    // pixel and system synchronizers
    ResetSync u_sys_sync (
        .clk  (clk_sys),
        .arst (arst_global),
        .srst (srst)
    );

    ResetSync u_pix_sync (
        .clk  (pix_clk),
        .arst (arst_global),
        .srst (prst)
    );
endmodule
