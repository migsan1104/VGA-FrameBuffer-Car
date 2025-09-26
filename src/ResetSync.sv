// 2 flip flop synchronizer made for reset signal from board

module ResetSync (
    input  logic clk,     //  pixel or systemclock domain
    input  logic arst,    //  pixel or system async reset, active-high
    output logic srst     // pixel or system synced reset, active-high
);
    logic ff1;

    always_ff @(posedge clk) begin
        ff1 <= arst;
        srst <= ff1;
        
    end

    
endmodule
