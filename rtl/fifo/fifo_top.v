// FIFO Top-Level Module
// Synchronous FIFO with configurable depth and width
// Usage: Simple buffering interface

module fifo_top #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 16
) (
    // System signals
    input wire clk,
    input wire rst_n,

    // Write interface
    input wire [DATA_WIDTH-1:0] wr_data,
    input wire wr_en,
    output wire full,

    // Read interface
    output wire [DATA_WIDTH-1:0] rd_data,
    input wire rd_en,
    output wire empty,

    // Status
    output wire [$clog2(DEPTH):0] count
);

    // Instantiate synchronous FIFO
    sync_fifo #(
        .DATA_WIDTH(DATA_WIDTH),
        .DEPTH(DEPTH)
    ) u_fifo (
        .clk(clk),
        .rst_n(rst_n),
        .wr_data(wr_data),
        .wr_en(wr_en),
        .full(full),
        .rd_data(rd_data),
        .rd_en(rd_en),
        .empty(empty),
        .count(count)
    );

endmodule
