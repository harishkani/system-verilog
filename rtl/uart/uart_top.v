// UART Top-Level Module
// Combines verified TX and RX modules
// Usage: Instantiate this module for full-duplex UART communication

module uart_top #(
    parameter CLKS_PER_BIT = 100  // System clock cycles per UART bit
                                   // Example: 1 MHz clock / 10 kbps = 100
                                   // Example: 50 MHz clock / 115200 bps = 434
) (
    // System signals
    input wire clk,
    input wire rst_n,

    // TX interface
    input wire [7:0] tx_data,
    input wire tx_start,
    output wire tx_busy,

    // RX interface
    output wire [7:0] rx_data,
    output wire rx_valid,

    // UART physical interface
    input wire uart_rx,
    output wire uart_tx
);

    // Instantiate TX module
    uart_tx_working #(
        .CLKS_PER_BIT(CLKS_PER_BIT)
    ) u_tx (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(tx_data),
        .start(tx_start),
        .tx(uart_tx),
        .busy(tx_busy)
    );

    // Instantiate RX module
    uart_rx_working #(
        .CLKS_PER_BIT(CLKS_PER_BIT)
    ) u_rx (
        .clk(clk),
        .rst_n(rst_n),
        .rx(uart_rx),
        .data_out(rx_data),
        .valid(rx_valid)
    );

endmodule
