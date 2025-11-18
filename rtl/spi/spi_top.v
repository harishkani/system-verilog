// SPI Top-Level Module
// Full-duplex SPI master with configurable mode
// Usage: Simple interface for SPI communication

module spi_top #(
    parameter CLK_DIV = 4,     // System clock divider (must be even, >= 2)
    parameter CPOL = 0,        // Clock polarity: 0=idle low, 1=idle high
    parameter CPHA = 0         // Clock phase: 0=sample on first edge, 1=sample on second edge
) (
    // System signals
    input wire clk,
    input wire rst_n,

    // Data interface
    input wire [7:0] tx_data,
    input wire tx_valid,
    output wire [7:0] rx_data,
    output wire rx_valid,

    // SPI physical interface (master mode)
    output wire spi_sclk,
    output wire spi_mosi,
    input wire spi_miso,
    output wire spi_cs_n
);

    // Instantiate SPI master
    spi_master #(
        .CLK_DIV(CLK_DIV),
        .CPOL(CPOL),
        .CPHA(CPHA)
    ) u_spi_master (
        .clk(clk),
        .rst_n(rst_n),
        .tx_data(tx_data),
        .tx_valid(tx_valid),
        .rx_data(rx_data),
        .rx_valid(rx_valid),
        .sclk(spi_sclk),
        .mosi(spi_mosi),
        .miso(spi_miso),
        .cs_n(spi_cs_n)
    );

endmodule
