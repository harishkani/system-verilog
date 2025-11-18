// SPI Master Testbench
`timescale 1ns/1ps

module spi_tb;
    reg clk;
    reg rst_n;
    reg [7:0] tx_data;
    reg tx_valid;
    wire tx_ready;
    wire [7:0] rx_data;
    wire rx_valid;
    wire sclk;
    wire mosi;
    reg miso;
    wire cs_n;
    reg cpol;
    reg cpha;

    // Instantiate SPI master
    spi_master #(
        .DATA_WIDTH(8),
        .CLK_DIV(4)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .tx_data(tx_data),
        .tx_valid(tx_valid),
        .tx_ready(tx_ready),
        .rx_data(rx_data),
        .rx_valid(rx_valid),
        .sclk(sclk),
        .mosi(mosi),
        .miso(miso),
        .cs_n(cs_n),
        .cpol(cpol),
        .cpha(cpha)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Test stimulus
    initial begin
        $display("Starting SPI Master Test");
        rst_n = 0;
        tx_valid = 0;
        tx_data = 0;
        miso = 0;
        cpol = 0;
        cpha = 0;

        #20 rst_n = 1;
        #20;

        // Test 1: Send 0xA5
        $display("Test 1: Sending 0xA5");
        @(posedge clk);
        tx_data = 8'hA5;
        tx_valid = 1;
        @(posedge clk);
        tx_valid = 0;

        // Wait for transfer to complete
        @(posedge rx_valid);
        #20;
        $display("Transfer complete");

        #100;
        $display("SPI Master Test Complete");
        $finish;
    end

    // Monitor
    initial begin
        $monitor("Time=%0t cs_n=%b sclk=%b mosi=%b tx_ready=%b rx_valid=%b",
                 $time, cs_n, sclk, mosi, tx_ready, rx_valid);
    end

    // Optional VCD dump for waveform viewing
    initial begin
        $dumpfile("spi_tb.vcd");
        $dumpvars(0, spi_tb);
    end

endmodule
