// Simple UART Debug Testbench
`timescale 1ns/1ps

module uart_simple_tb;
    reg clk;
    reg rst_n;
    reg [7:0] tx_data;
    reg tx_valid;
    wire tx_ready;
    wire uart_line;
    wire [7:0] rx_data;
    wire rx_valid;
    wire rx_error;
    reg [1:0] parity_mode;

    // Instantiate TX
    uart_tx #(
        .CLK_FREQ(1_000_000),
        .BAUD_RATE(10_000),
        .DATA_BITS(8),
        .STOP_BITS(1)
    ) tx_inst (
        .clk(clk),
        .rst_n(rst_n),
        .tx_data(tx_data),
        .tx_valid(tx_valid),
        .tx_ready(tx_ready),
        .tx(uart_line),
        .parity_mode(parity_mode)
    );

    // Instantiate RX
    uart_rx #(
        .CLK_FREQ(1_000_000),
        .BAUD_RATE(10_000),
        .DATA_BITS(8),
        .STOP_BITS(1)
    ) rx_inst (
        .clk(clk),
        .rst_n(rst_n),
        .rx_data(rx_data),
        .rx_valid(rx_valid),
        .rx_error(rx_error),
        .rx(uart_line),
        .parity_mode(parity_mode)
    );

    // Clock generation (1 MHz)
    initial begin
        clk = 0;
        forever #500 clk = ~clk;
    end

    // Monitor signals
    initial begin
        $monitor("Time=%0t uart_line=%b rx_valid=%b rx_data=%h rx_error=%b",
                 $time, uart_line, rx_valid, rx_data, rx_error);
    end

    // Test stimulus
    initial begin
        $display("Simple UART Debug Test");
        rst_n = 0;
        tx_valid = 0;
        tx_data = 0;
        parity_mode = 2'b00;

        #2000 rst_n = 1;
        #2000;

        // Send single byte
        $display("\nSending 0xAA");
        tx_data = 8'hAA;
        tx_valid = 1;
        @(posedge clk);
        tx_valid = 0;

        // Wait for completion
        #2000000;

        $display("\nFinal: rx_data=%h, rx_valid=%b, rx_error=%b", rx_data, rx_valid, rx_error);
        $finish;
    end

    // VCD dump
    initial begin
        $dumpfile("uart_simple.vcd");
        $dumpvars(0, uart_simple_tb);
    end

endmodule
