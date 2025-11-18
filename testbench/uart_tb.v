// UART Testbench
`timescale 1ns/1ps

module uart_tb;
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
    reg [7:0] expected_data;

    // Instantiate TX
    uart_tx #(
        .CLK_FREQ(1_000_000),
        .BAUD_RATE(10_000),  // Changed to 10kHz for clean division
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
        .BAUD_RATE(10_000),  // Changed to 10kHz for clean division
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

    // Test stimulus
    initial begin
        $display("========================================");
        $display("Starting UART Test");
        $display("========================================");
        rst_n = 0;
        tx_valid = 0;
        tx_data = 0;
        parity_mode = 2'b00;

        #2000 rst_n = 1;
        #2000;

        // Test 1: Send 0xA5
        $display("\nTest 1: Sending 0xA5 (no parity)");
        tx_data = 8'hA5;
        tx_valid = 1;
        @(posedge clk);
        tx_valid = 0;

        wait(rx_valid);
        @(posedge clk);
        if (rx_data == 8'hA5 && !rx_error)
            $display("PASS: Received 0x%h", rx_data);
        else
            $display("FAIL: Received 0x%h, error=%b", rx_data, rx_error);

        #50000;

        // Test 2: Send multiple bytes
        $display("\nTest 2: Sending multiple bytes");
        repeat(5) begin
            wait(tx_ready);
            tx_data = $random;
            expected_data = tx_data;
            $display("Sending: 0x%h", tx_data);
            tx_valid = 1;
            @(posedge clk);
            tx_valid = 0;

            wait(rx_valid);
            @(posedge clk);
            if (rx_data == expected_data && !rx_error)
                $display("PASS: Received 0x%h", rx_data);
            else
                $display("FAIL: Expected 0x%h, got 0x%h, error=%b", expected_data, rx_data, rx_error);
            #10000;
        end

        #50000;
        $display("\n========================================");
        $display("UART Test Complete");
        $display("========================================");
        $finish;
    end

    // Optional VCD dump
    initial begin
        $dumpfile("uart_tb.vcd");
        $dumpvars(0, uart_tb);
    end

endmodule
