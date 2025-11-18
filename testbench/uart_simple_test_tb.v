// Test simplified UART
`timescale 1ns/1ps

module uart_simple_test_tb;
    reg clk;
    reg rst_n;
    reg [7:0] tx_data;
    reg tx_start;
    wire tx_line;
    wire tx_busy;
    wire [7:0] rx_data;
    wire rx_valid;

    uart_simple_tx #(
        .CLKS_PER_BIT(100)
    ) tx_inst (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(tx_data),
        .start(tx_start),
        .tx(tx_line),
        .busy(tx_busy)
    );

    uart_simple_rx #(
        .CLKS_PER_BIT(100)
    ) rx_inst (
        .clk(clk),
        .rst_n(rst_n),
        .rx(tx_line),
        .data_out(rx_data),
        .valid(rx_valid)
    );

    initial begin
        clk = 0;
        forever #500 clk = ~clk;
    end

    integer errors;

    initial begin
        $display("========================================");
        $display("Simple UART Test");
        $display("========================================");
        errors = 0;
        rst_n = 0;
        tx_start = 0;
        tx_data = 0;

        #2000 rst_n = 1;
        #2000;

        // Test 1: Send 0xAA
        $display("\nTest 1: Sending 0xAA");
        tx_data = 8'hAA;
        tx_start = 1;
        @(posedge clk);
        tx_start = 0;

        // Wait for transmission to complete
        #200000; // Wait 200us

        if (rx_valid) begin
            if (rx_data == 8'hAA) begin
                $display("PASS: Received 0x%h", rx_data);
            end else begin
                $display("FAIL: Expected 0xAA, got 0x%h", rx_data);
                errors = errors + 1;
            end
        end else begin
            $display("FAIL: rx_valid never went high, last rx_data=0x%h", rx_data);
            errors = errors + 1;
        end

        $display("\n========================================");
        if (errors == 0)
            $display("ALL TESTS PASSED!");
        else
            $display("TESTS FAILED: %0d errors", errors);
        $display("========================================");
        $finish;
    end

    initial begin
        $dumpfile("uart_simple_test.vcd");
        $dumpvars(0, uart_simple_test_tb);
    end

endmodule
