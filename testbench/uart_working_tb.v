// UART Working Testbench
`timescale 1ns/1ps

module uart_working_tb;
    reg clk;
    reg rst_n;
    reg [7:0] tx_data;
    reg tx_start;
    wire tx_line;
    wire tx_busy;
    wire [7:0] rx_data;
    wire rx_valid;

    uart_tx_working #(
        .CLKS_PER_BIT(100)
    ) tx_inst (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(tx_data),
        .start(tx_start),
        .tx(tx_line),
        .busy(tx_busy)
    );

    uart_rx_working #(
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
        forever #500 clk = ~clk;  // 1MHz clock, 1us period
    end

    integer errors;
    integer i;
    reg [7:0] test_data;

    initial begin
        $display("========================================");
        $display("UART Working Test");
        $display("Clock period: 1us, Baud time: 100us");
        $display("========================================");
        errors = 0;
        rst_n = 0;
        tx_start = 0;
        tx_data = 0;

        #2000 rst_n = 1;
        #2000;

        // Test 1: Send 0xAA
        $display("\nTest 1: Sending 0xAA (10101010)");
        tx_data = 8'hAA;
        tx_start = 1;
        #1000;  // Hold start for one clock
        tx_start = 0;

        // Wait for full transmission: 10 bits * 100 clocks/bit * 1us/clock = 1000us + margin
        #1050000;

        $display("Final: rx_state=%0d, rx_data=0x%h, rx_valid=%b",
                 rx_inst.state, rx_data, rx_valid);

        if (rx_data == 8'hAA) begin
            $display("PASS: Received 0x%h", rx_data);
        end else begin
            $display("FAIL: Expected 0xAA, got 0x%h", rx_data);
            errors = errors + 1;
        end

        #10000;

        // Test 2: Send 0x55
        $display("\nTest 2: Sending 0x55 (01010101)");
        tx_data = 8'h55;
        tx_start = 1;
        #1000;
        tx_start = 0;
        #1050000;

        if (rx_data == 8'h55) begin
            $display("PASS: Received 0x%h", rx_data);
        end else begin
            $display("FAIL: Expected 0x55, got 0x%h", rx_data);
            errors = errors + 1;
        end

        #10000;

        // Test 3: Send 0xFF
        $display("\nTest 3: Sending 0xFF (all ones)");
        tx_data = 8'hFF;
        tx_start = 1;
        #1000;
        tx_start = 0;
        #1050000;

        if (rx_data == 8'hFF) begin
            $display("PASS: Received 0x%h", rx_data);
        end else begin
            $display("FAIL: Expected 0xFF, got 0x%h", rx_data);
            errors = errors + 1;
        end

        #10000;

        // Test 4: Send 0x00
        $display("\nTest 4: Sending 0x00 (all zeros)");
        tx_data = 8'h00;
        tx_start = 1;
        #1000;
        tx_start = 0;
        #1050000;

        if (rx_data == 8'h00) begin
            $display("PASS: Received 0x%h", rx_data);
        end else begin
            $display("FAIL: Expected 0x00, got 0x%h", rx_data);
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
        $dumpfile("uart_working_tb.vcd");
        $dumpvars(0, uart_working_tb);
    end

endmodule
