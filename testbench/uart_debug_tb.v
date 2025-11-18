// UART Debug Testbench
`timescale 1ns/1ps

module uart_debug_tb;
    reg clk, rst_n;
    reg [7:0] tx_data;
    reg tx_start;
    wire tx_line;
    wire tx_busy;
    wire [7:0] rx_data;
    wire rx_valid;

    uart_tx_working #(.CLKS_PER_BIT(100)) tx_inst (
        .clk(clk), .rst_n(rst_n), .data_in(tx_data), .start(tx_start),
        .tx(tx_line), .busy(tx_busy)
    );

    uart_rx_working #(.CLKS_PER_BIT(100)) rx_inst (
        .clk(clk), .rst_n(rst_n), .rx(tx_line),
        .data_out(rx_data), .valid(rx_valid)
    );

    initial begin
        clk = 0;
        forever #500 clk = ~clk;
    end

    // Monitor signals (disabled for clarity)
    // initial begin
    //     $monitor("Time=%0t tx_line=%b tx_state=%0d rx_state=%0d rx_data=%h rx_valid=%b",
    //              $time, tx_line, tx_inst.state, rx_inst.state, rx_data, rx_valid);
    // end

    initial begin
        $display("UART Debug Test - Sending 0xAA");
        rst_n = 0;
        tx_start = 0;
        tx_data = 0;

        #2000 rst_n = 1;
        #2000;

        $display("Before start: tx_start=%b, tx_data=%h", tx_start, tx_data);
        tx_data = 8'hAA;
        tx_start = 1;
        $display("Asserting start: tx_start=%b, tx_data=%h", tx_start, tx_data);
        @(posedge clk);
        $display("After clock: tx_line=%b, tx_state=%0d", tx_line, tx_inst.state);
        tx_start = 0;

        #10000;
        $display("After 10us: tx_line=%b, tx_state=%0d", tx_line, tx_inst.state);

        #150000;  // Wait for full transmission

        $display("\nFinal: rx_data=0x%h, rx_valid=%b", rx_data, rx_valid);
        $finish;
    end

endmodule
