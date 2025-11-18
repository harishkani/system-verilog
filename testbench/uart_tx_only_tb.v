// Test TX only
`timescale 1ns/1ps

module uart_tx_only_tb;
    reg clk;
    reg rst_n;
    reg [7:0] tx_data;
    reg tx_valid;
    wire tx_ready;
    wire tx;

    uart_tx #(
        .CLK_FREQ(1_000_000),
        .BAUD_RATE(10_000),
        .DATA_BITS(8),
        .STOP_BITS(1)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .tx_data(tx_data),
        .tx_valid(tx_valid),
        .tx_ready(tx_ready),
        .tx(tx),
        .parity_mode(2'b00)
    );

    initial begin
        clk = 0;
        forever #500 clk = ~clk;
    end

    initial begin
        $display("TX Test - Sending 0xAA (10101010 binary, LSB first)");
        $display("Expected bit pattern: 1(idle) 0(start) 0,1,0,1,0,1,0,1 1(stop)");
        rst_n = 0;
        tx_valid = 0;
        tx_data = 0;

        #2000 rst_n = 1;
        #2000;

        tx_data = 8'hAA;
        tx_valid = 1;
        @(posedge clk);
        tx_valid = 0;

        #2000000;
        $finish;
    end

    // Monitor TX output
    initial begin
        $monitor("Time=%0t tx=%b tx_ready=%b", $time, tx, tx_ready);
    end

    initial begin
        $dumpfile("uart_tx_only.vcd");
        $dumpvars(0, uart_tx_only_tb);
    end

endmodule
