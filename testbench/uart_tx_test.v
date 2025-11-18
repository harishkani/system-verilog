// Minimal TX test
`timescale 1ns/1ps

module uart_tx_test;
    reg clk, rst_n, start;
    reg [7:0] data_in;
    wire tx, busy;

    uart_tx_working #(.CLKS_PER_BIT(10)) dut (  // Use smaller count for faster test
        .clk(clk), .rst_n(rst_n), .data_in(data_in),
        .start(start), .tx(tx), .busy(busy)
    );

    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 10ns period
    end

    initial begin
        $display("TX Only Test");
        rst_n = 1;
        start = 0;
        data_in = 8'hAA;

        #20 rst_n = 0;
        #20 rst_n = 1;
        #20;

        $display("Time=%0t: Before start, state=%0d", $time, dut.state);

        start = 1;
        #10;  // Wait one clock
        $display("Time=%0t: After start high, state=%0d", $time, dut.state);

        start = 0;
        #10;
        $display("Time=%0t: After start low, state=%0d, tx=%b", $time, dut.state, tx);

        #200;
        $display("Time=%0t: After delay, state=%0d, tx=%b", $time, dut.state, tx);

        if (dut.state != 0 || tx == 0)
            $display("PASS: TX is working");
        else
            $display("FAIL: TX never started");

        $finish;
    end

endmodule
