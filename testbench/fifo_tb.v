// FIFO Testbench
`timescale 1ns/1ps

module fifo_tb;
    reg clk;
    reg rst_n;
    reg [7:0] wr_data;
    reg wr_en;
    wire full;
    wire almost_full;
    wire [7:0] rd_data;
    reg rd_en;
    wire empty;
    wire almost_empty;
    wire [4:0] count;

    // Instantiate FIFO
    sync_fifo #(
        .DATA_WIDTH(8),
        .DEPTH(16)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .wr_data(wr_data),
        .wr_en(wr_en),
        .full(full),
        .almost_full(almost_full),
        .rd_data(rd_data),
        .rd_en(rd_en),
        .empty(empty),
        .almost_empty(almost_empty),
        .count(count)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    integer i;
    integer errors;

    // Test stimulus
    initial begin
        $display("========================================");
        $display("Starting FIFO Test");
        $display("========================================");
        errors = 0;
        rst_n = 0;
        wr_en = 0;
        rd_en = 0;
        wr_data = 0;

        #20 rst_n = 1;
        #10;

        // Test 1: Fill FIFO
        $display("\nTest 1: Filling FIFO with 16 values");
        for (i = 0; i < 16; i = i + 1) begin
            @(posedge clk);
            wr_data = i;
            wr_en = 1;
        end
        @(posedge clk);
        wr_en = 0;

        if (full)
            $display("PASS: FIFO is full (count=%0d)", count);
        else begin
            $display("FAIL: FIFO should be full (count=%0d)", count);
            errors = errors + 1;
        end

        #50;

        // Test 2: Empty FIFO and verify data
        $display("\nTest 2: Emptying FIFO and verifying data");
        for (i = 0; i < 16; i = i + 1) begin
            @(posedge clk);
            rd_en = 1;
            @(posedge clk);
            rd_en = 0;
            if (rd_data == i)
                $display("PASS: Read data %0d matches", i);
            else begin
                $display("FAIL: Expected %0d, got %0d", i, rd_data);
                errors = errors + 1;
            end
        end

        @(posedge clk);
        if (empty)
            $display("PASS: FIFO is empty (count=%0d)", count);
        else begin
            $display("FAIL: FIFO should be empty (count=%0d)", count);
            errors = errors + 1;
        end

        #50;

        // Test 3: Simultaneous read/write
        $display("\nTest 3: Simultaneous read/write");
        // First write some data
        for (i = 0; i < 8; i = i + 1) begin
            @(posedge clk);
            wr_data = 8'hAA + i;
            wr_en = 1;
        end
        @(posedge clk);
        wr_en = 0;

        $display("Count after writing 8 values: %0d", count);

        // Now simultaneous read and write
        for (i = 0; i < 10; i = i + 1) begin
            @(posedge clk);
            wr_data = 8'h50 + i;
            wr_en = 1;
            rd_en = 1;
        end
        @(posedge clk);
        wr_en = 0;
        rd_en = 0;

        $display("Count after simultaneous operations: %0d", count);
        if (count == 8)
            $display("PASS: Count maintained at 8");
        else begin
            $display("FAIL: Expected count 8, got %0d", count);
            errors = errors + 1;
        end

        #50;
        $display("\n========================================");
        if (errors == 0)
            $display("ALL TESTS PASSED!");
        else
            $display("TESTS FAILED: %0d errors", errors);
        $display("========================================");
        $finish;
    end

    // Optional VCD dump
    initial begin
        $dumpfile("fifo_tb.vcd");
        $dumpvars(0, fifo_tb);
    end

endmodule
