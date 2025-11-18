// APB Testbench
`timescale 1ns/1ps

module apb_tb;
    reg clk;
    reg rst_n;

    // Master control interface
    reg req;
    reg wr;
    reg [15:0] addr;
    reg [31:0] wdata;
    wire [31:0] rdata;
    wire ready;

    // APB bus
    wire [15:0] PADDR;
    wire PSEL;
    wire PENABLE;
    wire PWRITE;
    wire [31:0] PWDATA;
    wire [31:0] PRDATA;
    wire PREADY;
    wire PSLVERR;

    // Instantiate master
    apb_master #(
        .ADDR_WIDTH(16),
        .DATA_WIDTH(32)
    ) master (
        .clk(clk),
        .rst_n(rst_n),
        .req(req),
        .wr(wr),
        .addr(addr),
        .wdata(wdata),
        .rdata(rdata),
        .ready(ready),
        .PADDR(PADDR),
        .PSEL(PSEL),
        .PENABLE(PENABLE),
        .PWRITE(PWRITE),
        .PWDATA(PWDATA),
        .PRDATA(PRDATA),
        .PREADY(PREADY),
        .PSLVERR(PSLVERR)
    );

    // Instantiate slave
    apb_slave #(
        .ADDR_WIDTH(16),
        .DATA_WIDTH(32),
        .MEM_DEPTH(256)
    ) slave (
        .clk(clk),
        .rst_n(rst_n),
        .PADDR(PADDR),
        .PSEL(PSEL),
        .PENABLE(PENABLE),
        .PWRITE(PWRITE),
        .PWDATA(PWDATA),
        .PRDATA(PRDATA),
        .PREADY(PREADY),
        .PSLVERR(PSLVERR)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    integer i;
    integer errors;
    reg [31:0] test_data;

    // Test stimulus
    initial begin
        $display("========================================");
        $display("Starting APB Test");
        $display("========================================");
        errors = 0;
        rst_n = 0;
        req = 0;
        wr = 0;
        addr = 0;
        wdata = 0;

        #20 rst_n = 1;
        #10;

        // Test 1: Single write
        $display("\nTest 1: Single write to address 0x0004");
        @(posedge clk);
        addr = 16'h0004;
        wdata = 32'hDEADBEEF;
        wr = 1;
        req = 1;
        @(posedge clk);
        req = 0;

        wait(ready);
        @(posedge clk);
        if (!PSLVERR)
            $display("PASS: Write completed successfully");
        else begin
            $display("FAIL: Write error detected");
            errors = errors + 1;
        end

        #50;

        // Test 2: Read back the same address
        $display("\nTest 2: Read from address 0x0004");
        @(posedge clk);
        addr = 16'h0004;
        wr = 0;
        req = 1;
        @(posedge clk);
        req = 0;

        wait(ready);
        @(posedge clk);
        if (rdata == 32'hDEADBEEF && !PSLVERR) begin
            $display("PASS: Read data matches (0x%h)", rdata);
        end else begin
            $display("FAIL: Expected 0xDEADBEEF, got 0x%h", rdata);
            errors = errors + 1;
        end

        #50;

        // Test 3: Multiple writes to sequential addresses
        $display("\nTest 3: Write to 8 sequential addresses");
        for (i = 0; i < 8; i = i + 1) begin
            @(posedge clk);
            addr = i * 4;  // Word-aligned addresses
            wdata = 32'hA0000000 + i;
            wr = 1;
            req = 1;
            @(posedge clk);
            req = 0;

            wait(ready);
            @(posedge clk);

            if (!PSLVERR)
                $display("PASS: Write %0d to address 0x%h", i, i*4);
            else begin
                $display("FAIL: Write error at address 0x%h", i*4);
                errors = errors + 1;
            end
            #20;
        end

        #50;

        // Test 4: Read back sequential addresses
        $display("\nTest 4: Read from 8 sequential addresses");
        for (i = 0; i < 8; i = i + 1) begin
            @(posedge clk);
            addr = i * 4;
            wr = 0;
            req = 1;
            @(posedge clk);
            req = 0;

            wait(ready);
            @(posedge clk);

            test_data = 32'hA0000000 + i;
            if (rdata == test_data && !PSLVERR) begin
                $display("PASS: Read data matches at address 0x%h (0x%h)", i*4, rdata);
            end else begin
                $display("FAIL: At address 0x%h, expected 0x%h, got 0x%h", i*4, test_data, rdata);
                errors = errors + 1;
            end
            #20;
        end

        #50;

        // Test 5: Back-to-back transactions
        $display("\nTest 5: Back-to-back write transactions");
        @(posedge clk);
        addr = 16'h0100;
        wdata = 32'h12345678;
        wr = 1;
        req = 1;
        @(posedge clk);
        req = 0;
        wait(ready);

        // Immediately start next transaction
        @(posedge clk);
        addr = 16'h0104;
        wdata = 32'h9ABCDEF0;
        req = 1;
        @(posedge clk);
        req = 0;
        wait(ready);

        $display("PASS: Back-to-back transactions completed");

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
        $dumpfile("apb_tb.vcd");
        $dumpvars(0, apb_tb);
    end

endmodule
