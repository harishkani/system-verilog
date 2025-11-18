// AXI Lite Testbench
`timescale 1ns/1ps

module axi_lite_tb;
    reg clk;
    reg rst_n;

    // Master control
    reg req;
    reg wr;
    reg [31:0] addr;
    reg [31:0] wdata;
    reg [3:0] wstrb;
    wire [31:0] rdata;
    wire ready;
    wire resp_ok;

    // AXI Lite signals
    wire [31:0] AWADDR;
    wire AWVALID;
    wire AWREADY;
    wire [31:0] WDATA;
    wire [3:0] WSTRB;
    wire WVALID;
    wire WREADY;
    wire [1:0] BRESP;
    wire BVALID;
    wire BREADY;
    wire [31:0] ARADDR;
    wire ARVALID;
    wire ARREADY;
    wire [31:0] RDATA;
    wire [1:0] RRESP;
    wire RVALID;
    wire RREADY;

    // Instantiate master
    axi_lite_master #(
        .ADDR_WIDTH(32),
        .DATA_WIDTH(32)
    ) master (
        .clk(clk),
        .rst_n(rst_n),
        .req(req),
        .wr(wr),
        .addr(addr),
        .wdata(wdata),
        .wstrb(wstrb),
        .rdata(rdata),
        .ready(ready),
        .resp_ok(resp_ok),
        .AWADDR(AWADDR),
        .AWVALID(AWVALID),
        .AWREADY(AWREADY),
        .WDATA(WDATA),
        .WSTRB(WSTRB),
        .WVALID(WVALID),
        .WREADY(WREADY),
        .BRESP(BRESP),
        .BVALID(BVALID),
        .BREADY(BREADY),
        .ARADDR(ARADDR),
        .ARVALID(ARVALID),
        .ARREADY(ARREADY),
        .RDATA(RDATA),
        .RRESP(RRESP),
        .RVALID(RVALID),
        .RREADY(RREADY)
    );

    // Instantiate slave
    axi_lite_slave_simple #(
        .ADDR_WIDTH(32),
        .DATA_WIDTH(32),
        .MEM_DEPTH(256)
    ) slave (
        .clk(clk),
        .rst_n(rst_n),
        .AWADDR(AWADDR),
        .AWVALID(AWVALID),
        .AWREADY(AWREADY),
        .WDATA(WDATA),
        .WSTRB(WSTRB),
        .WVALID(WVALID),
        .WREADY(WREADY),
        .BRESP(BRESP),
        .BVALID(BVALID),
        .BREADY(BREADY),
        .ARADDR(ARADDR),
        .ARVALID(ARVALID),
        .ARREADY(ARREADY),
        .RDATA(RDATA),
        .RRESP(RRESP),
        .RVALID(RVALID),
        .RREADY(RREADY)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    integer errors;
    integer i;
    reg [31:0] test_data;

    // Test stimulus
    initial begin
        $display("========================================");
        $display("AXI Lite Test");
        $display("========================================");
        errors = 0;
        rst_n = 0;
        req = 0;
        wr = 0;
        addr = 0;
        wdata = 0;
        wstrb = 4'b1111;

        #20 rst_n = 1;
        #10;

        // Test 1: Single write
        $display("\nTest 1: Write 0xCAFEBABE to address 0x10");
        @(posedge clk);
        addr = 32'h00000010;
        wdata = 32'hCAFEBABE;
        wstrb = 4'b1111;
        wr = 1;
        req = 1;
        @(posedge clk);
        req = 0;

        wait(ready);
        @(posedge clk);
        if (resp_ok)
            $display("PASS: Write successful");
        else begin
            $display("FAIL: Write failed");
            errors = errors + 1;
        end

        #50;

        // Test 2: Read back
        $display("\nTest 2: Read from address 0x10");
        @(posedge clk);
        addr = 32'h00000010;
        wr = 0;
        req = 1;
        @(posedge clk);
        req = 0;

        wait(ready);
        @(posedge clk);
        if (resp_ok && rdata == 32'hCAFEBABE) begin
            $display("PASS: Read data matches (0x%h)", rdata);
        end else begin
            $display("FAIL: Expected 0xCAFEBABE, got 0x%h, resp_ok=%b", rdata, resp_ok);
            errors = errors + 1;
        end

        #50;

        // Test 3: Multiple writes
        $display("\nTest 3: Write to 8 addresses");
        for (i = 0; i < 8; i = i + 1) begin
            @(posedge clk);
            addr = i * 4;
            wdata = 32'hA0000000 + i;
            wstrb = 4'b1111;
            wr = 1;
            req = 1;
            @(posedge clk);
            req = 0;

            wait(ready);
            @(posedge clk);

            if (resp_ok)
                $display("PASS: Write %0d to address 0x%h", i, i*4);
            else begin
                $display("FAIL: Write %0d failed", i);
                errors = errors + 1;
            end
            #20;
        end

        #50;

        // Test 4: Multiple reads
        $display("\nTest 4: Read from 8 addresses");
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
            if (resp_ok && rdata == test_data) begin
                $display("PASS: Read address 0x%h = 0x%h", i*4, rdata);
            end else begin
                $display("FAIL: At 0x%h, expected 0x%h, got 0x%h", i*4, test_data, rdata);
                errors = errors + 1;
            end
            #20;
        end

        #50;

        // Test 5: Byte write (partial strobes)
        $display("\nTest 5: Byte write with WSTRB");
        @(posedge clk);
        addr = 32'h00000020;
        wdata = 32'h00000000;
        wstrb = 4'b1111;
        wr = 1;
        req = 1;
        @(posedge clk);
        req = 0;
        wait(ready);

        // Write only lower byte
        @(posedge clk);
        addr = 32'h00000020;
        wdata = 32'h000000FF;
        wstrb = 4'b0001;  // Only byte 0
        wr = 1;
        req = 1;
        @(posedge clk);
        req = 0;
        wait(ready);

        // Read back
        @(posedge clk);
        addr = 32'h00000020;
        wr = 0;
        req = 1;
        @(posedge clk);
        req = 0;
        wait(ready);
        @(posedge clk);

        if (rdata == 32'h000000FF) begin
            $display("PASS: Byte strobe write successful (0x%h)", rdata);
        end else begin
            $display("FAIL: Expected 0x000000FF, got 0x%h", rdata);
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

    // VCD dump
    initial begin
        $dumpfile("axi_lite_tb.vcd");
        $dumpvars(0, axi_lite_tb);
    end

endmodule
