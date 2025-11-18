// Minimal AXI Lite Test
`timescale 1ns/1ps

module axi_lite_minimal_tb;
    reg clk, rst_n;
    reg req, wr;
    reg [31:0] addr, wdata;
    wire [31:0] rdata;
    wire ready, resp_ok;

    wire [31:0] AWADDR, WDATA, ARADDR, RDATA;
    wire AWVALID, AWREADY, WVALID, WREADY, BVALID, BREADY, ARVALID, ARREADY, RVALID, RREADY;
    wire [3:0] WSTRB;
    wire [1:0] BRESP, RRESP;

    axi_lite_master master (
        .clk(clk), .rst_n(rst_n),
        .req(req), .wr(wr), .addr(addr), .wdata(wdata), .wstrb(4'b1111),
        .rdata(rdata), .ready(ready), .resp_ok(resp_ok),
        .AWADDR(AWADDR), .AWVALID(AWVALID), .AWREADY(AWREADY),
        .WDATA(WDATA), .WSTRB(WSTRB), .WVALID(WVALID), .WREADY(WREADY),
        .BRESP(BRESP), .BVALID(BVALID), .BREADY(BREADY),
        .ARADDR(ARADDR), .ARVALID(ARVALID), .ARREADY(ARREADY),
        .RDATA(RDATA), .RRESP(RRESP), .RVALID(RVALID), .RREADY(RREADY)
    );

    axi_lite_slave_simple slave (
        .clk(clk), .rst_n(rst_n),
        .AWADDR(AWADDR), .AWVALID(AWVALID), .AWREADY(AWREADY),
        .WDATA(WDATA), .WSTRB(WSTRB), .WVALID(WVALID), .WREADY(WREADY),
        .BRESP(BRESP), .BVALID(BVALID), .BREADY(BREADY),
        .ARADDR(ARADDR), .ARVALID(ARVALID), .ARREADY(ARREADY),
        .RDATA(RDATA), .RRESP(RRESP), .RVALID(RVALID), .RREADY(RREADY)
    );

    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    initial begin
        $display("Minimal AXI Lite Test");
        $monitor("Time=%0t req=%b ready=%b AWVALID=%b AWREADY=%b WVALID=%b WREADY=%b BVALID=%b BREADY=%b",
                 $time, req, ready, AWVALID, AWREADY, WVALID, WREADY, BVALID, BREADY);

        rst_n = 0;
        req = 0;
        wr = 1;
        addr = 32'h10;
        wdata = 32'hABCD;

        #20 rst_n = 1;
        #20;

        $display("\nStarting write transaction");
        req = 1;
        @(posedge clk);
        req = 0;

        wait(ready);
        @(posedge clk);
        $display("PASS: Transaction completed at time=%0t", $time);

        $finish;
    end

endmodule
