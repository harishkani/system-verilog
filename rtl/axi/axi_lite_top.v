// AXI Lite Top-Level Module
// Connects master and slave with all 5 channels
// Usage: Example system showing master-slave connection

module axi_lite_top #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32,
    parameter MEM_DEPTH = 256
) (
    input wire clk,
    input wire rst_n,

    // Master control interface
    input wire req,
    input wire wr,
    input wire [ADDR_WIDTH-1:0] addr,
    input wire [DATA_WIDTH-1:0] wdata,
    input wire [3:0] wstrb,
    output wire ready,
    output wire resp_ok,
    output wire [DATA_WIDTH-1:0] rdata
);

    // AXI Lite 5-channel interface signals

    // Write Address Channel (AW)
    wire [ADDR_WIDTH-1:0] AWADDR;
    wire AWVALID;
    wire AWREADY;

    // Write Data Channel (W)
    wire [DATA_WIDTH-1:0] WDATA;
    wire [3:0] WSTRB;
    wire WVALID;
    wire WREADY;

    // Write Response Channel (B)
    wire [1:0] BRESP;
    wire BVALID;
    wire BREADY;

    // Read Address Channel (AR)
    wire [ADDR_WIDTH-1:0] ARADDR;
    wire ARVALID;
    wire ARREADY;

    // Read Data Channel (R)
    wire [DATA_WIDTH-1:0] RDATA;
    wire [1:0] RRESP;
    wire RVALID;
    wire RREADY;

    // Instantiate AXI Lite Master
    axi_lite_master #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
    ) u_master (
        .clk(clk),
        .rst_n(rst_n),

        // Control interface
        .req(req),
        .wr(wr),
        .addr(addr),
        .wdata(wdata),
        .wstrb(wstrb),
        .ready(ready),
        .resp_ok(resp_ok),
        .rdata(rdata),

        // AXI Lite Write Address Channel
        .AWADDR(AWADDR),
        .AWVALID(AWVALID),
        .AWREADY(AWREADY),

        // AXI Lite Write Data Channel
        .WDATA(WDATA),
        .WSTRB(WSTRB),
        .WVALID(WVALID),
        .WREADY(WREADY),

        // AXI Lite Write Response Channel
        .BRESP(BRESP),
        .BVALID(BVALID),
        .BREADY(BREADY),

        // AXI Lite Read Address Channel
        .ARADDR(ARADDR),
        .ARVALID(ARVALID),
        .ARREADY(ARREADY),

        // AXI Lite Read Data Channel
        .RDATA(RDATA),
        .RRESP(RRESP),
        .RVALID(RVALID),
        .RREADY(RREADY)
    );

    // Instantiate AXI Lite Slave (simplified version)
    axi_lite_slave_simple #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .MEM_DEPTH(MEM_DEPTH)
    ) u_slave (
        .clk(clk),
        .rst_n(rst_n),

        // AXI Lite Write Address Channel
        .AWADDR(AWADDR),
        .AWVALID(AWVALID),
        .AWREADY(AWREADY),

        // AXI Lite Write Data Channel
        .WDATA(WDATA),
        .WSTRB(WSTRB),
        .WVALID(WVALID),
        .WREADY(WREADY),

        // AXI Lite Write Response Channel
        .BRESP(BRESP),
        .BVALID(BVALID),
        .BREADY(BREADY),

        // AXI Lite Read Address Channel
        .ARADDR(ARADDR),
        .ARVALID(ARVALID),
        .ARREADY(ARREADY),

        // AXI Lite Read Data Channel
        .RDATA(RDATA),
        .RRESP(RRESP),
        .RVALID(RVALID),
        .RREADY(RREADY)
    );

endmodule
