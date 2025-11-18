// APB Top-Level Module
// Connects APB master and slave
// Usage: Example system showing APB master-slave connection

module apb_top #(
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
    output wire ready,
    output wire slverr,
    output wire [DATA_WIDTH-1:0] rdata
);

    // APB interface signals
    wire [ADDR_WIDTH-1:0] PADDR;
    wire PSEL;
    wire PENABLE;
    wire PWRITE;
    wire [DATA_WIDTH-1:0] PWDATA;
    wire PREADY;
    wire PSLVERR;
    wire [DATA_WIDTH-1:0] PRDATA;

    // Instantiate APB Master
    apb_master #(
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
        .ready(ready),
        .slverr(slverr),
        .rdata(rdata),

        // APB interface
        .PADDR(PADDR),
        .PSEL(PSEL),
        .PENABLE(PENABLE),
        .PWRITE(PWRITE),
        .PWDATA(PWDATA),
        .PREADY(PREADY),
        .PSLVERR(PSLVERR),
        .PRDATA(PRDATA)
    );

    // Instantiate APB Slave
    apb_slave #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .MEM_DEPTH(MEM_DEPTH)
    ) u_slave (
        .clk(clk),
        .rst_n(rst_n),

        // APB interface
        .PADDR(PADDR),
        .PSEL(PSEL),
        .PENABLE(PENABLE),
        .PWRITE(PWRITE),
        .PWDATA(PWDATA),
        .PREADY(PREADY),
        .PSLVERR(PSLVERR),
        .PRDATA(PRDATA)
    );

endmodule
