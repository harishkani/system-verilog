// AXI Lite Slave
// Simple memory-mapped slave with AXI Lite interface
module axi_lite_slave #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32,
    parameter MEM_DEPTH = 256
) (
    input wire                      clk,
    input wire                      rst_n,

    // AXI Lite Write Address Channel
    input wire [ADDR_WIDTH-1:0]     AWADDR,
    input wire                      AWVALID,
    output reg                      AWREADY,

    // AXI Lite Write Data Channel
    input wire [DATA_WIDTH-1:0]     WDATA,
    input wire [3:0]                WSTRB,
    input wire                      WVALID,
    output reg                      WREADY,

    // AXI Lite Write Response Channel
    output reg [1:0]                BRESP,
    output reg                      BVALID,
    input wire                      BREADY,

    // AXI Lite Read Address Channel
    input wire [ADDR_WIDTH-1:0]     ARADDR,
    input wire                      ARVALID,
    output reg                      ARREADY,

    // AXI Lite Read Data Channel
    output reg [DATA_WIDTH-1:0]     RDATA,
    output reg [1:0]                RRESP,
    output reg                      RVALID,
    input wire                      RREADY
);

    // Response types
    localparam OKAY   = 2'b00;
    localparam SLVERR = 2'b10;

    // Memory
    reg [DATA_WIDTH-1:0] mem [0:MEM_DEPTH-1];

    // Address latches
    reg [ADDR_WIDTH-1:0] wr_addr;
    reg [ADDR_WIDTH-1:0] rd_addr;

    wire [7:0] wr_mem_addr = wr_addr[9:2];  // Word-aligned
    wire [7:0] rd_mem_addr = rd_addr[9:2];

    integer i;

    // Write address channel
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            AWREADY <= 0;
            wr_addr <= 0;
        end else begin
            if (AWVALID && !AWREADY) begin
                AWREADY <= 1;
                wr_addr <= AWADDR;
            end else begin
                AWREADY <= 0;
            end
        end
    end

    // Write data channel
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            WREADY <= 0;
            for (i = 0; i < MEM_DEPTH; i = i + 1)
                mem[i] <= 0;
        end else begin
            if (WVALID && !WREADY) begin
                WREADY <= 1;
                if (wr_mem_addr < MEM_DEPTH) begin
                    // Write with byte strobes
                    if (WSTRB[0]) mem[wr_mem_addr][7:0]   <= WDATA[7:0];
                    if (WSTRB[1]) mem[wr_mem_addr][15:8]  <= WDATA[15:8];
                    if (WSTRB[2]) mem[wr_mem_addr][23:16] <= WDATA[23:16];
                    if (WSTRB[3]) mem[wr_mem_addr][31:24] <= WDATA[31:24];
                end
            end else begin
                WREADY <= 0;
            end
        end
    end

    // Write response channel
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            BVALID <= 0;
            BRESP  <= OKAY;
        end else begin
            if (WVALID && WREADY && !BVALID) begin
                BVALID <= 1;
                if (wr_mem_addr < MEM_DEPTH)
                    BRESP <= OKAY;
                else
                    BRESP <= SLVERR;
            end else if (BVALID && BREADY) begin
                BVALID <= 0;
            end
        end
    end

    // Read address channel
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ARREADY <= 0;
            rd_addr <= 0;
        end else begin
            if (ARVALID && !ARREADY) begin
                ARREADY <= 1;
                rd_addr <= ARADDR;
            end else begin
                ARREADY <= 0;
            end
        end
    end

    // Read data channel
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            RVALID <= 0;
            RDATA  <= 0;
            RRESP  <= OKAY;
        end else begin
            if (ARVALID && ARREADY && !RVALID) begin
                RVALID <= 1;
                if (rd_mem_addr < MEM_DEPTH) begin
                    RDATA <= mem[rd_mem_addr];
                    RRESP <= OKAY;
                end else begin
                    RDATA <= 32'hDEADDEAD;
                    RRESP <= SLVERR;
                end
            end else if (RVALID && RREADY) begin
                RVALID <= 0;
            end
        end
    end

endmodule
