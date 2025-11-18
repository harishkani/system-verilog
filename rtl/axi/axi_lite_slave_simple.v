// AXI Lite Slave - Simplified version with immediate ready
module axi_lite_slave_simple #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32,
    parameter MEM_DEPTH = 256
) (
    input wire                      clk,
    input wire                      rst_n,

    // AXI Lite Write Address Channel
    input wire [ADDR_WIDTH-1:0]     AWADDR,
    input wire                      AWVALID,
    output wire                     AWREADY,

    // AXI Lite Write Data Channel
    input wire [DATA_WIDTH-1:0]     WDATA,
    input wire [3:0]                WSTRB,
    input wire                      WVALID,
    output wire                     WREADY,

    // AXI Lite Write Response Channel
    output reg [1:0]                BRESP,
    output reg                      BVALID,
    input wire                      BREADY,

    // AXI Lite Read Address Channel
    input wire [ADDR_WIDTH-1:0]     ARADDR,
    input wire                      ARVALID,
    output wire                     ARREADY,

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

    integer i;

    // Always ready for address
    assign AWREADY = 1'b1;
    assign WREADY = 1'b1;
    assign ARREADY = 1'b1;

    // Write transaction
    reg [ADDR_WIDTH-1:0] wr_addr_reg;
    reg wr_addr_valid;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_addr_reg <= 0;
            wr_addr_valid <= 0;
            for (i = 0; i < MEM_DEPTH; i = i + 1)
                mem[i] <= 0;
        end else begin
            // Capture write address
            if (AWVALID && AWREADY) begin
                wr_addr_reg <= AWADDR;
                wr_addr_valid <= 1'b1;
            end

            // Perform write
            if (WVALID && WREADY && wr_addr_valid) begin
                if (wr_addr_reg[9:2] < MEM_DEPTH) begin
                    if (WSTRB[0]) mem[wr_addr_reg[9:2]][7:0]   <= WDATA[7:0];
                    if (WSTRB[1]) mem[wr_addr_reg[9:2]][15:8]  <= WDATA[15:8];
                    if (WSTRB[2]) mem[wr_addr_reg[9:2]][23:16] <= WDATA[23:16];
                    if (WSTRB[3]) mem[wr_addr_reg[9:2]][31:24] <= WDATA[31:24];
                end
                wr_addr_valid <= 1'b0;
            end
        end
    end

    // Write response
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            BVALID <= 0;
            BRESP  <= OKAY;
        end else begin
            if (WVALID && WREADY && !BVALID) begin
                BVALID <= 1;
                BRESP <= (wr_addr_reg[9:2] < MEM_DEPTH) ? OKAY : SLVERR;
            end else if (BVALID && BREADY) begin
                BVALID <= 0;
            end
        end
    end

    // Read transaction
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            RVALID <= 0;
            RDATA  <= 0;
            RRESP  <= OKAY;
        end else begin
            if (ARVALID && ARREADY && !RVALID) begin
                RVALID <= 1;
                if (ARADDR[9:2] < MEM_DEPTH) begin
                    RDATA <= mem[ARADDR[9:2]];
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
