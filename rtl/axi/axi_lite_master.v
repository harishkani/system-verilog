// AXI Lite Master
// Simplified AXI protocol with single outstanding transactions
module axi_lite_master #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
) (
    input wire                      clk,
    input wire                      rst_n,

    // Control interface
    input wire                      req,
    input wire                      wr,
    input wire [ADDR_WIDTH-1:0]     addr,
    input wire [DATA_WIDTH-1:0]     wdata,
    input wire [3:0]                wstrb,  // Byte strobes
    output reg [DATA_WIDTH-1:0]     rdata,
    output reg                      ready,
    output reg                      resp_ok,

    // AXI Lite Write Address Channel
    output reg [ADDR_WIDTH-1:0]     AWADDR,
    output reg                      AWVALID,
    input wire                      AWREADY,

    // AXI Lite Write Data Channel
    output reg [DATA_WIDTH-1:0]     WDATA,
    output reg [3:0]                WSTRB,
    output reg                      WVALID,
    input wire                      WREADY,

    // AXI Lite Write Response Channel
    input wire [1:0]                BRESP,
    input wire                      BVALID,
    output reg                      BREADY,

    // AXI Lite Read Address Channel
    output reg [ADDR_WIDTH-1:0]     ARADDR,
    output reg                      ARVALID,
    input wire                      ARREADY,

    // AXI Lite Read Data Channel
    input wire [DATA_WIDTH-1:0]     RDATA,
    input wire [1:0]                RRESP,
    input wire                      RVALID,
    output reg                      RREADY
);

    // State machine
    localparam IDLE        = 3'd0;
    localparam WRITE_ADDR  = 3'd1;
    localparam WRITE_DATA  = 3'd2;
    localparam WRITE_RESP  = 3'd3;
    localparam READ_ADDR   = 3'd4;
    localparam READ_DATA   = 3'd5;
    localparam DONE        = 3'd6;

    reg [2:0] state, next_state;

    // State machine
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next_state;
    end

    // Next state logic
    always @(*) begin
        next_state = state;
        case (state)
            IDLE: begin
                if (req) begin
                    if (wr)
                        next_state = WRITE_ADDR;
                    else
                        next_state = READ_ADDR;
                end
            end

            WRITE_ADDR: begin
                if (AWVALID && AWREADY)
                    next_state = WRITE_DATA;
            end

            WRITE_DATA: begin
                if (WVALID && WREADY)
                    next_state = WRITE_RESP;
            end

            WRITE_RESP: begin
                if (BVALID && BREADY)
                    next_state = DONE;
            end

            READ_ADDR: begin
                if (ARVALID && ARREADY)
                    next_state = READ_DATA;
            end

            READ_DATA: begin
                if (RVALID && RREADY)
                    next_state = DONE;
            end

            DONE: begin
                next_state = IDLE;
            end

            default: next_state = IDLE;
        endcase
    end

    // Output logic
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            AWADDR  <= 0;
            AWVALID <= 0;
            WDATA   <= 0;
            WSTRB   <= 0;
            WVALID  <= 0;
            BREADY  <= 0;
            ARADDR  <= 0;
            ARVALID <= 0;
            RREADY  <= 0;
            rdata   <= 0;
            ready   <= 0;
            resp_ok <= 0;
        end else begin
            ready <= 0;  // Default

            case (state)
                IDLE: begin
                    AWVALID <= 0;
                    WVALID  <= 0;
                    BREADY  <= 0;
                    ARVALID <= 0;
                    RREADY  <= 0;

                    if (req) begin
                        AWADDR <= addr;
                        ARADDR <= addr;
                        WDATA  <= wdata;
                        WSTRB  <= wstrb;
                    end
                end

                WRITE_ADDR: begin
                    AWVALID <= 1;
                end

                WRITE_DATA: begin
                    WVALID <= 1;
                end

                WRITE_RESP: begin
                    AWVALID <= 0;  // Deassert address valid
                    WVALID  <= 0;  // Deassert data valid
                    BREADY  <= 1;  // Ready to receive response
                    if (BVALID) begin
                        resp_ok <= (BRESP == 2'b00);  // OKAY response
                    end
                end

                READ_ADDR: begin
                    ARVALID <= 1;
                end

                READ_DATA: begin
                    ARVALID <= 0;  // Deassert address valid
                    RREADY  <= 1;  // Ready to receive data
                    if (RVALID) begin
                        rdata   <= RDATA;
                        resp_ok <= (RRESP == 2'b00);  // OKAY response
                    end
                end

                DONE: begin
                    // Deassert all signals
                    AWVALID <= 0;
                    WVALID  <= 0;
                    BREADY  <= 0;
                    ARVALID <= 0;
                    RREADY  <= 0;
                    ready   <= 1;
                end
            endcase
        end
    end

endmodule
