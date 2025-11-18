// APB Master - AMBA Advanced Peripheral Bus
// Simple protocol for low-power peripheral access
module apb_master #(
    parameter ADDR_WIDTH = 16,
    parameter DATA_WIDTH = 32
) (
    input wire                      clk,
    input wire                      rst_n,

    // Control interface
    input wire                      req,        // Request transaction
    input wire                      wr,         // 1=Write, 0=Read
    input wire [ADDR_WIDTH-1:0]     addr,       // Address
    input wire [DATA_WIDTH-1:0]     wdata,      // Write data
    output reg [DATA_WIDTH-1:0]     rdata,      // Read data
    output reg                      ready,      // Transaction complete

    // APB interface
    output reg [ADDR_WIDTH-1:0]     PADDR,      // APB Address
    output reg                      PSEL,       // APB Select
    output reg                      PENABLE,    // APB Enable
    output reg                      PWRITE,     // APB Write
    output reg [DATA_WIDTH-1:0]     PWDATA,     // APB Write Data
    input wire [DATA_WIDTH-1:0]     PRDATA,     // APB Read Data
    input wire                      PREADY,     // APB Ready
    input wire                      PSLVERR     // APB Slave Error
);

    // APB State Machine
    localparam IDLE   = 2'd0;
    localparam SETUP  = 2'd1;
    localparam ACCESS = 2'd2;

    reg [1:0] state, next_state;

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
                if (req)
                    next_state = SETUP;
            end
            SETUP: begin
                next_state = ACCESS;
            end
            ACCESS: begin
                if (PREADY)
                    next_state = IDLE;
            end
            default: next_state = IDLE;
        endcase
    end

    // APB signals
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PADDR   <= {ADDR_WIDTH{1'b0}};
            PSEL    <= 1'b0;
            PENABLE <= 1'b0;
            PWRITE  <= 1'b0;
            PWDATA  <= {DATA_WIDTH{1'b0}};
            rdata   <= {DATA_WIDTH{1'b0}};
            ready   <= 1'b0;
        end else begin
            case (state)
                IDLE: begin
                    PSEL    <= 1'b0;
                    PENABLE <= 1'b0;
                    ready   <= 1'b0;

                    if (req) begin
                        PADDR  <= addr;
                        PWRITE <= wr;
                        PWDATA <= wdata;
                    end
                end

                SETUP: begin
                    PSEL    <= 1'b1;
                    PENABLE <= 1'b0;
                    ready   <= 1'b0;
                end

                ACCESS: begin
                    PSEL    <= 1'b1;
                    PENABLE <= 1'b1;

                    if (PREADY) begin
                        if (!PWRITE)
                            rdata <= PRDATA;
                        ready <= 1'b1;
                    end
                end

                default: begin
                    PSEL    <= 1'b0;
                    PENABLE <= 1'b0;
                    ready   <= 1'b0;
                end
            endcase
        end
    end

endmodule
