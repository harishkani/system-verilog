// APB Slave - Simple memory-mapped slave
module apb_slave #(
    parameter ADDR_WIDTH = 16,
    parameter DATA_WIDTH = 32,
    parameter MEM_DEPTH = 256
) (
    input wire                      clk,
    input wire                      rst_n,

    // APB interface
    input wire [ADDR_WIDTH-1:0]     PADDR,
    input wire                      PSEL,
    input wire                      PENABLE,
    input wire                      PWRITE,
    input wire [DATA_WIDTH-1:0]     PWDATA,
    output reg [DATA_WIDTH-1:0]     PRDATA,
    output reg                      PREADY,
    output reg                      PSLVERR
);

    // Internal memory
    reg [DATA_WIDTH-1:0] mem [0:MEM_DEPTH-1];

    // Memory address
    wire [7:0] mem_addr;
    assign mem_addr = PADDR[9:2];  // Word-aligned access

    integer i;

    // APB protocol implementation
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PRDATA  <= {DATA_WIDTH{1'b0}};
            PREADY  <= 1'b0;
            PSLVERR <= 1'b0;

            // Initialize memory
            for (i = 0; i < MEM_DEPTH; i = i + 1) begin
                mem[i] <= {DATA_WIDTH{1'b0}};
            end
        end else begin
            PREADY  <= 1'b0;
            PSLVERR <= 1'b0;

            // APB transaction
            if (PSEL && PENABLE) begin
                if (mem_addr < MEM_DEPTH) begin
                    if (PWRITE) begin
                        // Write transaction
                        mem[mem_addr] <= PWDATA;
                    end else begin
                        // Read transaction
                        PRDATA <= mem[mem_addr];
                    end
                    PREADY <= 1'b1;
                end else begin
                    // Address out of range
                    PSLVERR <= 1'b1;
                    PREADY  <= 1'b1;
                end
            end
        end
    end

endmodule
