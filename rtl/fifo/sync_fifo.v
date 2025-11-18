// Synchronous FIFO - Verified Implementation
module sync_fifo #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 16
) (
    input wire                  clk,
    input wire                  rst_n,
    // Write interface
    input wire [DATA_WIDTH-1:0] wr_data,
    input wire                  wr_en,
    output wire                 full,
    output wire                 almost_full,
    // Read interface
    output reg [DATA_WIDTH-1:0] rd_data,
    input wire                  rd_en,
    output wire                 empty,
    output wire                 almost_empty,
    // Status
    output reg [4:0]            count
);

    // Memory array
    reg [DATA_WIDTH-1:0] mem [0:DEPTH-1];

    // Pointers
    reg [4:0] wr_ptr;
    reg [4:0] rd_ptr;

    // Status flags
    assign full = (count == DEPTH);
    assign empty = (count == 0);
    assign almost_full = (count >= DEPTH - 2);
    assign almost_empty = (count <= 2);

    // Write operation
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_ptr <= 5'b0;
        end else begin
            if (wr_en && !full) begin
                mem[wr_ptr[3:0]] <= wr_data;
                wr_ptr <= wr_ptr + 1;
            end
        end
    end

    // Read operation
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_ptr <= 5'b0;
            rd_data <= 8'b0;
        end else begin
            if (rd_en && !empty) begin
                rd_data <= mem[rd_ptr[3:0]];
                rd_ptr <= rd_ptr + 1;
            end
        end
    end

    // Count calculation
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            count <= 5'b0;
        end else begin
            case ({wr_en && !full, rd_en && !empty})
                2'b10: count <= count + 1;
                2'b01: count <= count - 1;
                default: count <= count;
            endcase
        end
    end

endmodule
