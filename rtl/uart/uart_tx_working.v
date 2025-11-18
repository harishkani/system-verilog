// UART Transmitter - Verified Working Implementation
// Simplified with clear timing - All tests passed
// Test results: 0xAA, 0x55, 0xFF, 0x00 transmitted correctly

module uart_tx_working #(
    parameter CLKS_PER_BIT = 100  // System clock cycles per UART bit
) (
    input wire clk,
    input wire rst_n,
    input wire [7:0] data_in,
    input wire start,
    output reg tx,
    output reg busy
);

    localparam IDLE  = 0;
    localparam START = 1;
    localparam DATA  = 2;
    localparam STOP  = 3;

    reg [1:0] state;
    reg [15:0] clk_count;
    reg [2:0] bit_idx;
    reg [7:0] data_reg;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            tx <= 1'b1;
            busy <= 1'b0;
            clk_count <= 0;
            bit_idx <= 0;
            data_reg <= 0;
        end else begin
            case (state)
                IDLE: begin
                    tx <= 1'b1;
                    busy <= 1'b0;
                    clk_count <= 0;
                    bit_idx <= 0;
                    if (start) begin
                        data_reg <= data_in;
                        state <= START;
                        busy <= 1'b1;
                    end
                end

                START: begin
                    tx <= 1'b0;  // Start bit
                    if (clk_count < CLKS_PER_BIT - 1) begin
                        clk_count <= clk_count + 1;
                    end else begin
                        clk_count <= 0;
                        state <= DATA;
                    end
                end

                DATA: begin
                    tx <= data_reg[bit_idx];  // Send LSB first
                    if (clk_count < CLKS_PER_BIT - 1) begin
                        clk_count <= clk_count + 1;
                    end else begin
                        clk_count <= 0;
                        if (bit_idx == 7) begin
                            state <= STOP;
                            bit_idx <= 0;
                        end else begin
                            bit_idx <= bit_idx + 1;
                        end
                    end
                end

                STOP: begin
                    tx <= 1'b1;  // Stop bit
                    if (clk_count < CLKS_PER_BIT - 1) begin
                        clk_count <= clk_count + 1;
                    end else begin
                        clk_count <= 0;
                        state <= IDLE;
                    end
                end
            endcase
        end
    end
endmodule
