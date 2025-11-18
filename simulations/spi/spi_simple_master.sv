/*******************************************************************************
 * Module: spi_simple_master
 *
 * Description:
 *   Simplified SPI Master optimized for simulation clarity and correctness
 *   Uses simpler state machine and direct SPI signal generation
 *
 * This version prioritizes simulation correctness over all design features
 ******************************************************************************/

module spi_simple_master #(
    parameter DATA_WIDTH = 8,
    parameter CLK_DIV = 4
) (
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic [DATA_WIDTH-1:0]   tx_data,
    input  logic                    tx_valid,
    output logic                    tx_ready,
    output logic [DATA_WIDTH-1:0]   rx_data,
    output logic                    rx_valid,
    output logic                    sclk,
    output logic                    mosi,
    input  logic                    miso,
    output logic                    cs_n,
    input  logic                    cpol,
    input  logic                    cpha
);

    // State machine
    typedef enum logic [1:0] {
        IDLE,
        SETUP,
        TRANSFER,
        DONE
    } state_t;

    state_t state;

    // Counters
    logic [$clog2(CLK_DIV*2)-1:0] clk_cnt;     // For SPI clock generation
    logic [$clog2(DATA_WIDTH)-1:0] bit_cnt;     // Bit counter
    logic sclk_reg;
    logic [DATA_WIDTH-1:0] tx_reg, rx_reg;

    // SPI clock generation - toggle every CLK_DIV/2 clocks
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            clk_cnt <= '0;
            sclk_reg <= cpol;
        end else if (state == TRANSFER) begin
            if (clk_cnt == (CLK_DIV/2 - 1)) begin
                clk_cnt <= '0;
                sclk_reg <= ~sclk_reg;
            end else begin
                clk_cnt <= clk_cnt + 1;
            end
        end else begin
            clk_cnt <= '0;
            sclk_reg <= cpol;
        end
    end

    assign sclk = sclk_reg;

    // Detect SPI clock edges
    logic sclk_prev;
    logic sclk_edge;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            sclk_prev <= cpol;
        else
            sclk_prev <= sclk_reg;
    end

    assign sclk_edge = (sclk_prev != sclk_reg);  // Any edge

    logic sample_now, change_now;

    // Determine when to sample and change based on mode
    always_comb begin
        if (cpha == 1'b0) begin
            // Mode 0/2: Change on one edge, sample on other
            if (cpol == 1'b0) begin
                sample_now = sclk_edge && sclk_reg;   // Sample on rising
                change_now = sclk_edge && !sclk_reg;  // Change on falling
            end else begin
                sample_now = sclk_edge && !sclk_reg;  // Sample on falling
                change_now = sclk_edge && sclk_reg;   // Change on rising
            end
        end else begin
            // Mode 1/3: Opposite
            if (cpol == 1'b0) begin
                sample_now = sclk_edge && !sclk_reg;  // Sample on falling
                change_now = sclk_edge && sclk_reg;   // Change on rising
            end else begin
                sample_now = sclk_edge && sclk_reg;   // Sample on rising
                change_now = sclk_edge && !sclk_reg;  // Change on falling
            end
        end
    end

    // Main state machine
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            bit_cnt <= '0;
            tx_reg <= '0;
            rx_reg <= '0;
            rx_valid <= 1'b0;
        end else begin
            rx_valid <= 1'b0;  // Default

            case (state)
                IDLE: begin
                    bit_cnt <= '0;
                    if (tx_valid) begin
                        tx_reg <= tx_data;
                        state <= SETUP;
                    end
                end

                SETUP: begin
                    // One clock for setup
                    state <= TRANSFER;
                end

                TRANSFER: begin
                    // Sample MISO on sample edge
                    if (sample_now) begin
                        rx_reg <= {rx_reg[DATA_WIDTH-2:0], miso};
                        bit_cnt <= bit_cnt + 1;
                    end

                    // Shift TX on change edge (before first sample in CPHA=0)
                    if (change_now && (cpha == 1'b0 || bit_cnt > 0)) begin
                        tx_reg <= {tx_reg[DATA_WIDTH-2:0], 1'b0};
                    end

                    // Done after sampling all bits
                    if (bit_cnt == DATA_WIDTH && sample_now) begin
                        state <= DONE;
                    end
                end

                DONE: begin
                    rx_data <= rx_reg;
                    rx_valid <= 1'b1;
                    state <= IDLE;
                end
            endcase
        end
    end

    // Outputs
    assign mosi = tx_reg[DATA_WIDTH-1];
    assign cs_n = (state == IDLE);
    assign tx_ready = (state == IDLE);

endmodule
