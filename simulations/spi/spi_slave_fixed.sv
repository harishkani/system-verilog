/*******************************************************************************
 * Module: spi_slave (Fixed for simulation)
 *
 * Description:
 *   SPI Slave device - simplified version that works reliably in simulation
 *   Removed complex synchronizers for cleaner simulation behavior
 *
 * Note: For production use, add proper synchronizers for metastability protection
 ******************************************************************************/

module spi_slave #(
    parameter DATA_WIDTH = 8
) (
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic [DATA_WIDTH-1:0]   tx_data,
    input  logic                    tx_valid,
    output logic                    tx_ready,
    output logic [DATA_WIDTH-1:0]   rx_data,
    output logic                    rx_valid,
    input  logic                    sclk,
    input  logic                    mosi,
    output logic                    miso,
    input  logic                    cs_n,
    input  logic                    cpol,
    input  logic                    cpha
);

    //==========================================================================
    // Simplified synchronization (2-stage for simulation)
    //==========================================================================
    logic [1:0] sclk_sync;
    logic [1:0] cs_n_sync;
    logic [1:0] mosi_sync;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sclk_sync <= {2{cpol}};
            cs_n_sync <= 2'b11;
            mosi_sync <= 2'b00;
        end else begin
            sclk_sync <= {sclk_sync[0], sclk};
            cs_n_sync <= {cs_n_sync[0], cs_n};
            mosi_sync <= {mosi_sync[0], mosi};
        end
    end

    logic sclk_int, cs_n_int, mosi_int;
    assign sclk_int = sclk_sync[1];
    assign cs_n_int = cs_n_sync[1];
    assign mosi_int = mosi_sync[1];

    //==========================================================================
    // Edge Detection
    //==========================================================================
    logic sclk_prev, cs_n_prev;
    logic sclk_rising_edge, sclk_falling_edge;
    logic cs_n_falling_edge, cs_n_rising_edge;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sclk_prev <= cpol;
            cs_n_prev <= 1'b1;
        end else begin
            sclk_prev <= sclk_int;
            cs_n_prev <= cs_n_int;
        end
    end

    assign sclk_rising_edge = !sclk_prev && sclk_int;
    assign sclk_falling_edge = sclk_prev && !sclk_int;
    assign cs_n_falling_edge = cs_n_prev && !cs_n_int;
    assign cs_n_rising_edge = !cs_n_prev && cs_n_int;

    //==========================================================================
    // Sample/Change Edge Logic
    //==========================================================================
    logic sample_edge, change_edge;

    always_comb begin
        if (cpha == 0) begin
            sample_edge = cpol ? sclk_falling_edge : sclk_rising_edge;
            change_edge = cpol ? sclk_rising_edge : sclk_falling_edge;
        end else begin
            sample_edge = cpol ? sclk_rising_edge : sclk_falling_edge;
            change_edge = cpol ? sclk_falling_edge : sclk_rising_edge;
        end
    end

    //==========================================================================
    // Data Registers
    //==========================================================================
    logic [DATA_WIDTH-1:0] tx_shift_reg;
    logic [DATA_WIDTH-1:0] rx_shift_reg;
    logic [$clog2(DATA_WIDTH)-1:0] bit_counter;
    logic miso_reg;

    //==========================================================================
    // Bit Counter
    //==========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            bit_counter <= '0;
        end else begin
            if (cs_n_int || cs_n_rising_edge) begin
                bit_counter <= '0;
            end else if (sample_edge) begin
                bit_counter <= bit_counter + 1;
            end
        end
    end

    //==========================================================================
    // TX Shift Register - Load on CS falling, shift on change edge
    //==========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            tx_shift_reg <= '0;
            miso_reg <= 1'b0;
        end else begin
            if (cs_n_falling_edge && tx_valid) begin
                // Load data when transaction starts
                tx_shift_reg <= tx_data;
                miso_reg <= tx_data[DATA_WIDTH-1];  // Pre-load first bit
            end else if (!cs_n_int && change_edge) begin
                // Shift on change edge
                tx_shift_reg <= {tx_shift_reg[DATA_WIDTH-2:0], 1'b0};
                miso_reg <= tx_shift_reg[DATA_WIDTH-2];  // Next bit
            end else if (cs_n_int) begin
                miso_reg <= 1'b0;
            end
        end
    end

    // Output MISO with proper tri-state
    assign miso = cs_n ? 1'bz : miso_reg;

    //==========================================================================
    // RX Shift Register - Sample on sample edge
    //==========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_shift_reg <= '0;
        end else begin
            if (!cs_n_int && sample_edge) begin
                rx_shift_reg <= {rx_shift_reg[DATA_WIDTH-2:0], mosi_int};
            end
        end
    end

    assign rx_data = rx_shift_reg;

    //==========================================================================
    // Output Signals
    //==========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_valid <= 1'b0;
        end else begin
            // Pulse rx_valid when CS rises and all bits received
            rx_valid <= cs_n_rising_edge && (bit_counter == DATA_WIDTH);
        end
    end

    assign tx_ready = cs_n;

endmodule
