/*******************************************************************************
 * Module: spi_slave
 *
 * Description:
 *   SPI Slave device that responds to SPI master transactions.
 *   Synchronizes all SPI signals to local clock domain for safe operation.
 *
 * Features:
 *   - Configurable data width
 *   - Supports all 4 SPI modes (CPOL/CPHA)
 *   - Full-duplex communication
 *   - 3-stage synchronizers for metastability protection
 *   - Automatic CS detection for transaction boundaries
 *
 * Operation:
 *   1. Waits for CS to go low (transaction start)
 *   2. Loads tx_data into shift register
 *   3. Shifts data in/out on appropriate clock edges
 *   4. Presents received data when CS goes high
 *
 * Author: Auto-generated
 * Date: 2025
 ******************************************************************************/

module spi_slave #(
    parameter DATA_WIDTH = 8    // Number of bits per transfer
) (
    // System signals
    input  logic                    clk,      // Local system clock
    input  logic                    rst_n,    // Active-low asynchronous reset

    // Data interface - User side
    input  logic [DATA_WIDTH-1:0]   tx_data,  // Data to send to master
    input  logic                    tx_valid, // Indicate tx_data is valid
    output logic                    tx_ready, // Ready to accept new tx_data
    output logic [DATA_WIDTH-1:0]   rx_data,  // Data received from master
    output logic                    rx_valid, // Pulses when rx_data is valid

    // SPI interface - Physical pins
    input  logic                    sclk,     // SPI clock from master
    input  logic                    mosi,     // Master Out Slave In
    output logic                    miso,     // Master In Slave Out
    input  logic                    cs_n,     // Chip Select (active low)

    // Configuration
    input  logic                    cpol,     // Clock polarity
    input  logic                    cpha      // Clock phase
);

    //==========================================================================
    // Synchronizer Registers
    //==========================================================================
    // 3-stage synchronizers to safely cross from SPI domain to local clock domain
    // This prevents metastability issues from asynchronous inputs

    logic [2:0] sclk_sync;  // Synchronized SPI clock
    logic [2:0] cs_n_sync;  // Synchronized chip select
    logic [2:0] mosi_sync;  // Synchronized MOSI data

    // Synchronized versions of SPI signals
    logic sclk_int;
    logic cs_n_int;
    logic mosi_int;

    //==========================================================================
    // Signal Synchronization
    //==========================================================================
    // Three flip-flop stages for each asynchronous input
    // Stage 1: May be metastable
    // Stage 2: Metastability should resolve
    // Stage 3: Clean, stable signal ready for use

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sclk_sync <= {3{cpol}};  // Initialize to idle clock state
            cs_n_sync <= 3'b111;     // Initialize to inactive (high)
            mosi_sync <= 3'b000;
        end else begin
            // Shift in new values at each clock
            sclk_sync <= {sclk_sync[1:0], sclk};
            cs_n_sync <= {cs_n_sync[1:0], cs_n};
            mosi_sync <= {mosi_sync[1:0], mosi};
        end
    end

    // Use the final (third) stage as the synchronized signal
    assign sclk_int = sclk_sync[2];
    assign cs_n_int = cs_n_sync[2];
    assign mosi_int = mosi_sync[2];

    //==========================================================================
    // Edge Detection for SCLK
    //==========================================================================

    logic sclk_prev;
    logic sclk_rising_edge;
    logic sclk_falling_edge;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            sclk_prev <= cpol;
        else
            sclk_prev <= sclk_int;
    end

    assign sclk_rising_edge = !sclk_prev && sclk_int;
    assign sclk_falling_edge = sclk_prev && !sclk_int;

    //==========================================================================
    // Edge Detection for CS (Chip Select)
    //==========================================================================
    // Falling edge: Transaction starts
    // Rising edge: Transaction ends

    logic cs_n_prev;
    logic cs_n_falling_edge;  // Start of transaction
    logic cs_n_rising_edge;   // End of transaction

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            cs_n_prev <= 1'b1;
        else
            cs_n_prev <= cs_n_int;
    end

    assign cs_n_falling_edge = cs_n_prev && !cs_n_int;
    assign cs_n_rising_edge = !cs_n_prev && cs_n_int;

    //==========================================================================
    // Sample and Change Edge Determination
    //==========================================================================

    logic sample_edge;
    logic change_edge;

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
    // Internal Registers
    //==========================================================================

    logic [DATA_WIDTH-1:0] tx_shift_reg;  // Data to transmit to master
    logic [DATA_WIDTH-1:0] rx_shift_reg;  // Data received from master
    logic [$clog2(DATA_WIDTH)-1:0] bit_counter;

    //==========================================================================
    // Bit Counter
    //==========================================================================
    // Counts bits transferred within a transaction

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            bit_counter <= '0;
        end else begin
            if (cs_n_int) begin
                bit_counter <= '0;  // Reset when CS is inactive
            end else if (sample_edge) begin
                bit_counter <= bit_counter + 1;  // Count each sampled bit
            end
        end
    end

    //==========================================================================
    // Transmit Shift Register
    //==========================================================================
    // Loads data when CS falls, shifts out MSB first

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            tx_shift_reg <= '0;
        end else begin
            if (cs_n_falling_edge && tx_valid) begin
                // Load new data at start of transaction
                tx_shift_reg <= tx_data;
            end else if (!cs_n_int && change_edge) begin
                // Shift left during active transaction
                tx_shift_reg <= {tx_shift_reg[DATA_WIDTH-2:0], 1'b0};
            end
        end
    end

    // MISO output: high-Z when CS inactive, MSB of shift register when active
    assign miso = cs_n_int ? 1'bz : tx_shift_reg[DATA_WIDTH-1];

    //==========================================================================
    // Receive Shift Register
    //==========================================================================
    // Samples MOSI on each sample edge during active transaction

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_shift_reg <= '0;
        end else begin
            if (!cs_n_int && sample_edge) begin
                // Shift in new bit from MOSI
                rx_shift_reg <= {rx_shift_reg[DATA_WIDTH-2:0], mosi_int};
            end
        end
    end

    assign rx_data = rx_shift_reg;

    //==========================================================================
    // Valid Signal Generation
    //==========================================================================
    // Assert rx_valid for one cycle when complete transaction finishes

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            rx_valid <= 1'b0;
        else
            // Valid when CS rises and we've received all bits
            rx_valid <= cs_n_rising_edge && (bit_counter == DATA_WIDTH);
    end

    // Ready to accept new tx_data when CS is inactive
    assign tx_ready = cs_n_int;

endmodule
