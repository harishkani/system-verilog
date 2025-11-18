/*******************************************************************************
 * Module: spi_master
 *
 * Description:
 *   SPI (Serial Peripheral Interface) Master controller that generates the
 *   SPI clock and controls data transfers with slave devices.
 *
 * Features:
 *   - Configurable data width (8, 16, 32 bits typical)
 *   - Supports all 4 SPI modes (CPOL=0/1, CPHA=0/1)
 *   - Full-duplex communication (simultaneous TX and RX)
 *   - Configurable clock divider for SPI clock generation
 *   - Handshake protocol with tx_valid/tx_ready signals
 *
 * SPI Modes:
 *   Mode 0: CPOL=0, CPHA=0 - Sample on rising edge, change on falling edge
 *   Mode 1: CPOL=0, CPHA=1 - Sample on falling edge, change on rising edge
 *   Mode 2: CPOL=1, CPHA=0 - Sample on falling edge, change on rising edge
 *   Mode 3: CPOL=1, CPHA=1 - Sample on rising edge, change on falling edge
 *
 * Author: Auto-generated
 * Date: 2025
 ******************************************************************************/

module spi_master #(
    parameter DATA_WIDTH = 8,    // Number of bits per transfer (typically 8, 16, or 32)
    parameter CLK_DIV = 4        // System clock divider: SPI_CLK = SYS_CLK / CLK_DIV
) (
    // System signals
    input  logic                    clk,      // System clock (faster than SPI clock)
    input  logic                    rst_n,    // Active-low asynchronous reset

    // Control interface - User side
    input  logic [DATA_WIDTH-1:0]   tx_data,  // Data to transmit to slave
    input  logic                    tx_valid, // Assert high to start transmission
    output logic                    tx_ready, // High when ready to accept new data
    output logic [DATA_WIDTH-1:0]   rx_data,  // Data received from slave
    output logic                    rx_valid, // Pulses high when rx_data is valid

    // SPI interface - Physical pins
    output logic                    sclk,     // SPI clock output to slave
    output logic                    mosi,     // Master Out Slave In - data to slave
    input  logic                    miso,     // Master In Slave Out - data from slave
    output logic                    cs_n,     // Chip Select (active low)

    // Configuration
    input  logic                    cpol,     // Clock Polarity: 0=idle low, 1=idle high
    input  logic                    cpha      // Clock Phase: 0=sample first edge, 1=sample second edge
);

    //==========================================================================
    // State Machine Definition
    //==========================================================================
    typedef enum logic [1:0] {
        IDLE     = 2'b00,  // Waiting for transaction, CS high
        TRANSFER = 2'b01,  // Active transfer, CS low, clock running
        DONE     = 2'b10   // Transfer complete, data ready
    } state_t;

    state_t current_state, next_state;

    //==========================================================================
    // Internal Signals
    //==========================================================================

    // Shift registers for transmit and receive data
    logic [DATA_WIDTH-1:0]          tx_shift_reg;  // Shifts data out MSB first
    logic [DATA_WIDTH-1:0]          rx_shift_reg;  // Shifts data in MSB first

    // Counters
    logic [$clog2(DATA_WIDTH)-1:0]  bit_counter;   // Counts bits transferred (0 to DATA_WIDTH-1)
    logic [$clog2(CLK_DIV)-1:0]     clk_counter;   // Divides system clock for SPI clock

    // Control signals
    logic                           sclk_enable;   // Enable SPI clock generation
    logic                           sclk_int;      // Internal SPI clock before output

    // Edge detection signals
    logic                           sclk_prev;         // Previous SPI clock value
    logic                           sclk_rising_edge;  // Pulse on rising edge of SPI clock
    logic                           sclk_falling_edge; // Pulse on falling edge of SPI clock

    // Sample and change edge determination based on mode
    logic                           sample_edge;   // When to sample MISO
    logic                           change_edge;   // When to change MOSI

    //==========================================================================
    // SPI Clock Generation
    //==========================================================================
    // Creates SPI clock by dividing system clock by CLK_DIV
    // Example: 50MHz system clock / 4 = 12.5MHz SPI clock

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            clk_counter <= '0;
            sclk_int <= cpol;  // Initialize to idle state based on CPOL
        end else begin
            if (sclk_enable) begin  // Only run clock during TRANSFER state
                if (clk_counter == CLK_DIV - 1) begin
                    clk_counter <= '0;
                    sclk_int <= ~sclk_int;  // Toggle SPI clock every CLK_DIV system clocks
                end else begin
                    clk_counter <= clk_counter + 1;
                end
            end else begin
                clk_counter <= '0;
                sclk_int <= cpol;  // Return to idle state when not enabled
            end
        end
    end

    assign sclk = sclk_int;  // Output internal clock to SPI bus

    //==========================================================================
    // Edge Detection for SPI Clock
    //==========================================================================
    // Detects rising and falling edges of the SPI clock
    // Used to determine when to sample MISO and when to change MOSI

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            sclk_prev <= cpol;
        else
            sclk_prev <= sclk_int;
    end

    // Edge detection: compare current vs previous clock value
    assign sclk_rising_edge = !sclk_prev && sclk_int;   // Was low, now high
    assign sclk_falling_edge = sclk_prev && !sclk_int;  // Was high, now low

    //==========================================================================
    // Sample and Change Edge Determination
    //==========================================================================
    // Different SPI modes sample and change data on different edges
    // This logic determines the correct edges based on CPOL and CPHA

    always_comb begin
        if (cpha == 0) begin
            // Mode 0 or Mode 2: Sample on first edge, change on opposite edge
            sample_edge = cpol ? sclk_falling_edge : sclk_rising_edge;
            change_edge = cpol ? sclk_rising_edge : sclk_falling_edge;
        end else begin
            // Mode 1 or Mode 3: Sample on second edge, change on first edge
            sample_edge = cpol ? sclk_rising_edge : sclk_falling_edge;
            change_edge = cpol ? sclk_falling_edge : sclk_rising_edge;
        end
    end

    //==========================================================================
    // State Machine - Sequential Logic
    //==========================================================================

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            current_state <= IDLE;
        else
            current_state <= next_state;
    end

    //==========================================================================
    // State Machine - Combinational Logic
    //==========================================================================
    // Determines next state based on current state and inputs

    always_comb begin
        next_state = current_state;  // Default: stay in current state

        case (current_state)
            IDLE: begin
                // Start transfer when user provides valid data
                if (tx_valid && tx_ready)
                    next_state = TRANSFER;
            end

            TRANSFER: begin
                // Complete transfer after all bits are sampled
                if (bit_counter == DATA_WIDTH - 1 && sample_edge)
                    next_state = DONE;
            end

            DONE: begin
                // Return to idle immediately (data presented for 1 cycle)
                next_state = IDLE;
            end
        endcase
    end

    //==========================================================================
    // Control Signal Generation
    //==========================================================================
    // Generates output control signals based on current state

    always_comb begin
        tx_ready = (current_state == IDLE);      // Ready for new data only in IDLE
        rx_valid = (current_state == DONE);      // Received data valid in DONE state
        sclk_enable = (current_state == TRANSFER); // Clock runs only during TRANSFER
        cs_n = (current_state == IDLE);          // CS active low during TRANSFER and DONE
    end

    //==========================================================================
    // Bit Counter
    //==========================================================================
    // Counts from 0 to DATA_WIDTH-1 to track number of bits transferred

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            bit_counter <= '0;
        end else begin
            case (current_state)
                IDLE:
                    bit_counter <= '0;  // Reset counter in idle

                TRANSFER: begin
                    if (sample_edge)
                        bit_counter <= bit_counter + 1;  // Increment on each sample edge
                end
            endcase
        end
    end

    //==========================================================================
    // Transmit Shift Register and MOSI Output
    //==========================================================================
    // Loads data in IDLE, shifts left on each change edge
    // MSB is always presented on MOSI (MSB-first transmission)

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            tx_shift_reg <= '0;
        end else begin
            case (current_state)
                IDLE: begin
                    if (tx_valid)
                        tx_shift_reg <= tx_data;  // Load new data to transmit
                end

                TRANSFER: begin
                    if (change_edge)
                        // Shift left: next bit moves to MSB position
                        tx_shift_reg <= {tx_shift_reg[DATA_WIDTH-2:0], 1'b0};
                end
            endcase
        end
    end

    assign mosi = tx_shift_reg[DATA_WIDTH-1];  // Always output the MSB

    //==========================================================================
    // Receive Shift Register
    //==========================================================================
    // Samples MISO on each sample edge and shifts into register
    // MSB-first reception (same as transmission)

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_shift_reg <= '0;
        end else begin
            if (current_state == TRANSFER && sample_edge) begin
                // Shift left and insert new bit at LSB
                rx_shift_reg <= {rx_shift_reg[DATA_WIDTH-2:0], miso};
            end
        end
    end

    assign rx_data = rx_shift_reg;  // Output complete received data

endmodule
