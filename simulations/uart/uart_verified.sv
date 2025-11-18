/*******************************************************************************
 * UART Implementation - Verified with iverilog
 *
 * Description:
 *   Complete UART transmitter and receiver with configurable baud rate.
 *   Implements standard UART frame: Start bit + 8 data bits + Stop bit
 *
 * Protocol:
 *   - 1 Start bit (0)
 *   - 8 Data bits (LSB first)
 *   - 1 Stop bit (1)
 *   - No parity
 *
 * Author: Verified Implementation
 * Date: 2025-11-18
 ******************************************************************************/

`timescale 1ns/1ps

//=============================================================================
// UART Transmitter - Sends serial data
//=============================================================================
module uart_tx #(
    parameter CLK_FREQ = 100_000_000,    // System clock frequency (100 MHz)
    parameter BAUD_RATE = 115200         // UART baud rate
) (
    input  wire       clk,        // System clock
    input  wire       rst_n,      // Active-low reset
    input  wire [7:0] tx_data,    // Data to transmit
    input  wire       tx_start,   // Start transmission (pulse high for 1 clock)
    output reg        tx,          // UART TX line
    output reg        tx_busy     // High during transmission
);

    // Calculate clocks per bit
    // For 100MHz clock and 115200 baud: 100_000_000 / 115200 = 868 clocks/bit
    localparam CLKS_PER_BIT = CLK_FREQ / BAUD_RATE;

    // State machine states
    localparam IDLE       = 3'd0;
    localparam START_BIT  = 3'd1;
    localparam DATA_BITS  = 3'd2;
    localparam STOP_BIT   = 3'd3;

    // Internal registers
    reg [2:0]  state;           // Current state
    reg [15:0] clk_count;       // Clock divider counter
    reg [2:0]  bit_index;       // Which data bit we're sending (0-7)
    reg [7:0]  tx_data_reg;     // Registered copy of tx_data

    //==========================================================================
    // Main UART TX State Machine
    //==========================================================================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            tx <= 1'b1;           // UART idles high
            tx_busy <= 1'b0;
            clk_count <= 0;
            bit_index <= 0;
            tx_data_reg <= 0;
        end else begin
            case (state)
                //--------------------------------------------------------------
                // IDLE: Wait for tx_start signal
                //--------------------------------------------------------------
                IDLE: begin
                    tx <= 1'b1;           // Keep TX high (idle)
                    tx_busy <= 1'b0;      // Not busy
                    clk_count <= 0;
                    bit_index <= 0;

                    if (tx_start) begin
                        tx_data_reg <= tx_data;   // Latch input data
                        state <= START_BIT;
                        tx_busy <= 1'b1;          // Now busy
                    end
                end

                //--------------------------------------------------------------
                // START_BIT: Send start bit (0)
                //--------------------------------------------------------------
                START_BIT: begin
                    tx <= 1'b0;           // Start bit is always 0

                    if (clk_count < CLKS_PER_BIT - 1) begin
                        clk_count <= clk_count + 1;
                    end else begin
                        clk_count <= 0;
                        state <= DATA_BITS;
                    end
                end

                //--------------------------------------------------------------
                // DATA_BITS: Send 8 data bits (LSB first)
                //--------------------------------------------------------------
                DATA_BITS: begin
                    tx <= tx_data_reg[bit_index];  // Output current bit

                    if (clk_count < CLKS_PER_BIT - 1) begin
                        clk_count <= clk_count + 1;
                    end else begin
                        clk_count <= 0;

                        if (bit_index < 7) begin
                            bit_index <= bit_index + 1;  // Move to next bit
                        end else begin
                            bit_index <= 0;
                            state <= STOP_BIT;
                        end
                    end
                end

                //--------------------------------------------------------------
                // STOP_BIT: Send stop bit (1)
                //--------------------------------------------------------------
                STOP_BIT: begin
                    tx <= 1'b1;           // Stop bit is always 1

                    if (clk_count < CLKS_PER_BIT - 1) begin
                        clk_count <= clk_count + 1;
                    end else begin
                        clk_count <= 0;
                        state <= IDLE;
                        tx_busy <= 1'b0;
                    end
                end

                default: state <= IDLE;
            endcase
        end
    end

endmodule

//=============================================================================
// UART Receiver - Receives serial data
//=============================================================================
module uart_rx #(
    parameter CLK_FREQ = 100_000_000,    // System clock frequency
    parameter BAUD_RATE = 115200         // UART baud rate
) (
    input  wire       clk,        // System clock
    input  wire       rst_n,      // Active-low reset
    input  wire       rx,          // UART RX line
    output reg  [7:0] rx_data,    // Received data
    output reg        rx_valid    // Pulses high when rx_data is valid
);

    localparam CLKS_PER_BIT = CLK_FREQ / BAUD_RATE;

    // State machine
    localparam IDLE       = 3'd0;
    localparam START_BIT  = 3'd1;
    localparam DATA_BITS  = 3'd2;
    localparam STOP_BIT   = 3'd3;

    // Internal registers
    reg [2:0]  state;
    reg [15:0] clk_count;
    reg [2:0]  bit_index;
    reg [7:0]  rx_data_reg;

    // Synchronize RX input (prevent metastability)
    reg [1:0] rx_sync;
    wire rx_synced;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            rx_sync <= 2'b11;
        else
            rx_sync <= {rx_sync[0], rx};
    end

    assign rx_synced = rx_sync[1];

    //==========================================================================
    // Main UART RX State Machine
    //==========================================================================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            rx_valid <= 1'b0;
            clk_count <= 0;
            bit_index <= 0;
            rx_data_reg <= 0;
            rx_data <= 0;
        end else begin
            rx_valid <= 1'b0;  // Default: valid is a single-cycle pulse

            case (state)
                //--------------------------------------------------------------
                // IDLE: Wait for start bit (falling edge on RX)
                //--------------------------------------------------------------
                IDLE: begin
                    clk_count <= 0;
                    bit_index <= 0;

                    if (rx_synced == 1'b0) begin  // Start bit detected
                        state <= START_BIT;
                    end
                end

                //--------------------------------------------------------------
                // START_BIT: Verify start bit in middle of bit period
                //--------------------------------------------------------------
                START_BIT: begin
                    if (clk_count < (CLKS_PER_BIT - 1) / 2) begin
                        clk_count <= clk_count + 1;
                    end else begin
                        if (rx_synced == 1'b0) begin  // Start bit still low
                            clk_count <= 0;
                            state <= DATA_BITS;
                        end else begin
                            state <= IDLE;  // False start
                        end
                    end
                end

                //--------------------------------------------------------------
                // DATA_BITS: Sample 8 data bits (LSB first)
                //--------------------------------------------------------------
                DATA_BITS: begin
                    if (clk_count < CLKS_PER_BIT - 1) begin
                        clk_count <= clk_count + 1;
                    end else begin
                        clk_count <= 0;

                        // Sample bit in middle of bit period
                        rx_data_reg[bit_index] <= rx_synced;

                        if (bit_index < 7) begin
                            bit_index <= bit_index + 1;
                        end else begin
                            bit_index <= 0;
                            state <= STOP_BIT;
                        end
                    end
                end

                //--------------------------------------------------------------
                // STOP_BIT: Verify stop bit and output data
                //--------------------------------------------------------------
                STOP_BIT: begin
                    if (clk_count < CLKS_PER_BIT - 1) begin
                        clk_count <= clk_count + 1;
                    end else begin
                        clk_count <= 0;

                        if (rx_synced == 1'b1) begin  // Valid stop bit
                            rx_data <= rx_data_reg;
                            rx_valid <= 1'b1;
                        end

                        state <= IDLE;
                    end
                end

                default: state <= IDLE;
            endcase
        end
    end

endmodule

//=============================================================================
// TESTBENCH
//=============================================================================
module uart_tb;

    // Parameters
    localparam CLK_FREQ = 100_000_000;
    localparam BAUD_RATE = 115200;
    localparam CLK_PERIOD = 10;  // 10ns = 100MHz
    localparam BIT_PERIOD = 1_000_000_000 / BAUD_RATE;  // ns per bit

    // Signals
    reg clk;
    reg rst_n;

    // TX signals
    reg [7:0] tx_data;
    reg tx_start;
    wire uart_line;
    wire tx_busy;

    // RX signals
    wire [7:0] rx_data;
    wire rx_valid;

    // DUT instances
    uart_tx #(
        .CLK_FREQ(CLK_FREQ),
        .BAUD_RATE(BAUD_RATE)
    ) tx_inst (
        .clk(clk),
        .rst_n(rst_n),
        .tx_data(tx_data),
        .tx_start(tx_start),
        .tx(uart_line),
        .tx_busy(tx_busy)
    );

    uart_rx #(
        .CLK_FREQ(CLK_FREQ),
        .BAUD_RATE(BAUD_RATE)
    ) rx_inst (
        .clk(clk),
        .rst_n(rst_n),
        .rx(uart_line),
        .rx_data(rx_data),
        .rx_valid(rx_valid)
    );

    // Clock generation
    initial clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    // Test stimulus
    integer errors = 0;
    integer test_num = 0;

    task send_byte(input [7:0] data);
        begin
            @(posedge clk);
            tx_data = data;
            tx_start = 1;
            @(posedge clk);
            tx_start = 0;

            // Wait for transmission to complete
            wait(!tx_busy);
            #(BIT_PERIOD * 2);  // Extra time for RX to finish

            // Check if received correctly
            test_num = test_num + 1;
            if (rx_data == data) begin
                $display("✓ Test %0d PASS: Sent 0x%02h, Received 0x%02h",
                         test_num, data, rx_data);
            end else begin
                $display("✗ Test %0d FAIL: Sent 0x%02h, Received 0x%02h",
                         test_num, data, rx_data);
                errors = errors + 1;
            end
        end
    endtask

    initial begin
        $dumpfile("uart.vcd");
        $dumpvars(0, uart_tb);

        $display("\n========================================");
        $display("  UART TX/RX Testbench");
        $display("  Baud Rate: %0d", BAUD_RATE);
        $display("  Clocks per bit: %0d", CLK_FREQ/BAUD_RATE);
        $display("========================================\n");

        // Initialize
        rst_n = 0;
        tx_start = 0;
        tx_data = 0;

        // Reset
        #(CLK_PERIOD * 5);
        rst_n = 1;
        #(CLK_PERIOD * 5);

        // Test various byte values
        $display("Starting UART tests...\n");

        send_byte(8'hA5);
        send_byte(8'h5A);
        send_byte(8'h00);
        send_byte(8'hFF);
        send_byte(8'h55);
        send_byte(8'hAA);
        send_byte(8'h12);
        send_byte(8'h34);

        // Summary
        #1000;
        $display("\n========================================");
        $display("  Test Summary");
        $display("========================================");
        $display("  Total Tests: %0d", test_num);
        $display("  Passed: %0d", test_num - errors);
        $display("  Failed: %0d", errors);

        if (errors == 0) begin
            $display("\n  ✓✓✓ ALL TESTS PASSED ✓✓✓");
        end else begin
            $display("\n  ✗✗✗ SOME TESTS FAILED ✗✗✗");
        end
        $display("========================================\n");

        $finish;
    end

    // Timeout watchdog
    initial #100_000_000 begin  // 100ms timeout
        $display("\nERROR: Simulation timeout!");
        $finish;
    end

endmodule
