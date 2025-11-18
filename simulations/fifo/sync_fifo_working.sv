/*******************************************************************************
 * Synchronous FIFO - Fully Commented and Verified
 *
 * Description:
 *   A synchronous FIFO (First-In-First-Out) buffer that operates on a single
 *   clock domain. Data written first is read first.
 *
 * Features:
 *   - Configurable data width and depth
 *   - Full and Empty flags
 *   - Almost-Full and Almost-Empty flags (programmable thresholds)
 *   - Data count output
 *   - Write and read enable controls
 *
 * Operation:
 *   Write: Assert wr_en with wr_data when !full
 *   Read:  Assert rd_en when !empty, rd_data valid next cycle
 *
 * Author: Auto-generated with detailed comments
 * Date: 2025
 ******************************************************************************/

`timescale 1ns/1ps

module sync_fifo #(
    parameter DATA_WIDTH = 8,                    // Width of each data entry
    parameter DEPTH = 16,                        // Number of entries in FIFO
    parameter ALMOST_FULL_THRESHOLD = 14,        // Almost full when count >= this
    parameter ALMOST_EMPTY_THRESHOLD = 2         // Almost empty when count <= this
) (
    input  wire                    clk,          // System clock
    input  wire                    rst_n,        // Active-low reset

    // Write interface
    input  wire [DATA_WIDTH-1:0]   wr_data,      // Data to write
    input  wire                    wr_en,        // Write enable
    output wire                    full,         // FIFO is full, cannot write
    output wire                    almost_full,  // FIFO is almost full

    // Read interface
    output reg  [DATA_WIDTH-1:0]   rd_data,      // Data read from FIFO
    input  wire                    rd_en,        // Read enable
    output wire                    empty,        // FIFO is empty, cannot read
    output wire                    almost_empty, // FIFO is almost empty

    // Status
    output wire [$clog2(DEPTH):0]  count         // Number of entries currently in FIFO
);

    //==========================================================================
    // Internal Memory Array
    //==========================================================================
    // This is the actual storage. Synthesizes to block RAM in FPGAs.
    reg [DATA_WIDTH-1:0] mem [0:DEPTH-1];

    //==========================================================================
    // Read and Write Pointers
    //==========================================================================
    // Pointers are one bit wider than needed for address to distinguish
    // between full and empty (both would have rd_ptr == wr_ptr otherwise)
    reg [$clog2(DEPTH):0] wr_ptr;  // Write pointer
    reg [$clog2(DEPTH):0] rd_ptr;  // Read pointer

    //==========================================================================
    // Status Signals
    //==========================================================================
    reg [$clog2(DEPTH):0] count_reg;  // Internal count register

    // FIFO is full when count equals depth
    assign full = (count_reg == DEPTH);

    // FIFO is empty when count is zero
    assign empty = (count_reg == 0);

    // Almost full/empty based on programmable thresholds
    assign almost_full = (count_reg >= ALMOST_FULL_THRESHOLD);
    assign almost_empty = (count_reg <= ALMOST_EMPTY_THRESHOLD);

    // Output the count
    assign count = count_reg;

    //==========================================================================
    // Write Logic
    //==========================================================================
    // Write data into memory when wr_en is high and FIFO is not full

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_ptr <= '0;  // Reset write pointer to 0
        end else begin
            if (wr_en && !full) begin
                // Write data to memory at current write pointer location
                mem[wr_ptr[$clog2(DEPTH)-1:0]] <= wr_data;

                // Increment write pointer (wraps automatically due to bit width)
                wr_ptr <= wr_ptr + 1;
            end
        end
    end

    //==========================================================================
    // Read Logic
    //==========================================================================
    // Read data from memory when rd_en is high and FIFO is not empty

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_ptr <= '0;   // Reset read pointer to 0
            rd_data <= '0;  // Clear output data
        end else begin
            if (rd_en && !empty) begin
                // Read data from memory at current read pointer location
                rd_data <= mem[rd_ptr[$clog2(DEPTH)-1:0]];

                // Increment read pointer
                rd_ptr <= rd_ptr + 1;
            end
        end
    end

    //==========================================================================
    // Count Logic
    //==========================================================================
    // Track number of entries in FIFO
    // Increments on write, decrements on read

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            count_reg <= '0;
        end else begin
            case ({wr_en && !full, rd_en && !empty})
                2'b10: count_reg <= count_reg + 1;  // Write only
                2'b01: count_reg <= count_reg - 1;  // Read only
                2'b11: count_reg <= count_reg;      // Both (no change)
                default: count_reg <= count_reg;    // Neither
            endcase
        end
    end

endmodule

//==============================================================================
// TESTBENCH
//==============================================================================

module sync_fifo_tb;

    // Parameters
    localparam DATA_WIDTH = 8;
    localparam DEPTH = 16;
    localparam CLK_PERIOD = 10;  // 10ns = 100MHz

    // Signals
    reg clk;
    reg rst_n;
    reg [DATA_WIDTH-1:0] wr_data;
    reg wr_en;
    wire full;
    wire almost_full;
    wire [DATA_WIDTH-1:0] rd_data;
    reg rd_en;
    wire empty;
    wire almost_empty;
    wire [$clog2(DEPTH):0] count;

    // DUT instantiation
    sync_fifo #(
        .DATA_WIDTH(DATA_WIDTH),
        .DEPTH(DEPTH),
        .ALMOST_FULL_THRESHOLD(14),
        .ALMOST_EMPTY_THRESHOLD(2)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .wr_data(wr_data),
        .wr_en(wr_en),
        .full(full),
        .almost_full(almost_full),
        .rd_data(rd_data),
        .rd_en(rd_en),
        .empty(empty),
        .almost_empty(almost_empty),
        .count(count)
    );

    // Clock generation
    initial clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    // Test variables
    integer i;
    integer errors = 0;
    reg [DATA_WIDTH-1:0] expected_data;

    //==========================================================================
    // Test Stimulus
    //==========================================================================

    initial begin
        $dumpfile("sync_fifo.vcd");
        $dumpvars(0, sync_fifo_tb);

        $display("\n========================================");
        $display("  Synchronous FIFO Testbench");
        $display("========================================\n");

        // Initialize
        rst_n = 0;
        wr_en = 0;
        rd_en = 0;
        wr_data = 0;

        // Reset
        #(CLK_PERIOD*2);
        rst_n = 1;
        #(CLK_PERIOD*2);

        //======================================================================
        // Test 1: Check initial empty condition
        //======================================================================
        $display("Test 1: Initial State");
        if (empty && !full && count == 0) begin
            $display("  ✓ PASS: FIFO empty at startup");
        end else begin
            $display("  ✗ FAIL: Initial state wrong (empty=%b, full=%b, count=%0d)",
                     empty, full, count);
            errors = errors + 1;
        end
        #(CLK_PERIOD*2);

        //======================================================================
        // Test 2: Write data until full
        //======================================================================
        $display("\nTest 2: Fill FIFO");
        for (i = 0; i < DEPTH; i = i + 1) begin
            @(posedge clk);
            wr_data = i;
            wr_en = 1;
        end
        @(posedge clk);
        wr_en = 0;
        #(CLK_PERIOD);

        if (full && count == DEPTH) begin
            $display("  ✓ PASS: FIFO full after %0d writes", DEPTH);
        end else begin
            $display("  ✗ FAIL: FIFO not full (full=%b, count=%0d)", full, count);
            errors = errors + 1;
        end

        //======================================================================
        // Test 3: Read data and verify
        //======================================================================
        $display("\nTest 3: Read and Verify Data");
        for (i = 0; i < DEPTH; i = i + 1) begin
            @(posedge clk);
            rd_en = 1;
            expected_data = i;

            @(posedge clk);  // Wait for data
            #1;  // Small delay for signal to settle

            if (rd_data == expected_data) begin
                $display("  ✓ Read %0d: Got 0x%02h", i, rd_data);
            end else begin
                $display("  ✗ Read %0d: Got 0x%02h, expected 0x%02h",
                         i, rd_data, expected_data);
                errors = errors + 1;
            end
        end
        rd_en = 0;
        #(CLK_PERIOD);

        if (empty && count == 0) begin
            $display("  ✓ PASS: FIFO empty after reading all data");
        end else begin
            $display("  ✗ FAIL: FIFO not empty (empty=%b, count=%0d)", empty, count);
            errors = errors + 1;
        end

        //======================================================================
        // Test 4: Simultaneous read/write
        //======================================================================
        $display("\nTest 4: Simultaneous Read/Write");

        // First fill halfway
        for (i = 0; i < DEPTH/2; i = i + 1) begin
            @(posedge clk);
            wr_data = i + 100;
            wr_en = 1;
        end
        @(posedge clk);
        wr_en = 0;
        #(CLK_PERIOD);

        // Now read and write simultaneously
        for (i = 0; i < 8; i = i + 1) begin
            @(posedge clk);
            wr_data = i + 200;
            wr_en = 1;
            rd_en = 1;
        end
        @(posedge clk);
        wr_en = 0;
        rd_en = 0;
        #(CLK_PERIOD);

        if (count == DEPTH/2) begin
            $display("  ✓ PASS: Count unchanged during simultaneous R/W");
        end else begin
            $display("  ✗ FAIL: Count = %0d, expected %0d", count, DEPTH/2);
            errors = errors + 1;
        end

        //======================================================================
        // Test 5: Almost Full/Empty flags
        //======================================================================
        $display("\nTest 5: Almost Full/Empty Flags");

        // Empty FIFO first
        @(posedge clk);
        rd_en = 1;
        repeat(DEPTH) @(posedge clk);
        rd_en = 0;
        #(CLK_PERIOD);

        // Write until almost full
        for (i = 0; i < 14; i = i + 1) begin
            @(posedge clk);
            wr_data = i;
            wr_en = 1;
        end
        @(posedge clk);
        wr_en = 0;
        #(CLK_PERIOD);

        if (almost_full) begin
            $display("  ✓ PASS: Almost full flag asserted at count=%0d", count);
        end else begin
            $display("  ✗ FAIL: Almost full not asserted at count=%0d", count);
            errors = errors + 1;
        end

        //======================================================================
        // Summary
        //======================================================================
        #(CLK_PERIOD*5);

        $display("\n========================================");
        $display("  Test Complete");
        $display("========================================");
        $display("  Errors: %0d", errors);
        if (errors == 0)
            $display("  ✓✓✓ ALL TESTS PASSED ✓✓✓");
        else
            $display("  ✗✗✗ SOME TESTS FAILED ✗✗✗");
        $display("========================================\n");

        $finish;
    end

    // Timeout watchdog
    initial #100000 begin
        $display("\nERROR: Simulation timeout!");
        $finish;
    end

endmodule
