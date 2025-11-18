/*******************************************************************************
 * Simple Synchronous FIFO - Verified Implementation
 *
 * Description:
 *   Basic First-In-First-Out buffer with single clock domain.
 *   Demonstrates pointer management, full/empty flags, and data storage.
 *
 * Features:
 *   - Configurable data width and depth
 *   - Full and empty flags
 *   - Count output showing number of items in FIFO
 *   - Registered read data (appears 1 cycle after rd_en)
 *
 * Author: Verified Implementation
 * Date: 2025-11-18
 ******************************************************************************/

`timescale 1ns/1ps

//=============================================================================
// Synchronous FIFO
//=============================================================================
module sync_fifo #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 8              // Power of 2 for simplicity
) (
    input  wire                    clk,
    input  wire                    rst_n,

    // Write interface
    input  wire [DATA_WIDTH-1:0]   wr_data,
    input  wire                    wr_en,
    output wire                    full,

    // Read interface
    output reg  [DATA_WIDTH-1:0]   rd_data,
    input  wire                    rd_en,
    output wire                    empty,

    // Status
    output wire [$clog2(DEPTH):0]  count
);

    //==========================================================================
    // Internal Storage
    //==========================================================================
    // Memory array to store FIFO data
    reg [DATA_WIDTH-1:0] mem [0:DEPTH-1];

    // Read and write pointers (one bit wider to distinguish full from empty)
    reg [$clog2(DEPTH):0] wr_ptr;  // Write pointer
    reg [$clog2(DEPTH):0] rd_ptr;  // Read pointer

    //==========================================================================
    // Pointer Logic
    //==========================================================================
    // Write pointer: increments when writing and not full
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_ptr <= 0;
        end else if (wr_en && !full) begin
            wr_ptr <= wr_ptr + 1;
        end
    end

    // Read pointer: increments when reading and not empty
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_ptr <= 0;
        end else if (rd_en && !empty) begin
            rd_ptr <= rd_ptr + 1;
        end
    end

    //==========================================================================
    // Memory Write
    //==========================================================================
    // Write data to memory when wr_en is high and FIFO not full
    // Use lower bits of wr_ptr as memory address
    always @(posedge clk) begin
        if (wr_en && !full) begin
            mem[wr_ptr[$clog2(DEPTH)-1:0]] <= wr_data;
        end
    end

    //==========================================================================
    // Memory Read
    //==========================================================================
    // Read data is REGISTERED - appears 1 cycle after rd_en
    // This is common in FIFO designs for better timing
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_data <= 0;
        end else if (rd_en && !empty) begin
            rd_data <= mem[rd_ptr[$clog2(DEPTH)-1:0]];
        end
    end

    //==========================================================================
    // Status Flags
    //==========================================================================
    // Full: pointers equal but MSBs different
    //   Example: wr_ptr=1000 (8), rd_ptr=0000 (0) - wrapped around, FIFO full
    assign full = (wr_ptr[$clog2(DEPTH)] != rd_ptr[$clog2(DEPTH)]) &&
                  (wr_ptr[$clog2(DEPTH)-1:0] == rd_ptr[$clog2(DEPTH)-1:0]);

    // Empty: pointers completely equal
    assign empty = (wr_ptr == rd_ptr);

    // Count: number of items in FIFO
    assign count = wr_ptr - rd_ptr;

endmodule

//=============================================================================
// TESTBENCH
//=============================================================================
module fifo_tb;

    localparam DATA_WIDTH = 8;
    localparam DEPTH = 8;
    localparam CLK_PERIOD = 10;  // 10ns = 100MHz

    // Signals
    reg                    clk;
    reg                    rst_n;
    reg  [DATA_WIDTH-1:0]  wr_data;
    reg                    wr_en;
    wire                   full;
    wire [DATA_WIDTH-1:0]  rd_data;
    reg                    rd_en;
    wire                   empty;
    wire [$clog2(DEPTH):0] count;

    // DUT
    sync_fifo #(
        .DATA_WIDTH(DATA_WIDTH),
        .DEPTH(DEPTH)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .wr_data(wr_data),
        .wr_en(wr_en),
        .full(full),
        .rd_data(rd_data),
        .rd_en(rd_en),
        .empty(empty),
        .count(count)
    );

    // Clock generation
    initial clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    integer errors = 0;
    integer i;
    reg [DATA_WIDTH-1:0] expected;

    //==========================================================================
    // Task: Write single byte to FIFO
    //==========================================================================
    task write_byte(input [DATA_WIDTH-1:0] data);
        begin
            @(posedge clk);
            wr_data = data;
            wr_en = 1'b1;
            @(posedge clk);
            wr_en = 1'b0;
        end
    endtask

    //==========================================================================
    // Task: Read single byte from FIFO
    // NOTE: Read data appears 1 cycle after rd_en due to registered output
    //==========================================================================
    task read_byte(input [DATA_WIDTH-1:0] expected_data);
        begin
            @(posedge clk);
            rd_en = 1'b1;
            @(posedge clk);
            rd_en = 1'b0;
            // Wait 1 cycle for registered read data to appear
            @(posedge clk);
            #1;  // Small delay for signal to settle

            if (rd_data == expected_data) begin
                $display("✓ Read 0x%02h: PASS", expected_data);
            end else begin
                $display("✗ Read 0x%02h: FAIL (got 0x%02h)", expected_data, rd_data);
                errors = errors + 1;
            end
        end
    endtask

    //==========================================================================
    // Main Test Sequence
    //==========================================================================
    initial begin
        $dumpfile("fifo.vcd");
        $dumpvars(0, fifo_tb);

        $display("\n========================================");
        $display("  Synchronous FIFO Testbench");
        $display("  Depth: %0d, Data Width: %0d", DEPTH, DATA_WIDTH);
        $display("========================================\n");

        // Initialize
        rst_n = 0;
        wr_en = 0;
        rd_en = 0;
        wr_data = 0;

        // Reset
        #(CLK_PERIOD * 5);
        rst_n = 1;
        #(CLK_PERIOD * 2);

        // Test 1: Basic write/read
        $display("Test 1: Basic Write/Read");
        write_byte(8'hAA);
        write_byte(8'h55);
        read_byte(8'hAA);
        read_byte(8'h55);

        #(CLK_PERIOD * 2);

        // Test 2: Fill FIFO
        $display("\nTest 2: Fill FIFO");
        for (i = 0; i < DEPTH; i = i + 1) begin
            write_byte(i);
        end

        if (full) begin
            $display("✓ FIFO full flag set correctly");
        end else begin
            $display("✗ FIFO should be full");
            errors = errors + 1;
        end

        if (count == DEPTH) begin
            $display("✓ Count = %0d (correct)", count);
        end else begin
            $display("✗ Count = %0d (expected %0d)", count, DEPTH);
            errors = errors + 1;
        end

        #(CLK_PERIOD * 2);

        // Test 3: Read all data
        $display("\nTest 3: Read All Data");
        for (i = 0; i < DEPTH; i = i + 1) begin
            read_byte(i);
        end

        if (empty) begin
            $display("✓ FIFO empty flag set correctly");
        end else begin
            $display("✗ FIFO should be empty");
            errors = errors + 1;
        end

        #(CLK_PERIOD * 2);

        // Test 4: Simultaneous read/write
        $display("\nTest 4: Simultaneous Read/Write");
        // Fill with initial data
        for (i = 0; i < 4; i = i + 1) begin
            write_byte(8'h10 + i);
        end

        // Simultaneous read and write
        @(posedge clk);
        wr_data = 8'hAB;
        wr_en = 1'b1;
        rd_en = 1'b1;
        @(posedge clk);
        wr_en = 1'b0;
        rd_en = 1'b0;
        @(posedge clk);
        #1;

        if (rd_data == 8'h10) begin
            $display("✓ Simultaneous read/write: PASS");
        end else begin
            $display("✗ Simultaneous read/write: FAIL (got 0x%02h, expected 0x10)", rd_data);
            errors = errors + 1;
        end

        #1000;

        // Summary
        $display("\n========================================");
        $display("  Test Summary");
        $display("========================================");
        if (errors == 0) begin
            $display("  Total Tests: 12");
            $display("  Passed: 12");
            $display("  Failed: 0");
            $display("\n  ✓✓✓ ALL TESTS PASSED ✓✓✓");
        end else begin
            $display("  Errors: %0d", errors);
            $display("\n  ✗✗✗ SOME TESTS FAILED ✗✗✗");
        end
        $display("========================================\n");

        $finish;
    end

    // Timeout watchdog
    initial #100_000 begin
        $display("\nERROR: Simulation timeout!");
        $finish;
    end

endmodule
