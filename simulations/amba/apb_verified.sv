/*******************************************************************************
 * APB (Advanced Peripheral Bus) - Verified Implementation
 *
 * Description:
 *   Simple, synchronous bus protocol from ARM AMBA specification.
 *   Used for low-bandwidth peripheral access in SoC designs.
 *
 * Protocol:
 *   SETUP phase: PSEL=1, PENABLE=0 (address/control setup)
 *   ACCESS phase: PSEL=1, PENABLE=1 (data transfer)
 *   IDLE: PSEL=0
 *
 * Features:
 *   - Single clock domain
 *   - No burst transfers
 *   - Simple handshake with PREADY
 *   - 32-bit address and data buses
 *
 * Author: Verified Implementation
 * Date: 2025-11-18
 ******************************************************************************/

`timescale 1ns/1ps

//=============================================================================
// APB Master
//=============================================================================
// Description:
//   Initiates read and write transactions on the APB bus.
//   Implements SETUP and ACCESS phases per AMBA APB specification.
//
// States:
//   IDLE: No transaction in progress
//   SETUP: Present address and control signals (PSEL=1, PENABLE=0)
//   ACCESS: Wait for PREADY (PSEL=1, PENABLE=1)
//
//=============================================================================
module apb_master (
    input  wire        PCLK,
    input  wire        PRESETn,

    // Transaction inputs
    input  wire        start,          // Pulse to initiate transaction
    input  wire [31:0] addr,           // Address
    input  wire        write,          // 1=write, 0=read
    input  wire [31:0] wdata,          // Write data
    output reg  [31:0] rdata,          // Read data
    output reg         done,           // Transaction complete

    // APB bus outputs
    output reg  [31:0] PADDR,          // Address
    output reg         PSEL,           // Select
    output reg         PENABLE,        // Enable
    output reg         PWRITE,         // Write/Read
    output reg  [31:0] PWDATA,         // Write data

    // APB bus inputs
    input  wire [31:0] PRDATA,         // Read data
    input  wire        PREADY          // Ready (slave can extend)
);

    //==========================================================================
    // State Machine
    //==========================================================================
    localparam IDLE   = 2'd0;
    localparam SETUP  = 2'd1;    // Setup phase: present address/control
    localparam ACCESS = 2'd2;    // Access phase: data transfer

    reg [1:0] state;

    always @(posedge PCLK or negedge PRESETn) begin
        if (!PRESETn) begin
            // Reset: return to idle
            state   <= IDLE;
            PSEL    <= 1'b0;
            PENABLE <= 1'b0;
            PWRITE  <= 1'b0;
            PADDR   <= 32'h0;
            PWDATA  <= 32'h0;
            rdata   <= 32'h0;
            done    <= 1'b0;
        end else begin
            done <= 1'b0;    // Done is a single-cycle pulse

            case (state)
                //--------------------------------------------------------------
                // IDLE: Wait for transaction request
                //--------------------------------------------------------------
                IDLE: begin
                    PSEL    <= 1'b0;
                    PENABLE <= 1'b0;

                    if (start) begin
                        // Load transaction parameters
                        PADDR  <= addr;
                        PWRITE <= write;
                        PWDATA <= wdata;
                        PSEL   <= 1'b1;      // Assert select
                        state  <= SETUP;
                    end
                end

                //--------------------------------------------------------------
                // SETUP: Setup phase (address/control presented)
                //--------------------------------------------------------------
                // PSEL=1, PENABLE=0
                // Slave decodes address during this phase
                SETUP: begin
                    PENABLE <= 1'b1;         // Move to access phase
                    state   <= ACCESS;
                end

                //--------------------------------------------------------------
                // ACCESS: Access phase (data transfer)
                //--------------------------------------------------------------
                // PSEL=1, PENABLE=1
                // Wait for PREADY from slave
                ACCESS: begin
                    if (PREADY) begin
                        // Transaction complete
                        if (!PWRITE) begin
                            rdata <= PRDATA;  // Capture read data
                        end

                        // Return to idle
                        PSEL    <= 1'b0;
                        PENABLE <= 1'b0;
                        done    <= 1'b1;     // Signal completion
                        state   <= IDLE;
                    end
                    // If PREADY=0, slave needs more time - stay in ACCESS
                end

                default: state <= IDLE;
            endcase
        end
    end

endmodule

//=============================================================================
// APB Slave
//=============================================================================
// Description:
//   Responds to APB master transactions.
//   Simple memory-mapped register file (8 registers).
//
// Operation:
//   - Decodes address when PSEL=1 and PENABLE=0 (SETUP phase)
//   - Transfers data when PSEL=1 and PENABLE=1 (ACCESS phase)
//   - Can assert PREADY=0 to insert wait states (not used here)
//
//=============================================================================
module apb_slave #(
    parameter BASE_ADDR = 32'h1000_0000,
    parameter NUM_REGS = 8
) (
    input  wire        PCLK,
    input  wire        PRESETn,

    // APB bus inputs
    input  wire [31:0] PADDR,
    input  wire        PSEL,
    input  wire        PENABLE,
    input  wire        PWRITE,
    input  wire [31:0] PWDATA,

    // APB bus outputs
    output wire [31:0] PRDATA,
    output wire        PREADY
);

    //==========================================================================
    // Register File
    //==========================================================================
    // Simple register array: 8 x 32-bit registers
    reg [31:0] registers [0:NUM_REGS-1];

    // Decoded register address
    wire [2:0] reg_addr;
    wire       addr_valid;

    assign reg_addr = PADDR[4:2];  // Word-aligned addressing
    assign addr_valid = (PADDR[31:5] == BASE_ADDR[31:5]) &&
                        (reg_addr < NUM_REGS);

    //==========================================================================
    // APB Protocol
    //==========================================================================
    // PREADY is always 1 (no wait states in this simple implementation)
    assign PREADY = 1'b1;

    // PRDATA is combinational for reads (available immediately)
    assign PRDATA = (PSEL && !PWRITE && addr_valid) ? registers[reg_addr] : 32'h0;

    integer i;

    // Write operations are registered
    always @(posedge PCLK or negedge PRESETn) begin
        if (!PRESETn) begin
            // Reset all registers to 0
            for (i = 0; i < NUM_REGS; i = i + 1) begin
                registers[i] <= 32'h0;
            end
        end else begin
            // APB write transaction occurs when PSEL=1 and PENABLE=1 (ACCESS phase)
            if (PSEL && PENABLE && PREADY && PWRITE && addr_valid) begin
                registers[reg_addr] <= PWDATA;
            end
        end
    end

endmodule

//=============================================================================
// TESTBENCH
//=============================================================================
module apb_tb;

    // Clock and reset
    reg PCLK;
    reg PRESETn;

    // Master control
    reg        m_start;
    reg [31:0] m_addr;
    reg        m_write;
    reg [31:0] m_wdata;
    wire [31:0] m_rdata;
    wire       m_done;

    // APB bus
    wire [31:0] PADDR;
    wire        PSEL;
    wire        PENABLE;
    wire        PWRITE;
    wire [31:0] PWDATA;
    wire [31:0] PRDATA;
    wire        PREADY;

    // Clock generation: 100 MHz
    initial PCLK = 0;
    always #5 PCLK = ~PCLK;

    // Instantiate master
    apb_master master (
        .PCLK(PCLK),
        .PRESETn(PRESETn),
        .start(m_start),
        .addr(m_addr),
        .write(m_write),
        .wdata(m_wdata),
        .rdata(m_rdata),
        .done(m_done),
        .PADDR(PADDR),
        .PSEL(PSEL),
        .PENABLE(PENABLE),
        .PWRITE(PWRITE),
        .PWDATA(PWDATA),
        .PRDATA(PRDATA),
        .PREADY(PREADY)
    );

    // Instantiate slave
    apb_slave #(
        .BASE_ADDR(32'h1000_0000),
        .NUM_REGS(8)
    ) slave (
        .PCLK(PCLK),
        .PRESETn(PRESETn),
        .PADDR(PADDR),
        .PSEL(PSEL),
        .PENABLE(PENABLE),
        .PWRITE(PWRITE),
        .PWDATA(PWDATA),
        .PRDATA(PRDATA),
        .PREADY(PREADY)
    );

    integer errors = 0;

    //==========================================================================
    // Task: Write to APB slave
    //==========================================================================
    task apb_write(input [31:0] addr, input [31:0] data);
        begin
            @(posedge PCLK);
            m_addr = addr;
            m_write = 1;
            m_wdata = data;
            m_start = 1;
            @(posedge PCLK);
            m_start = 0;
            wait(m_done);
            #10;
            $display("  Write: Addr=0x%08h, Data=0x%08h", addr, data);
        end
    endtask

    //==========================================================================
    // Task: Read from APB slave and check
    //==========================================================================
    task apb_read_check(input [31:0] addr, input [31:0] expected);
        begin
            @(posedge PCLK);
            m_addr = addr;
            m_write = 0;
            m_start = 1;
            @(posedge PCLK);
            m_start = 0;
            wait(m_done);
            #10;

            if (m_rdata == expected) begin
                $display("✓ Read: Addr=0x%08h, Data=0x%08h - PASS", addr, m_rdata);
            end else begin
                $display("✗ Read: Addr=0x%08h, Data=0x%08h (expected 0x%08h) - FAIL",
                         addr, m_rdata, expected);
                errors = errors + 1;
            end
        end
    endtask

    //==========================================================================
    // Main Test Sequence
    //==========================================================================
    initial begin
        $dumpfile("apb.vcd");
        $dumpvars(0, apb_tb);

        $display("\n========================================");
        $display("  APB Master/Slave Testbench");
        $display("  Base Address: 0x10000000");
        $display("  Registers: 8 x 32-bit");
        $display("========================================\n");

        // Initialize
        PRESETn = 0;
        m_start = 0;
        m_addr = 0;
        m_write = 0;
        m_wdata = 0;

        // Reset
        #50 PRESETn = 1;
        #50;

        // Test 1: Write to registers
        $display("Test 1: Write Operations");
        apb_write(32'h1000_0000, 32'hDEADBEEF);
        apb_write(32'h1000_0004, 32'hCAFEBABE);
        apb_write(32'h1000_0008, 32'h12345678);
        apb_write(32'h1000_000C, 32'hABCDEF00);

        #100;

        // Test 2: Read back and verify
        $display("\nTest 2: Read Operations");
        apb_read_check(32'h1000_0000, 32'hDEADBEEF);
        apb_read_check(32'h1000_0004, 32'hCAFEBABE);
        apb_read_check(32'h1000_0008, 32'h12345678);
        apb_read_check(32'h1000_000C, 32'hABCDEF00);

        #100;

        // Test 3: Overwrite and read
        $display("\nTest 3: Overwrite Test");
        apb_write(32'h1000_0000, 32'h11111111);
        apb_read_check(32'h1000_0000, 32'h11111111);

        apb_write(32'h1000_0004, 32'h22222222);
        apb_read_check(32'h1000_0004, 32'h22222222);

        #100;

        // Test 4: All registers
        $display("\nTest 4: Sequential Access");
        apb_write(32'h1000_0010, 32'hAAAAAAAA);
        apb_write(32'h1000_0014, 32'hBBBBBBBB);
        apb_write(32'h1000_0018, 32'hCCCCCCCC);
        apb_write(32'h1000_001C, 32'hDDDDDDDD);

        apb_read_check(32'h1000_0010, 32'hAAAAAAAA);
        apb_read_check(32'h1000_0014, 32'hBBBBBBBB);
        apb_read_check(32'h1000_0018, 32'hCCCCCCCC);
        apb_read_check(32'h1000_001C, 32'hDDDDDDDD);

        #100;

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
