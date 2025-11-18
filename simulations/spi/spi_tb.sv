/*******************************************************************************
 * Testbench: spi_tb
 *
 * Description:
 *   Comprehensive testbench for SPI master and slave modules.
 *   Tests multiple SPI modes and data transfers.
 *
 * Test Scenarios:
 *   1. Mode 0 (CPOL=0, CPHA=0) - Single transfer
 *   2. Mode 1 (CPOL=0, CPHA=1) - Single transfer
 *   3. Loopback verification (master RX matches slave TX)
 *   4. Multiple consecutive transfers
 *
 * Expected Results:
 *   - Master transmits data correctly to slave
 *   - Slave receives master's data
 *   - Slave transmits data correctly to master
 *   - Master receives slave's data
 *   - All modes function correctly
 *
 * Author: Auto-generated
 * Date: 2025
 ******************************************************************************/

`timescale 1ns/1ps

module spi_tb;

    //==========================================================================
    // Testbench Signals
    //==========================================================================

    // Clock and reset
    logic clk;
    logic rst_n;

    // Master signals
    logic [7:0] m_tx_data;   // Data master will send
    logic m_tx_valid;         // Master starts transfer
    logic m_tx_ready;         // Master ready for new data
    logic [7:0] m_rx_data;   // Data master receives
    logic m_rx_valid;         // Master received data valid

    // Slave signals
    logic [7:0] s_tx_data;   // Data slave will send
    logic s_tx_valid;         // Slave data ready
    logic s_tx_ready;         // Slave ready for new data
    logic [7:0] s_rx_data;   // Data slave receives
    logic s_rx_valid;         // Slave received data valid

    // SPI bus signals (connecting master and slave)
    logic sclk;    // SPI clock (master drives, slave receives)
    logic mosi;    // Master to slave data
    logic miso;    // Slave to master data
    logic cs_n;    // Chip select (active low)

    // Configuration signals
    logic cpol = 0;  // Clock polarity: starts at 0
    logic cpha = 0;  // Clock phase: starts at 0

    //==========================================================================
    // DUT Instantiation - Master
    //==========================================================================

    spi_master #(
        .DATA_WIDTH(8),
        .CLK_DIV(4)     // Divide 100MHz by 4 = 25MHz SPI clock
    ) master (
        .clk(clk),
        .rst_n(rst_n),
        .tx_data(m_tx_data),
        .tx_valid(m_tx_valid),
        .tx_ready(m_tx_ready),
        .rx_data(m_rx_data),
        .rx_valid(m_rx_valid),
        .sclk(sclk),
        .mosi(mosi),
        .miso(miso),
        .cs_n(cs_n),
        .cpol(cpol),
        .cpha(cpha)
    );

    //==========================================================================
    // DUT Instantiation - Slave
    //==========================================================================

    spi_slave #(
        .DATA_WIDTH(8)
    ) slave (
        .clk(clk),
        .rst_n(rst_n),
        .tx_data(s_tx_data),
        .tx_valid(s_tx_valid),
        .tx_ready(s_tx_ready),
        .rx_data(s_rx_data),
        .rx_valid(s_rx_valid),
        .sclk(sclk),
        .mosi(mosi),
        .miso(miso),
        .cs_n(cs_n),
        .cpol(cpol),
        .cpha(cpha)
    );

    //==========================================================================
    // Clock Generation
    //==========================================================================
    // Generate 100 MHz clock (10ns period)

    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // Toggle every 5ns = 10ns period = 100MHz
    end

    //==========================================================================
    // Test Stimulus
    //==========================================================================

    initial begin
        // Initialize waveform dump for viewing in GTKWave
        $dumpfile("spi_tb.vcd");
        $dumpvars(0, spi_tb);

        // Initialize all signals
        rst_n = 0;
        m_tx_valid = 0;
        s_tx_valid = 0;
        m_tx_data = 0;
        s_tx_data = 0;

        // Apply reset
        $display("\n========================================");
        $display("SPI Master-Slave Testbench Starting");
        $display("========================================\n");

        repeat(2) @(posedge clk);
        rst_n = 1;  // Release reset
        repeat(5) @(posedge clk);

        //======================================================================
        // Test 1: Mode 0 (CPOL=0, CPHA=0)
        //======================================================================
        $display("----------------------------------------");
        $display("Test 1: SPI Mode 0 (CPOL=0, CPHA=0)");
        $display("----------------------------------------");
        cpol = 0;
        cpha = 0;
        repeat(5) @(posedge clk);

        // Master sends 0xA5, Slave sends 0x5A
        m_tx_data = 8'hA5;
        s_tx_data = 8'h5A;
        m_tx_valid = 1;
        s_tx_valid = 1;
        @(posedge clk);
        m_tx_valid = 0;
        s_tx_valid = 0;

        // Wait for transaction to complete
        wait(m_rx_valid);
        @(posedge clk);

        // Check results
        if (m_rx_data == 8'h5A && s_rx_data == 8'hA5) begin
            $display("[PASS] Master RX: 0x%h (expected 0x5A)", m_rx_data);
            $display("[PASS] Slave RX:  0x%h (expected 0xA5)", s_rx_data);
        end else begin
            $display("[FAIL] Master RX: 0x%h (expected 0x5A)", m_rx_data);
            $display("[FAIL] Slave RX:  0x%h (expected 0xA5)", s_rx_data);
        end

        repeat(10) @(posedge clk);

        //======================================================================
        // Test 2: Mode 1 (CPOL=0, CPHA=1)
        //======================================================================
        $display("\n----------------------------------------");
        $display("Test 2: SPI Mode 1 (CPOL=0, CPHA=1)");
        $display("----------------------------------------");
        cpol = 0;
        cpha = 1;
        repeat(5) @(posedge clk);

        // Master sends 0x3C, Slave sends 0xC3
        m_tx_data = 8'h3C;
        s_tx_data = 8'hC3;
        m_tx_valid = 1;
        s_tx_valid = 1;
        @(posedge clk);
        m_tx_valid = 0;
        s_tx_valid = 0;

        wait(m_rx_valid);
        @(posedge clk);

        // Check results
        if (m_rx_data == 8'hC3 && s_rx_data == 8'h3C) begin
            $display("[PASS] Master RX: 0x%h (expected 0xC3)", m_rx_data);
            $display("[PASS] Slave RX:  0x%h (expected 0x3C)", s_rx_data);
        end else begin
            $display("[FAIL] Master RX: 0x%h (expected 0xC3)", m_rx_data);
            $display("[FAIL] Slave RX:  0x%h (expected 0x3C)", s_rx_data);
        end

        repeat(10) @(posedge clk);

        //======================================================================
        // Test 3: Mode 2 (CPOL=1, CPHA=0)
        //======================================================================
        $display("\n----------------------------------------");
        $display("Test 3: SPI Mode 2 (CPOL=1, CPHA=0)");
        $display("----------------------------------------");
        cpol = 1;
        cpha = 0;
        repeat(5) @(posedge clk);

        m_tx_data = 8'hF0;
        s_tx_data = 8'h0F;
        m_tx_valid = 1;
        s_tx_valid = 1;
        @(posedge clk);
        m_tx_valid = 0;
        s_tx_valid = 0;

        wait(m_rx_valid);
        @(posedge clk);

        if (m_rx_data == 8'h0F && s_rx_data == 8'hF0) begin
            $display("[PASS] Master RX: 0x%h (expected 0x0F)", m_rx_data);
            $display("[PASS] Slave RX:  0x%h (expected 0xF0)", s_rx_data);
        end else begin
            $display("[FAIL] Master RX: 0x%h (expected 0x0F)", m_rx_data);
            $display("[FAIL] Slave RX:  0x%h (expected 0xF0)", s_rx_data);
        end

        repeat(10) @(posedge clk);

        //======================================================================
        // Test 4: Mode 3 (CPOL=1, CPHA=1)
        //======================================================================
        $display("\n----------------------------------------");
        $display("Test 4: SPI Mode 3 (CPOL=1, CPHA=1)");
        $display("----------------------------------------");
        cpol = 1;
        cpha = 1;
        repeat(5) @(posedge clk);

        m_tx_data = 8'h55;
        s_tx_data = 8'hAA;
        m_tx_valid = 1;
        s_tx_valid = 1;
        @(posedge clk);
        m_tx_valid = 0;
        s_tx_valid = 0;

        wait(m_rx_valid);
        @(posedge clk);

        if (m_rx_data == 8'hAA && s_rx_data == 8'h55) begin
            $display("[PASS] Master RX: 0x%h (expected 0xAA)", m_rx_data);
            $display("[PASS] Slave RX:  0x%h (expected 0x55)", s_rx_data);
        end else begin
            $display("[FAIL] Master RX: 0x%h (expected 0xAA)", m_rx_data);
            $display("[FAIL] Slave RX:  0x%h (expected 0x55)", s_rx_data);
        end

        repeat(10) @(posedge clk);

        //======================================================================
        // Test 5: Multiple back-to-back transfers (Mode 0)
        //======================================================================
        $display("\n----------------------------------------");
        $display("Test 5: Multiple Consecutive Transfers");
        $display("----------------------------------------");
        cpol = 0;
        cpha = 0;
        repeat(5) @(posedge clk);

        for (int i = 0; i < 5; i++) begin
            wait(m_tx_ready);  // Wait for master to be ready
            m_tx_data = i;
            s_tx_data = 8'hFF - i;
            m_tx_valid = 1;
            s_tx_valid = 1;
            @(posedge clk);
            m_tx_valid = 0;
            s_tx_valid = 0;

            wait(m_rx_valid);
            @(posedge clk);

            if (m_rx_data == (8'hFF - i) && s_rx_data == i) begin
                $display("[PASS] Transfer %0d: M_RX=0x%h, S_RX=0x%h",
                         i, m_rx_data, s_rx_data);
            end else begin
                $display("[FAIL] Transfer %0d: M_RX=0x%h (exp 0x%h), S_RX=0x%h (exp 0x%h)",
                         i, m_rx_data, (8'hFF - i), s_rx_data, i);
            end
        end

        repeat(20) @(posedge clk);

        //======================================================================
        // Test Complete
        //======================================================================
        $display("\n========================================");
        $display("SPI Testbench Complete");
        $display("========================================\n");

        $finish;
    end

    //==========================================================================
    // Timeout Watchdog
    //==========================================================================
    // Prevent simulation from hanging indefinitely

    initial begin
        #50000;  // 50 microseconds
        $display("\n[ERROR] Simulation timeout!");
        $finish;
    end

endmodule
