/*******************************************************************************
 * I2C Implementation - Simplified and Verified
 *
 * Description:
 *   Simplified I2C master and slave for reliable simulation.
 *   Implements core I2C protocol: START, address, data, ACK, STOP
 *
 * Protocol Summary:
 *   - START: SDA falls while SCL high
 *   - 8 bits transferred MSB first (7-bit addr + R/W, or 8-bit data)
 *   - ACK: Receiver pulls SDA low during 9th clock
 *   - STOP: SDA rises while SCL high
 *
 * Simplified for simulation clarity - single clock domain
 *
 * Author: Verified Implementation
 * Date: 2025-11-18
 ******************************************************************************/

`timescale 1ns/1ps

//=============================================================================
// I2C Master - Simplified single-byte transfer
//=============================================================================
module i2c_master #(
    parameter CLK_DIV = 100  // Divide system clock for I2C clock
) (
    input  wire       clk,
    input  wire       rst_n,

    // Control
    input  wire       start,       // Start transaction (pulse high for 1 clk)
    input  wire [6:0] slave_addr,  // 7-bit slave address
    input  wire       rw_bit,      // 0=write, 1=read
    input  wire [7:0] wr_data,     // Data to write (if write operation)
    output reg  [7:0] rd_data,     // Data read (if read operation)
    output reg        ack,          // ACK bit from slave
    output reg        busy,        // Transaction in progress

    // I2C bus
    output reg        scl,
    inout  wire       sda
);

    //==========================================================================
    // State Machine
    //==========================================================================
    // States for I2C transaction
    localparam IDLE       = 4'd0;   // Waiting for start command
    localparam START      = 4'd1;   // Generate START condition
    localparam ADDR       = 4'd2;   // Send 7-bit address + R/W bit
    localparam ACK_ADDR   = 4'd3;   // Receive ACK for address
    localparam WRITE_DATA = 4'd4;   // Send data byte (write operation)
    localparam ACK_WR     = 4'd5;   // Receive ACK for written data
    localparam READ_DATA  = 4'd6;   // Receive data byte (read operation)
    localparam SEND_NACK  = 4'd7;   // Send NACK after read
    localparam STOP       = 4'd8;   // Generate STOP condition

    reg [3:0] state;
    reg [7:0] clk_count;   // Clock divider counter
    reg [3:0] bit_count;   // Bit counter (0-7 for data, 8 for ACK)
    reg [7:0] shift_reg;   // Shift register for TX/RX
    reg       sda_out;      // SDA output value
    reg       sda_oe;       // SDA output enable (1=drive, 0=tri-state)

    // SDA tri-state control: drive when enabled, else high-Z
    assign sda = sda_oe ? sda_out : 1'bz;

    //==========================================================================
    // Main State Machine
    //==========================================================================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            scl <= 1'b1;           // SCL idles high
            sda_out <= 1'b1;
            sda_oe <= 1'b0;        // Release SDA (high-Z)
            busy <= 1'b0;
            ack <= 1'b0;
            clk_count <= 0;
            bit_count <= 0;
        end else begin
            case (state)
                //--------------------------------------------------------------
                // IDLE: Wait for start command
                //--------------------------------------------------------------
                IDLE: begin
                    scl <= 1'b1;
                    sda_out <= 1'b1;
                    sda_oe <= 1'b0;
                    busy <= 1'b0;
                    clk_count <= 0;
                    bit_count <= 0;

                    if (start) begin
                        shift_reg <= {slave_addr, rw_bit};  // Load address + R/W
                        state <= START;
                        busy <= 1'b1;
                    end
                end

                //--------------------------------------------------------------
                // START: Generate START condition
                // START = SDA falls while SCL is high
                //--------------------------------------------------------------
                START: begin
                    if (clk_count == 0) begin
                        // Initially both high
                        scl <= 1'b1;
                        sda_out <= 1'b1;
                        sda_oe <= 1'b1;
                        clk_count <= clk_count + 1;
                    end else if (clk_count < CLK_DIV/2) begin
                        // Pull SDA low while SCL still high = START
                        sda_out <= 1'b0;
                        clk_count <= clk_count + 1;
                    end else if (clk_count < CLK_DIV) begin
                        // Pull SCL low to begin bit transfer
                        scl <= 1'b0;
                        clk_count <= clk_count + 1;
                    end else begin
                        clk_count <= 0;
                        bit_count <= 0;
                        state <= ADDR;
                    end
                end

                //--------------------------------------------------------------
                // ADDR: Send 8 bits (7-bit address + R/W bit)
                //--------------------------------------------------------------
                ADDR, WRITE_DATA: begin
                    if (clk_count == 0) begin
                        // SCL low: Set data bit on SDA
                        scl <= 1'b0;
                        sda_out <= shift_reg[7];  // MSB first
                        sda_oe <= 1'b1;
                        clk_count <= clk_count + 1;
                    end else if (clk_count < CLK_DIV/2) begin
                        // Keep SCL low (setup time)
                        clk_count <= clk_count + 1;
                    end else if (clk_count == CLK_DIV/2) begin
                        // SCL high: Data is sampled by slave
                        scl <= 1'b1;
                        clk_count <= clk_count + 1;
                    end else if (clk_count < CLK_DIV) begin
                        // Keep SCL high (hold time)
                        clk_count <= clk_count + 1;
                    end else begin
                        // Bit complete
                        clk_count <= 0;
                        shift_reg <= {shift_reg[6:0], 1'b0};  // Shift left

                        if (bit_count == 7) begin
                            bit_count <= 0;
                            // After address, check ACK
                            state <= (state == ADDR) ? ACK_ADDR : ACK_WR;
                        end else begin
                            bit_count <= bit_count + 1;
                        end
                    end
                end

                //--------------------------------------------------------------
                // ACK_ADDR, ACK_WR: Receive ACK bit from slave
                // Slave pulls SDA low for ACK, leaves high for NACK
                //--------------------------------------------------------------
                ACK_ADDR, ACK_WR: begin
                    if (clk_count == 0) begin
                        // Release SDA so slave can control it
                        scl <= 1'b0;
                        sda_oe <= 1'b0;  // Tri-state (slave will pull low for ACK)
                        clk_count <= clk_count + 1;
                    end else if (clk_count < CLK_DIV/2) begin
                        clk_count <= clk_count + 1;
                    end else if (clk_count == CLK_DIV/2) begin
                        // SCL high: Sample ACK bit
                        scl <= 1'b1;
                        ack <= (sda == 1'b0);  // ACK if SDA is low
                        clk_count <= clk_count + 1;
                    end else if (clk_count < CLK_DIV) begin
                        clk_count <= clk_count + 1;
                    end else begin
                        clk_count <= 0;

                        if (state == ACK_ADDR) begin
                            // After address ACK, do read or write
                            if (rw_bit) begin
                                state <= READ_DATA;
                                bit_count <= 0;
                            end else begin
                                shift_reg <= wr_data;  // Load write data
                                state <= WRITE_DATA;
                                bit_count <= 0;
                            end
                        end else begin
                            // After write data ACK, done
                            state <= STOP;
                        end
                    end
                end

                //--------------------------------------------------------------
                // READ_DATA: Receive 8 data bits from slave
                //--------------------------------------------------------------
                READ_DATA: begin
                    if (clk_count == 0) begin
                        // Release SDA for slave to drive
                        scl <= 1'b0;
                        sda_oe <= 1'b0;
                        clk_count <= clk_count + 1;
                    end else if (clk_count < CLK_DIV/2) begin
                        clk_count <= clk_count + 1;
                    end else if (clk_count == CLK_DIV/2) begin
                        // SCL high: Sample data bit from slave
                        scl <= 1'b1;
                        shift_reg <= {shift_reg[6:0], sda};  // Shift in bit
                        clk_count <= clk_count + 1;
                    end else if (clk_count < CLK_DIV) begin
                        clk_count <= clk_count + 1;
                    end else begin
                        clk_count <= 0;

                        if (bit_count == 7) begin
                            rd_data <= {shift_reg[6:0], sda};  // Capture complete byte
                            bit_count <= 0;
                            state <= SEND_NACK;  // Master sends NACK to end read
                        end else begin
                            bit_count <= bit_count + 1;
                        end
                    end
                end

                //--------------------------------------------------------------
                // SEND_NACK: Master sends NACK after reading (SDA high during ACK clock)
                //--------------------------------------------------------------
                SEND_NACK: begin
                    if (clk_count == 0) begin
                        scl <= 1'b0;
                        sda_out <= 1'b1;  // NACK = SDA high
                        sda_oe <= 1'b1;
                        clk_count <= clk_count + 1;
                    end else if (clk_count < CLK_DIV/2) begin
                        clk_count <= clk_count + 1;
                    end else if (clk_count == CLK_DIV/2) begin
                        scl <= 1'b1;
                        clk_count <= clk_count + 1;
                    end else if (clk_count < CLK_DIV) begin
                        clk_count <= clk_count + 1;
                    end else begin
                        clk_count <= 0;
                        state <= STOP;
                    end
                end

                //--------------------------------------------------------------
                // STOP: Generate STOP condition
                // STOP = SDA rises while SCL is high
                //--------------------------------------------------------------
                STOP: begin
                    if (clk_count == 0) begin
                        // Start with SCL low, SDA low
                        scl <= 1'b0;
                        sda_out <= 1'b0;
                        sda_oe <= 1'b1;
                        clk_count <= clk_count + 1;
                    end else if (clk_count < CLK_DIV/2) begin
                        clk_count <= clk_count + 1;
                    end else if (clk_count == CLK_DIV/2) begin
                        // Raise SCL while SDA still low
                        scl <= 1'b1;
                        clk_count <= clk_count + 1;
                    end else if (clk_count < CLK_DIV*3/4) begin
                        clk_count <= clk_count + 1;
                    end else if (clk_count == CLK_DIV*3/4) begin
                        // Raise SDA while SCL high = STOP
                        sda_out <= 1'b1;
                        clk_count <= clk_count + 1;
                    end else if (clk_count < CLK_DIV) begin
                        clk_count <= clk_count + 1;
                    end else begin
                        clk_count <= 0;
                        sda_oe <= 1'b0;  // Release SDA
                        state <= IDLE;
                    end
                end

                default: state <= IDLE;
            endcase
        end
    end

endmodule

//=============================================================================
// I2C Slave - Simplified
//=============================================================================
module i2c_slave #(
    parameter SLAVE_ADDR = 7'h50
) (
    input  wire       clk,
    input  wire       rst_n,

    // Data interface
    input  wire [7:0] tx_data,     // Data to send when master reads
    output reg  [7:0] rx_data,     // Data received from master
    output reg        rx_valid,    // Pulse when rx_data is valid

    // I2C bus
    input  wire       scl,
    inout  wire       sda
);

    //==========================================================================
    // Synchronize inputs to prevent metastability
    //==========================================================================
    reg [1:0] scl_sync, sda_sync;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            scl_sync <= 2'b11;
            sda_sync <= 2'b11;
        end else begin
            scl_sync <= {scl_sync[0], scl};
            sda_sync <= {sda_sync[0], sda};
        end
    end

    wire scl_s = scl_sync[1];
    wire sda_s = sda_sync[1];

    //==========================================================================
    // Edge Detection
    //==========================================================================
    reg scl_prev, sda_prev;
    wire scl_rising, scl_falling;
    wire sda_edge;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            scl_prev <= 1'b1;
            sda_prev <= 1'b1;
        end else begin
            scl_prev <= scl_s;
            sda_prev <= sda_s;
        end
    end

    assign scl_rising = !scl_prev && scl_s;
    assign scl_falling = scl_prev && !scl_s;
    assign sda_edge = sda_prev != sda_s;

    // START = SDA falls while SCL high
    // STOP = SDA rises while SCL high
    wire start_cond = scl_s && scl_prev && !sda_s && sda_prev;
    wire stop_cond = scl_s && scl_prev && sda_s && !sda_prev;

    //==========================================================================
    // State Machine
    //==========================================================================
    localparam IDLE     = 3'd0;
    localparam RX_ADDR  = 3'd1;
    localparam TX_ACK   = 3'd2;
    localparam RX_DATA  = 3'd3;
    localparam TX_DATA  = 3'd4;
    localparam RX_ACK   = 3'd5;

    reg [2:0]  state;
    reg [3:0]  bit_count;
    reg [7:0]  shift_reg;
    reg        sda_out;
    reg        sda_oe;
    reg        rw_bit;

    assign sda = sda_oe ? sda_out : 1'bz;

    //==========================================================================
    // Main State Machine
    //==========================================================================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            sda_out <= 1'b1;
            sda_oe <= 1'b0;
            bit_count <= 0;
            rx_valid <= 1'b0;
        end else begin
            rx_valid <= 1'b0;  // Default: pulse for one cycle

            // STOP condition resets to IDLE
            if (stop_cond) begin
                $display("[SLAVE] STOP condition detected");
                state <= IDLE;
                sda_oe <= 1'b0;
                bit_count <= 0;
            end
            // START condition begins address reception
            else if (start_cond) begin
                $display("[SLAVE] START condition detected");
                state <= RX_ADDR;
                bit_count <= 0;
                sda_oe <= 1'b0;  // Release SDA
            end
            else begin
                case (state)
                    //----------------------------------------------------------
                    // IDLE: Waiting for START condition
                    //----------------------------------------------------------
                    IDLE: begin
                        sda_oe <= 1'b0;
                        bit_count <= 0;
                    end

                    //----------------------------------------------------------
                    // RX_ADDR: Receive 8 bits (7-bit address + R/W bit)
                    //----------------------------------------------------------
                    RX_ADDR: begin
                        if (scl_rising) begin
                            // Sample bit on SCL rising edge
                            shift_reg <= {shift_reg[6:0], sda_s};
                            bit_count <= bit_count + 1;

                            if (bit_count == 7) begin
                                // All 8 bits received - shift_reg now has old 7 bits, new bit in sda_s
                                // Check if upper 7 bits match our address
                                $display("[SLAVE] RX_ADDR complete: addr_rx=0x%h, expected=0x%h, rw=%b",
                                         shift_reg[6:0], SLAVE_ADDR, sda_s);
                                if (shift_reg[6:0] == SLAVE_ADDR) begin
                                    rw_bit <= sda_s;  // LSB is R/W bit
                                    state <= TX_ACK;  // Address matches, send ACK
                                    bit_count <= 0;
                                    $display("[SLAVE] Address match! Sending ACK");
                                end else begin
                                    state <= IDLE;  // Address mismatch, ignore
                                    bit_count <= 0;
                                    $display("[SLAVE] Address mismatch, ignoring");
                                end
                            end
                        end
                    end

                    //----------------------------------------------------------
                    // TX_ACK: Send ACK by pulling SDA low
                    //----------------------------------------------------------
                    TX_ACK: begin
                        if (scl_falling) begin
                            // Pull SDA low on SCL falling edge
                            sda_out <= 1'b0;  // ACK
                            sda_oe <= 1'b1;
                            $display("[SLAVE] TX_ACK: Pulling SDA low");
                        end else if (scl_rising) begin
                            // Release SDA on SCL rising edge, prepare for next phase
                            sda_oe <= 1'b0;

                            // Transition based on R/W bit
                            if (rw_bit == 1'b0) begin
                                // Write operation: receive data from master
                                $display("[SLAVE] TX_ACK done, transitioning to RX_DATA");
                                state <= RX_DATA;
                                bit_count <= 0;
                            end else begin
                                // Read operation: send data to master
                                shift_reg <= tx_data;
                                $display("[SLAVE] TX_ACK done, transitioning to TX_DATA with data=0x%h", tx_data);
                                state <= TX_DATA;
                                bit_count <= 0;
                            end
                        end
                    end

                    //----------------------------------------------------------
                    // RX_DATA: Receive 8 data bits from master
                    //----------------------------------------------------------
                    RX_DATA: begin
                        if (scl_rising) begin
                            shift_reg <= {shift_reg[6:0], sda_s};

                            if (bit_count == 7) begin
                                rx_data <= {shift_reg[6:0], sda_s};
                                rx_valid <= 1'b1;  // Signal data is valid
                                $display("[SLAVE] RX_DATA complete: received=0x%h", {shift_reg[6:0], sda_s});
                                state <= TX_ACK;    // Send ACK for received data
                                bit_count <= 0;
                            end else begin
                                bit_count <= bit_count + 1;
                            end
                        end
                    end

                    //----------------------------------------------------------
                    // TX_DATA: Send 8 data bits to master
                    //----------------------------------------------------------
                    TX_DATA: begin
                        if (scl_falling) begin
                            // Set data bit on SCL falling edge
                            sda_out <= shift_reg[7];  // MSB first
                            sda_oe <= 1'b1;
                        end else if (scl_rising) begin
                            // Shift on SCL rising edge
                            shift_reg <= {shift_reg[6:0], 1'b0};

                            if (bit_count == 7) begin
                                state <= RX_ACK;  // Receive ACK/NACK from master
                                bit_count <= 0;
                            end else begin
                                bit_count <= bit_count + 1;
                            end
                        end
                    end

                    //----------------------------------------------------------
                    // RX_ACK: Receive ACK/NACK from master after sending data
                    //----------------------------------------------------------
                    RX_ACK: begin
                        if (scl_falling) begin
                            // Release SDA for master to send ACK/NACK
                            sda_oe <= 1'b0;
                        end else if (scl_rising) begin
                            // Could sample ACK here if needed
                            // For now, just go back to IDLE
                            state <= IDLE;
                        end
                    end

                    default: state <= IDLE;
                endcase
            end
        end
    end

endmodule

//=============================================================================
// TESTBENCH
//=============================================================================
module i2c_tb;

    reg clk, rst_n;

    // Master interface
    reg        m_start;
    reg  [6:0] m_addr;
    reg        m_rw;
    reg  [7:0] m_wr_data;
    wire [7:0] m_rd_data;
    wire       m_ack;
    wire       m_busy;

    // Slave interface
    reg  [7:0] s_tx_data;
    wire [7:0] s_rx_data;
    wire       s_rx_valid;

    // I2C bus with pull-up
    wire scl, sda;
    pullup(sda);  // Simulate pull-up resistor

    // Instantiate master
    i2c_master #(.CLK_DIV(20)) master (
        .clk(clk), .rst_n(rst_n),
        .start(m_start), .slave_addr(m_addr), .rw_bit(m_rw),
        .wr_data(m_wr_data), .rd_data(m_rd_data),
        .ack(m_ack), .busy(m_busy),
        .scl(scl), .sda(sda)
    );

    // Instantiate slave
    i2c_slave #(.SLAVE_ADDR(7'h50)) slave (
        .clk(clk), .rst_n(rst_n),
        .tx_data(s_tx_data), .rx_data(s_rx_data), .rx_valid(s_rx_valid),
        .scl(scl), .sda(sda)
    );

    // Clock generation: 10ns period = 100 MHz
    initial clk = 0;
    always #5 clk = ~clk;

    integer errors = 0;

    //==========================================================================
    // Task: Write byte to slave
    //==========================================================================
    task i2c_write(input [7:0] data);
        begin
            @(posedge clk);
            m_addr = 7'h50;
            m_rw = 1'b0;  // Write
            m_wr_data = data;
            m_start = 1'b1;
            @(posedge clk);
            m_start = 1'b0;

            // Wait for transaction to complete
            wait(!m_busy);
            #100;

            // Check results
            if (m_ack && s_rx_data == data) begin
                $display("✓ Write 0x%02h: PASS (ACK=%b, Slave RX=0x%02h)",
                         data, m_ack, s_rx_data);
            end else begin
                $display("✗ Write 0x%02h: FAIL (ACK=%b, Slave RX=0x%02h, Expected=0x%02h)",
                         data, m_ack, s_rx_data, data);
                errors = errors + 1;
            end
        end
    endtask

    //==========================================================================
    // Task: Read byte from slave
    //==========================================================================
    task i2c_read(input [7:0] expected_data);
        begin
            @(posedge clk);
            s_tx_data = expected_data;  // Load data into slave before read
            m_addr = 7'h50;
            m_rw = 1'b1;  // Read
            m_start = 1'b1;
            @(posedge clk);
            m_start = 1'b0;

            // Wait for transaction to complete
            wait(!m_busy);
            #100;

            // Check results
            if (m_ack && m_rd_data == expected_data) begin
                $display("✓ Read 0x%02h: PASS (ACK=%b, Master RX=0x%02h)",
                         expected_data, m_ack, m_rd_data);
            end else begin
                $display("✗ Read 0x%02h: FAIL (ACK=%b, Master RX=0x%02h, Expected=0x%02h)",
                         expected_data, m_ack, m_rd_data, expected_data);
                errors = errors + 1;
            end
        end
    endtask

    //==========================================================================
    // Main Test Sequence
    //==========================================================================
    initial begin
        $dumpfile("i2c_simple.vcd");
        $dumpvars(0, i2c_tb);

        $display("\n========================================");
        $display("  I2C Master/Slave Testbench");
        $display("  Slave Address: 0x%02h", 7'h50);
        $display("========================================\n");

        // Initialize
        rst_n = 0;
        m_start = 0;
        s_tx_data = 0;

        // Reset
        #100 rst_n = 1;
        #200;

        // Test 1: Write operations
        $display("Test 1: Write Operations");
        i2c_write(8'hA5);
        i2c_write(8'h5A);
        i2c_write(8'hFF);
        i2c_write(8'h00);

        #500;

        // Test 2: Read operations
        $display("\nTest 2: Read Operations");
        i2c_read(8'h12);
        i2c_read(8'h34);
        i2c_read(8'hAB);
        i2c_read(8'hCD);

        #1000;

        // Summary
        $display("\n========================================");
        $display("  Test Summary");
        $display("========================================");
        if (errors == 0) begin
            $display("  Total Tests: 8");
            $display("  Passed: 8");
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
    initial #10_000_000 begin
        $display("\nERROR: Simulation timeout!");
        $finish;
    end

endmodule
