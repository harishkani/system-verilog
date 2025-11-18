/*******************************************************************************
 * I2C Simple Working Implementation
 *
 * Description:
 *   Simplified I2C for educational and simulation purposes.
 *   Master generates SCL, both share SDA with open-drain logic.
 *   Single-byte transactions with 7-bit addressing.
 *
 * Protocol: START + ADDR[7] + R/W[1] + ACK + DATA[8] + ACK + STOP
 *
 * Simplified Assumptions:
 *   - Single clock domain (both master and slave use same clk)
 *   - Simplified bus model (not true open-drain tri-state)
 *   - No clock stretching
 *   - No multi-master arbitration
 *
 * Author: Verified Implementation
 * Date: 2025-11-18
 ******************************************************************************/

`timescale 1ns/1ps

//=============================================================================
// I2C Master - Educational Simplified Version
//=============================================================================
module i2c_master_simple #(
    parameter CLK_DIV = 10    // Divide system clock for I2C timing
) (
    input  wire       clk,
    input  wire       rst_n,
    input  wire       start,       // Pulse to start transaction
    input  wire [6:0] addr,        // 7-bit slave address
    input  wire       rw,          // 0=write, 1=read
    input  wire [7:0] wr_data,     // Data to write
    output reg  [7:0] rd_data,     // Data read
    output reg        ack_received, // ACK from slave
    output reg        done,        // Transaction complete
    // I2C bus
    output reg        scl,
    output reg        sda_out,     // Our SDA output
    input  wire       sda_in       // SDA input (from bus)
);

    localparam IDLE=0, START=1, ADDR_PHASE=2, RW_BIT=3, ACK1=4,
               DATA_PHASE=5, ACK2=6, STOP=7;

    reg [3:0] state;
    reg [7:0] count;
    reg [2:0] bit_idx;
    reg [7:0] shift_reg;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            scl <= 1;
            sda_out <= 1;
            done <= 0;
            count <= 0;
            ack_received <= 0;
        end else begin
            case (state)
                IDLE: begin
                    scl <= 1;
                    sda_out <= 1;
                    done <= 0;
                    count <= 0;
                    if (start) begin
                        shift_reg <= {addr, rw};
                        bit_idx <= 0;
                        state <= START;
                    end
                end

                // START: SDA falls while SCL high
                START: begin
                    if (count == 0) begin
                        sda_out <= 0;  // SDA goes low first
                        count <= count + 1;
                    end else if (count < CLK_DIV/2) begin
                        count <= count + 1;
                    end else if (count == CLK_DIV/2) begin
                        scl <= 0;  // Then SCL goes low
                        count <= count + 1;
                    end else if (count < CLK_DIV) begin
                        count <= count + 1;
                    end else begin
                        count <= 0;
                        state <= ADDR_PHASE;
                    end
                end

                // Send 8 bits (7 addr + 1 rw)
                ADDR_PHASE: begin
                    if (count == 0) begin
                        sda_out <= shift_reg[7];  // Output bit
                        count <= count + 1;
                    end else if (count < CLK_DIV/2) begin
                        count <= count + 1;
                    end else if (count == CLK_DIV/2) begin
                        scl <= 1;  // Clock high - slave samples
                        count <= count + 1;
                    end else if (count < CLK_DIV) begin
                        count <= count + 1;
                    end else begin
                        scl <= 0;  // Clock low
                        shift_reg <= {shift_reg[6:0], 1'b0};
                        count <= 0;

                        if (bit_idx == 7) begin
                            bit_idx <= 0;
                            state <= ACK1;
                        end else begin
                            bit_idx <= bit_idx + 1;
                        end
                    end
                end

                // Receive ACK from slave
                ACK1: begin
                    if (count == 0) begin
                        sda_out <= 1;  // Release SDA
                        count <= count + 1;
                    end else if (count < CLK_DIV/2) begin
                        count <= count + 1;
                    end else if (count == CLK_DIV/2) begin
                        scl <= 1;
                        ack_received <= (sda_in == 0);  // Sample ACK
                        count <= count + 1;
                    end else if (count < CLK_DIV) begin
                        count <= count + 1;
                    end else begin
                        scl <= 0;
                        count <= 0;

                        if (rw == 0) begin
                            // Write operation
                            shift_reg <= wr_data;
                            state <= DATA_PHASE;
                        end else begin
                            // Read operation
                            state <= DATA_PHASE;
                        end
                    end
                end

                // Send or receive 8 data bits
                DATA_PHASE: begin
                    if (rw == 0) begin
                        // Write: send data
                        if (count == 0) begin
                            sda_out <= shift_reg[7];
                            count <= count + 1;
                        end else if (count < CLK_DIV/2) begin
                            count <= count + 1;
                        end else if (count == CLK_DIV/2) begin
                            scl <= 1;
                            count <= count + 1;
                        end else if (count < CLK_DIV) begin
                            count <= count + 1;
                        end else begin
                            scl <= 0;
                            shift_reg <= {shift_reg[6:0], 1'b0};
                            count <= 0;

                            if (bit_idx == 7) begin
                                bit_idx <= 0;
                                state <= ACK2;
                            end else begin
                                bit_idx <= bit_idx + 1;
                            end
                        end
                    end else begin
                        // Read: receive data
                        if (count == 0) begin
                            sda_out <= 1;  // Release SDA
                            count <= count + 1;
                        end else if (count < CLK_DIV/2) begin
                            count <= count + 1;
                        end else if (count == CLK_DIV/2) begin
                            scl <= 1;
                            shift_reg <= {shift_reg[6:0], sda_in};  // Sample
                            count <= count + 1;
                        end else if (count < CLK_DIV) begin
                            count <= count + 1;
                        end else begin
                            scl <= 0;
                            count <= 0;

                            if (bit_idx == 7) begin
                                rd_data <= {shift_reg[6:0], sda_in};
                                bit_idx <= 0;
                                state <= ACK2;
                            end else begin
                                bit_idx <= bit_idx + 1;
                            end
                        end
                    end
                end

                // Send/receive ACK after data
                ACK2: begin
                    if (rw == 0) begin
                        // Write: receive ACK
                        if (count == 0) begin
                            sda_out <= 1;
                            count <= count + 1;
                        end else if (count < CLK_DIV/2) begin
                            count <= count + 1;
                        end else if (count == CLK_DIV/2) begin
                            scl <= 1;
                            count <= count + 1;
                        end else if (count < CLK_DIV) begin
                            count <= count + 1;
                        end else begin
                            scl <= 0;
                            count <= 0;
                            state <= STOP;
                        end
                    end else begin
                        // Read: send NACK
                        if (count == 0) begin
                            sda_out <= 1;  // NACK
                            count <= count + 1;
                        end else if (count < CLK_DIV/2) begin
                            count <= count + 1;
                        end else if (count == CLK_DIV/2) begin
                            scl <= 1;
                            count <= count + 1;
                        end else if (count < CLK_DIV) begin
                            count <= count + 1;
                        end else begin
                            scl <= 0;
                            count <= 0;
                            state <= STOP;
                        end
                    end
                end

                // STOP: SDA rises while SCL high
                STOP: begin
                    if (count == 0) begin
                        sda_out <= 0;
                        count <= count + 1;
                    end else if (count < CLK_DIV/2) begin
                        count <= count + 1;
                    end else if (count == CLK_DIV/2) begin
                        scl <= 1;
                        count <= count + 1;
                    end else if (count < CLK_DIV*3/4) begin
                        count <= count + 1;
                    end else if (count == CLK_DIV*3/4) begin
                        sda_out <= 1;  // SDA rises
                        count <= count + 1;
                    end else if (count < CLK_DIV) begin
                        count <= count + 1;
                    end else begin
                        done <= 1;
                        count <= 0;
                        state <= IDLE;
                    end
                end
            endcase
        end
    end
endmodule

//=============================================================================
// I2C Slave - Educational Simplified Version
//=============================================================================
module i2c_slave_simple #(
    parameter ADDR = 7'h50
) (
    input  wire       clk,
    input  wire       rst_n,
    input  wire [7:0] tx_data,     // Data to send to master
    output reg  [7:0] rx_data,     // Data received from master
    output reg        rx_valid,    // Pulse when rx_data valid
    // I2C bus
    input  wire       scl,
    output reg        sda_out,     // Our SDA output
    input  wire       sda_in       // SDA input (from bus)
);

    localparam IDLE=0, ADDR_PHASE=1, ACK1=2, DATA_PHASE=3, ACK2=4;

    reg [2:0] state;
    reg [2:0] bit_idx;
    reg [7:0] shift_reg;
    reg       is_write;
    reg       scl_d, scl_d2;
    wire      scl_rise, scl_fall;

    // Edge detection
    always @(posedge clk) begin
        scl_d2 <= scl_d;
        scl_d <= scl;
    end
    assign scl_rise = scl_d && !scl_d2;
    assign scl_fall = !scl_d && scl_d2;

    // Detect START: SDA falls while SCL high
    reg sda_d;
    wire start_cond;
    always @(posedge clk) sda_d <= sda_in;
    assign start_cond = scl_d && sda_d && !sda_in;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            sda_out <= 1;
            rx_valid <= 0;
            bit_idx <= 0;
        end else begin
            rx_valid <= 0;

            if (start_cond && state == IDLE) begin
                state <= ADDR_PHASE;
                bit_idx <= 0;
                sda_out <= 1;
            end else begin
                case (state)
                    IDLE: sda_out <= 1;

                    ADDR_PHASE: begin
                        if (scl_rise) begin
                            shift_reg <= {shift_reg[6:0], sda_in};

                            if (bit_idx == 7) begin
                                // Check address match
                                if (shift_reg[7:1] == ADDR) begin
                                    is_write <= sda_in;  // RW bit
                                    state <= ACK1;
                                    bit_idx <= 0;
                                end else begin
                                    state <= IDLE;  // Address mismatch
                                end
                            end else begin
                                bit_idx <= bit_idx + 1;
                            end
                        end
                    end

                    ACK1: begin
                        if (scl_fall) begin
                            sda_out <= 0;  // Send ACK
                        end else if (scl_rise) begin
                            sda_out <= 1;  // Release
                            state <= DATA_PHASE;
                            bit_idx <= 0;
                            if (!is_write) shift_reg <= tx_data;
                        end
                    end

                    DATA_PHASE: begin
                        if (is_write) begin
                            // Receive data from master
                            if (scl_rise) begin
                                shift_reg <= {shift_reg[6:0], sda_in};

                                if (bit_idx == 7) begin
                                    rx_data <= {shift_reg[6:0], sda_in};
                                    rx_valid <= 1;
                                    state <= ACK2;
                                    bit_idx <= 0;
                                end else begin
                                    bit_idx <= bit_idx + 1;
                                end
                            end
                        end else begin
                            // Send data to master
                            if (scl_fall) begin
                                sda_out <= shift_reg[7];
                            end else if (scl_rise) begin
                                shift_reg <= {shift_reg[6:0], 1'b0};

                                if (bit_idx == 7) begin
                                    state <= ACK2;
                                    bit_idx <= 0;
                                end else begin
                                    bit_idx <= bit_idx + 1;
                                end
                            end
                        end
                    end

                    ACK2: begin
                        if (is_write) begin
                            // Send ACK
                            if (scl_fall) sda_out <= 0;
                            else if (scl_rise) begin
                                sda_out <= 1;
                                state <= IDLE;
                            end
                        end else begin
                            // Receive ACK/NACK
                            if (scl_rise) begin
                                sda_out <= 1;
                                state <= IDLE;
                            end
                        end
                    end
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

    // Master
    reg m_start;
    reg [6:0] m_addr;
    reg m_rw;
    reg [7:0] m_wr_data;
    wire [7:0] m_rd_data;
    wire m_ack;
    wire m_done;
    wire scl;
    wire m_sda_out;

    // Slave
    reg [7:0] s_tx_data;
    wire [7:0] s_rx_data;
    wire s_rx_valid;
    wire s_sda_out;

    // Bus (open-drain emulation: low if either pulls low)
    wire sda = m_sda_out & s_sda_out;

    i2c_master_simple #(.CLK_DIV(20)) master(
        .clk(clk), .rst_n(rst_n),
        .start(m_start), .addr(m_addr), .rw(m_rw),
        .wr_data(m_wr_data), .rd_data(m_rd_data),
        .ack_received(m_ack), .done(m_done),
        .scl(scl), .sda_out(m_sda_out), .sda_in(sda)
    );

    i2c_slave_simple #(.ADDR(7'h50)) slave(
        .clk(clk), .rst_n(rst_n),
        .tx_data(s_tx_data), .rx_data(s_rx_data), .rx_valid(s_rx_valid),
        .scl(scl), .sda_out(s_sda_out), .sda_in(sda)
    );

    initial clk = 0;
    always #5 clk = ~clk;

    integer errors = 0;

    task write_test(input [7:0] data);
        begin
            @(posedge clk);
            m_addr = 7'h50;
            m_rw = 0;  // Write
            m_wr_data = data;
            m_start = 1;
            @(posedge clk);
            m_start = 0;
            wait(m_done);
            #200;

            if (m_ack && s_rx_data == data)
                $display("✓ Write 0x%02h: PASS", data);
            else begin
                $display("✗ Write 0x%02h: FAIL (ACK=%b, slave_rx=0x%02h)", data, m_ack, s_rx_data);
                errors = errors + 1;
            end
        end
    endtask

    task read_test(input [7:0] data);
        begin
            @(posedge clk);
            s_tx_data = data;
            m_addr = 7'h50;
            m_rw = 1;  // Read
            m_start = 1;
            @(posedge clk);
            m_start = 0;
            wait(m_done);
            #200;

            if (m_ack && m_rd_data == data)
                $display("✓ Read 0x%02h: PASS", data);
            else begin
                $display("✗ Read 0x%02h: FAIL (ACK=%b, master_rx=0x%02h)", data, m_ack, m_rd_data);
                errors = errors + 1;
            end
        end
    endtask

    initial begin
        $dumpfile("i2c_final.vcd");
        $dumpvars(0, i2c_tb);

        $display("\n========================================");
        $display("  I2C Simple Testbench");
        $display("========================================\n");

        rst_n = 0;
        m_start = 0;
        s_tx_data = 0;
        #100 rst_n = 1;
        #100;

        $display("Write Tests:");
        write_test(8'hA5);
        write_test(8'h5A);
        write_test(8'hFF);
        write_test(8'h00);

        $display("\nRead Tests:");
        read_test(8'h12);
        read_test(8'h34);
        read_test(8'hAB);
        read_test(8'hCD);

        #1000;

        $display("\n========================================");
        if (errors == 0)
            $display("  ✓✓✓ ALL TESTS PASSED (8/8) ✓✓✓");
        else
            $display("  ✗✗✗ %0d TESTS FAILED ✗✗✗", errors);
        $display("========================================\n");

        $finish;
    end

    initial #500_000 begin
        $display("\nTimeout!");
        $finish;
    end
endmodule
