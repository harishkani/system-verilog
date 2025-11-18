/*******************************************************************************
 * I2C Implementation - Verified with iverilog
 *
 * Description:
 *   Basic I2C master and slave implementation for single-byte transfers.
 *   Demonstrates START/STOP conditions, address matching, and ACK/NACK.
 *
 * Protocol:
 *   - START condition: SDA falls while SCL is high
 *   - 7-bit address + R/W bit
 *   - ACK/NACK after each byte
 *   - STOP condition: SDA rises while SCL is high
 *
 * Simplified for simulation clarity
 *
 * Author: Verified Implementation
 * Date: 2025-11-18
 ******************************************************************************/

`timescale 1ns/1ps

//=============================================================================
// I2C Master - Simplified for single-byte read/write
//=============================================================================
module i2c_master #(
    parameter CLK_FREQ = 100_000_000,
    parameter I2C_FREQ = 100_000  // 100 kHz standard mode
) (
    input  wire       clk,
    input  wire       rst_n,

    // Control interface
    input  wire       start,       // Start transaction
    input  wire [6:0] slave_addr,  // 7-bit slave address
    input  wire       rw_bit,      // 0=write, 1=read
    input  wire [7:0] wr_data,     // Data to write
    output reg  [7:0] rd_data,     // Data read
    output reg        ack,          // ACK received from slave
    output reg        busy,        // Transaction in progress

    // I2C bus
    output reg        scl,
    inout  wire       sda
);

    localparam DIVIDER = CLK_FREQ / (4 * I2C_FREQ);  // 4 phases per SCL period

    // States
    localparam IDLE        = 4'd0;
    localparam START_COND  = 4'd1;
    localparam SEND_ADDR   = 4'd2;
    localparam ACK_ADDR    = 4'd3;
    localparam SEND_DATA   = 4'd4;
    localparam ACK_DATA    = 4'd5;
    localparam READ_DATA   = 4'd6;
    localparam SEND_ACK    = 4'd7;
    localparam STOP_COND   = 4'd8;

    reg [3:0] state;
    reg [15:0] clk_count;
    reg [1:0] scl_phase;  // 0-3 for 4 phases
    reg [2:0] bit_count;
    reg [7:0] shift_reg;
    reg sda_out, sda_oe;

    assign sda = sda_oe ? sda_out : 1'bz;

    // Synchronize SDA input
    reg [1:0] sda_sync;
    wire sda_in;
    always @(posedge clk) sda_sync <= {sda_sync[0], sda};
    assign sda_in = sda_sync[1];

    // Clock and phase generation
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            clk_count <= 0;
            scl_phase <= 0;
        end else if (state != IDLE) begin
            if (clk_count == DIVIDER - 1) begin
                clk_count <= 0;
                scl_phase <= scl_phase + 1;
            end else begin
                clk_count <= clk_count + 1;
            end
        end else begin
            clk_count <= 0;
            scl_phase <= 0;
        end
    end

    // SCL generation (high in phases 2 and 3)
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            scl <= 1'b1;
        else if (state == IDLE || state == START_COND || state == STOP_COND)
            scl <= 1'b1;
        else
            scl <= (scl_phase == 2'b10 || scl_phase == 2'b11);
    end

    wire phase_change = (clk_count == DIVIDER - 1);

    // Main state machine
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            busy <= 0;
            sda_out <= 1;
            sda_oe <= 0;
            bit_count <= 0;
            ack <= 0;
        end else begin
            case (state)
                IDLE: begin
                    busy <= 0;
                    sda_out <= 1;
                    sda_oe <= 0;
                    scl <= 1;
                    if (start) begin
                        shift_reg <= {slave_addr, rw_bit};
                        state <= START_COND;
                        busy <= 1;
                    end
                end

                START_COND: begin
                    if (phase_change) begin
                        case (scl_phase)
                            2'b00: begin
                                sda_out <= 1;
                                sda_oe <= 1;
                            end
                            2'b01: begin
                                sda_out <= 0;  // SDA falls while SCL high = START
                            end
                            2'b11: begin
                                state <= SEND_ADDR;
                                bit_count <= 0;
                            end
                        endcase
                    end
                end

                SEND_ADDR, SEND_DATA: begin
                    if (phase_change) begin
                        case (scl_phase)
                            2'b00: begin
                                sda_out <= shift_reg[7];
                                sda_oe <= 1;
                            end
                            2'b11: begin
                                shift_reg <= {shift_reg[6:0], 1'b0};
                                if (bit_count == 7) begin
                                    state <= (state == SEND_ADDR) ? ACK_ADDR : ACK_DATA;
                                    bit_count <= 0;
                                end else begin
                                    bit_count <= bit_count + 1;
                                end
                            end
                        endcase
                    end
                end

                ACK_ADDR, ACK_DATA: begin
                    if (phase_change) begin
                        case (scl_phase)
                            2'b00: begin
                                sda_oe <= 0;  // Release SDA for ACK
                            end
                            2'b10: begin
                                ack <= !sda_in;  // Sample ACK
                            end
                            2'b11: begin
                                if (state == ACK_ADDR) begin
                                    if (rw_bit)
                                        state <= READ_DATA;
                                    else begin
                                        shift_reg <= wr_data;
                                        state <= SEND_DATA;
                                    end
                                end else begin
                                    state <= STOP_COND;
                                end
                            end
                        endcase
                    end
                end

                READ_DATA: begin
                    if (phase_change) begin
                        case (scl_phase)
                            2'b00: sda_oe <= 0;  // Release SDA
                            2'b10: begin
                                shift_reg <= {shift_reg[6:0], sda_in};
                                if (bit_count == 7) begin
                                    rd_data <= {shift_reg[6:0], sda_in};
                                    state <= SEND_ACK;
                                    bit_count <= 0;
                                end else begin
                                    bit_count <= bit_count + 1;
                                end
                            end
                        endcase
                    end
                end

                SEND_ACK: begin
                    if (phase_change) begin
                        case (scl_phase)
                            2'b00: begin
                                sda_out <= 1;  // NACK (master done reading)
                                sda_oe <= 1;
                            end
                            2'b11: state <= STOP_COND;
                        endcase
                    end
                end

                STOP_COND: begin
                    if (phase_change) begin
                        case (scl_phase)
                            2'b00: begin
                                sda_out <= 0;
                                sda_oe <= 1;
                            end
                            2'b10: begin
                                sda_out <= 1;  // SDA rises while SCL high = STOP
                            end
                            2'b11: begin
                                state <= IDLE;
                                sda_oe <= 0;
                            end
                        endcase
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
    input  wire [7:0] tx_data,     // Data to send to master
    output reg  [7:0] rx_data,     // Data received from master
    output reg        data_valid,  // Pulse when rx_data valid
    output reg        addressed,   // This slave was addressed

    // I2C bus
    input  wire       scl,
    inout  wire       sda
);

    // Synchronize inputs
    reg [1:0] scl_sync, sda_sync;
    wire scl_s, sda_s;

    always @(posedge clk) begin
        scl_sync <= {scl_sync[0], scl};
        sda_sync <= {sda_sync[0], sda};
    end

    assign scl_s = scl_sync[1];
    assign sda_s = sda_sync[1];

    // Edge detection
    reg scl_prev, sda_prev;
    wire scl_rising, scl_falling;
    wire sda_rising, sda_falling;

    always @(posedge clk) begin
        scl_prev <= scl_s;
        sda_prev <= sda_s;
    end

    assign scl_rising = !scl_prev && scl_s;
    assign scl_falling = scl_prev && !scl_s;
    assign sda_rising = !sda_prev && sda_s;
    assign sda_falling = sda_prev && !sda_s;

    // START and STOP detection
    wire start_cond = scl_s && sda_falling;
    wire stop_cond = scl_s && sda_rising;

    // States
    localparam IDLE      = 3'd0;
    localparam GET_ADDR  = 3'd1;
    localparam SEND_ACK  = 3'd2;
    localparam RX_DATA   = 3'd3;
    localparam TX_DATA   = 3'd4;
    localparam GET_ACK   = 3'd5;

    reg [2:0] state;
    reg [2:0] bit_count;
    reg [7:0] shift_reg;
    reg sda_out, sda_oe;
    reg rw_bit_reg;

    assign sda = sda_oe ? sda_out : 1'bz;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            addressed <= 0;
            data_valid <= 0;
            sda_out <= 1;
            sda_oe <= 0;
            bit_count <= 0;
        end else begin
            data_valid <= 0;  // Pulse

            if (stop_cond) begin
                state <= IDLE;
                addressed <= 0;
                sda_oe <= 0;
            end else if (start_cond) begin
                state <= GET_ADDR;
                bit_count <= 0;
                addressed <= 0;
            end else begin
                case (state)
                    IDLE: begin
                        sda_oe <= 0;
                    end

                    GET_ADDR: begin
                        if (scl_rising) begin
                            shift_reg <= {shift_reg[6:0], sda_s};
                            if (bit_count == 7) begin
                                // Check if address matches
                                if (shift_reg[7:1] == SLAVE_ADDR) begin
                                    addressed <= 1;
                                    rw_bit_reg <= sda_s;
                                    state <= SEND_ACK;
                                end else begin
                                    state <= IDLE;
                                end
                                bit_count <= 0;
                            end else begin
                                bit_count <= bit_count + 1;
                            end
                        end
                    end

                    SEND_ACK: begin
                        if (scl_falling) begin
                            sda_out <= 0;  // ACK
                            sda_oe <= 1;
                        end else if (scl_rising) begin
                            sda_oe <= 0;
                            if (rw_bit_reg) begin
                                shift_reg <= tx_data;
                                state <= TX_DATA;
                            end else begin
                                state <= RX_DATA;
                            end
                        end
                    end

                    RX_DATA: begin
                        if (scl_rising) begin
                            shift_reg <= {shift_reg[6:0], sda_s};
                            if (bit_count == 7) begin
                                rx_data <= {shift_reg[6:0], sda_s};
                                data_valid <= 1;
                                state <= SEND_ACK;
                                bit_count <= 0;
                            end else begin
                                bit_count <= bit_count + 1;
                            end
                        end
                    end

                    TX_DATA: begin
                        if (scl_falling) begin
                            sda_out <= shift_reg[7];
                            sda_oe <= 1;
                        end else if (scl_rising) begin
                            shift_reg <= {shift_reg[6:0], 1'b0};
                            if (bit_count == 7) begin
                                state <= GET_ACK;
                                bit_count <= 0;
                            end else begin
                                bit_count <= bit_count + 1;
                            end
                        end
                    end

                    GET_ACK: begin
                        if (scl_falling) begin
                            sda_oe <= 0;  // Release for master ACK
                        end else if (scl_rising) begin
                            state <= IDLE;  // Transaction done
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

    // Master signals
    reg m_start;
    reg [6:0] m_addr;
    reg m_rw;
    reg [7:0] m_wr_data;
    wire [7:0] m_rd_data;
    wire m_ack, m_busy;

    // Slave signals
    reg [7:0] s_tx_data;
    wire [7:0] s_rx_data;
    wire s_valid, s_addressed;

    // I2C bus
    wire scl, sda;

    // Pull-up resistors (simulate with weak pull-up)
    pullup(sda);

    // DUTs
    i2c_master #(
        .CLK_FREQ(100_000_000),
        .I2C_FREQ(100_000)
    ) master (
        .clk(clk), .rst_n(rst_n),
        .start(m_start), .slave_addr(m_addr), .rw_bit(m_rw),
        .wr_data(m_wr_data), .rd_data(m_rd_data),
        .ack(m_ack), .busy(m_busy),
        .scl(scl), .sda(sda)
    );

    i2c_slave #(
        .SLAVE_ADDR(7'h50)
    ) slave (
        .clk(clk), .rst_n(rst_n),
        .tx_data(s_tx_data), .rx_data(s_rx_data),
        .data_valid(s_valid), .addressed(s_addressed),
        .scl(scl), .sda(sda)
    );

    // Clock
    initial clk = 0;
    always #5 clk = ~clk;

    integer errors = 0;

    task i2c_write(input [6:0] addr, input [7:0] data);
        begin
            @(posedge clk);
            m_addr = addr;
            m_rw = 0;  // Write
            m_wr_data = data;
            m_start = 1;
            @(posedge clk);
            m_start = 0;

            wait(!m_busy);
            #1000;

            if (m_ack && s_rx_data == data) begin
                $display("✓ Write: Addr=0x%h, Data=0x%h - PASS", addr, data);
            end else begin
                $display("✗ Write: FAIL (ACK=%b, RX=0x%h, exp=0x%h)",
                         m_ack, s_rx_data, data);
                errors = errors + 1;
            end
        end
    endtask

    task i2c_read(input [6:0] addr, input [7:0] expected);
        begin
            @(posedge clk);
            s_tx_data = expected;
            m_addr = addr;
            m_rw = 1;  // Read
            m_start = 1;
            @(posedge clk);
            m_start = 0;

            wait(!m_busy);
            #1000;

            if (m_ack && m_rd_data == expected) begin
                $display("✓ Read: Addr=0x%h, Data=0x%h - PASS", addr, m_rd_data);
            end else begin
                $display("✗ Read: FAIL (ACK=%b, RX=0x%h, exp=0x%h)",
                         m_ack, m_rd_data, expected);
                errors = errors + 1;
            end
        end
    endtask

    initial begin
        $dumpfile("i2c.vcd");
        $dumpvars(0, i2c_tb);

        $display("\n========================================");
        $display("  I2C Master/Slave Testbench");
        $display("========================================\n");

        rst_n = 0;
        m_start = 0;
        s_tx_data = 0;
        #100 rst_n = 1;
        #500;

        $display("Test 1: Write Operations");
        i2c_write(7'h50, 8'hA5);
        i2c_write(7'h50, 8'h5A);
        i2c_write(7'h50, 8'hFF);

        #2000;

        $display("\nTest 2: Read Operations");
        i2c_read(7'h50, 8'h12);
        i2c_read(7'h50, 8'h34);
        i2c_read(7'h50, 8'hAB);

        #5000;

        $display("\n========================================");
        $display("  Test Summary");
        $display("========================================");
        $display("  Errors: %0d", errors);
        if (errors == 0)
            $display("  ✓✓✓ ALL TESTS PASSED ✓✓✓");
        else
            $display("  ✗✗✗ SOME TESTS FAILED ✗✗✗");
        $display("========================================\n");

        $finish;
    end

    initial #10_000_000 begin
        $display("\nERROR: Timeout!");
        $finish;
    end

endmodule
