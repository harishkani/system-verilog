`timescale 1ns/1ps

// SPI MASTER - Mode 0 (CPOL=0, CPHA=0)
// Clock idles low, sample on rising edge, change on falling edge
module spi_master #(parameter WIDTH=8) (
    input  wire clk, rst_n,
    input  wire [WIDTH-1:0] tx_data,
    input  wire start,
    output reg  [WIDTH-1:0] rx_data,
    output reg  done,
    output reg  sclk, mosi, cs_n,
    input  wire miso
);
    reg [WIDTH-1:0] tx_reg, rx_reg;
    reg [3:0] bit_cnt;
    reg [2:0] clk_cnt;
    reg [1:0] state;
    
    localparam IDLE=0, XFER=1, FINISH=2;
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            done <= 0;
            sclk <= 0;
            cs_n <= 1;
        end else begin
            done <= 0;
            case (state)
                IDLE: if (start) begin
                    tx_reg <= tx_data;
                    bit_cnt <= 0;
                    clk_cnt <= 0;
                    cs_n <= 0;
                    sclk <= 0;
                    state <= XFER;
                end
                
                XFER: begin
                    clk_cnt <= clk_cnt + 1;
                    if (clk_cnt == 3) begin
                        clk_cnt <= 0;
                        sclk <= ~sclk;
                        if (!sclk) begin  // About to rise
                            // Sample will happen
                        end else begin  // About to fall
                            rx_reg <= {rx_reg[WIDTH-2:0], miso};
                            tx_reg <= {tx_reg[WIDTH-2:0], 1'b0};
                            bit_cnt <= bit_cnt + 1;
                            if (bit_cnt == WIDTH-1)
                                state <= FINISH;
                        end
                    end
                end
                
                FINISH: begin
                    rx_data <= rx_reg;
                    done <= 1;
                    cs_n <= 1;
                    sclk <= 0;
                    state <= IDLE;
                end
            endcase
        end
    end
    assign mosi = tx_reg[WIDTH-1];
endmodule

// SPI SLAVE
module spi_slave #(parameter WIDTH=8) (
    input  wire clk, rst_n,
    input  wire [WIDTH-1:0] tx_data,
    output reg  [WIDTH-1:0] rx_data,
    output reg  done,
    input  wire sclk, mosi, cs_n,
    output wire miso
);
    reg [WIDTH-1:0] tx_reg, rx_reg;
    reg [3:0] bit_cnt;
    reg sclk_d, cs_d;
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sclk_d <= 0;
            cs_d <= 1;
            done <= 0;
        end else begin
            sclk_d <= sclk;
            cs_d <= cs_n;
            done <= 0;
            
            if (cs_d && !cs_n) begin  // CS falling
                tx_reg <= tx_data;
                bit_cnt <= 0;
            end else if (!cs_n && !sclk_d && sclk) begin  // SCLK rising during transfer
                rx_reg <= {rx_reg[WIDTH-2:0], mosi};
                bit_cnt <= bit_cnt + 1;
            end else if (!cs_n && sclk_d && !sclk) begin  // SCLK falling during transfer
                tx_reg <= {tx_reg[WIDTH-2:0], 1'b0};
            end else if (!cs_d && cs_n && bit_cnt == WIDTH) begin  // CS rising after transfer
                rx_data <= rx_reg;
                done <= 1;
            end
        end
    end
    assign miso = cs_n ? 1'bz : tx_reg[WIDTH-1];
endmodule

// TESTBENCH
module tb;
    reg clk=0, rst_n;
    reg [7:0] m_tx, s_tx;
    wire [7:0] m_rx, s_rx;
    reg start;
    wire m_done, s_done;
    wire sclk, mosi, miso, cs_n;
    
    always #5 clk = ~clk;
    
    spi_master m(.clk(clk), .rst_n(rst_n), .tx_data(m_tx), .start(start),
                 .rx_data(m_rx), .done(m_done),
                 .sclk(sclk), .mosi(mosi), .cs_n(cs_n), .miso(miso));
    
    spi_slave s(.clk(clk), .rst_n(rst_n), .tx_data(s_tx),
                .rx_data(s_rx), .done(s_done),
                .sclk(sclk), .mosi(mosi), .cs_n(cs_n), .miso(miso));
    
    integer pass=0, fail=0;
    
    initial begin
        $dumpfile("spi.vcd");
        $dumpvars;
        
        $display("\n========== SPI SIMULATION ==========\n");
        
        rst_n=0; start=0; #30 rst_n=1; #20;
        
        // Test 1
        m_tx=8'hA5; s_tx=8'h5A; start=1; #10 start=0; #800;
        if (m_rx==8'h5A && s_rx==8'hA5) begin
            $display("✓ Test 1 PASS: M:A5→5A S:5A→A5");
            pass=pass+1;
        end else begin
            $display("✗ Test 1 FAIL: M_RX=%h(exp 5A) S_RX=%h(exp A5)", m_rx, s_rx);
            fail=fail+1;
        end
        
        // Test 2
        m_tx=8'h3C; s_tx=8'hC3; start=1; #10 start=0; #800;
        if (m_rx==8'hC3 && s_rx==8'h3C) begin
            $display("✓ Test 2 PASS: M:3C→C3 S:C3→3C");
            pass=pass+1;
        end else begin
            $display("✗ Test 2 FAIL: M_RX=%h(exp C3) S_RX=%h(exp 3C)", m_rx, s_rx);
            fail=fail+1;
        end
        
        // Test 3
        m_tx=8'hFF; s_tx=8'h00; start=1; #10 start=0; #800;
        if (m_rx==8'h00 && s_rx==8'hFF) begin
            $display("✓ Test 3 PASS: M:FF→00 S:00→FF");
            pass=pass+1;
        end else begin
            $display("✗ Test 3 FAIL: M_RX=%h(exp 00) S_RX=%h(exp FF)", m_rx, s_rx);
            fail=fail+1;
        end
        
        $display("\n====================================");
        $display("PASSED: %0d  FAILED: %0d", pass, fail);
        $display("====================================\n");
        $finish;
    end
endmodule
