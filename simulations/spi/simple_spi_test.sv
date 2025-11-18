// Ultra-simple SPI test - Mode 0 only for initial verification

`timescale 1ns/1ps

module simple_spi_master #(parameter WIDTH=8) (
    input clk, rst_n,
    input [WIDTH-1:0] data_in,
    input start,
    output reg [WIDTH-1:0] data_out,
    output reg done,
    output reg sclk, mosi, cs_n,
    input miso
);
    reg [WIDTH-1:0] tx_reg, rx_reg;
    reg [3:0] bit_cnt;
    reg [2:0] clk_cnt;
    reg [1:0] state;
    
    localparam IDLE=0, ACTIVE=1, FINISH=2;
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            sclk <= 0;
            cs_n <= 1;
            done <= 0;
            bit_cnt <= 0;
            clk_cnt <= 0;
        end else begin
            done <= 0;
            case (state)
                IDLE: begin
                    cs_n <= 1;
                    sclk <= 0;
                    if (start) begin
                        tx_reg <= data_in;
                        bit_cnt <= 0;
                        clk_cnt <= 0;
                        cs_n <= 0;
                        state <= ACTIVE;
                    end
                end
                
                ACTIVE: begin
                    clk_cnt <= clk_cnt + 1;
                    if (clk_cnt == 3) begin  // Clock divider
                        clk_cnt <= 0;
                        if (!sclk) begin
                            // Rising edge - sample MISO
                            sclk <= 1;
                            rx_reg <= {rx_reg[WIDTH-2:0], miso};
                        end else begin
                            // Falling edge - change MOSI
                            sclk <= 0;
                            tx_reg <= {tx_reg[WIDTH-2:0], 1'b0};
                            bit_cnt <= bit_cnt + 1;
                            if (bit_cnt == WIDTH-1) begin
                                state <= FINISH;
                            end
                        end
                    end
                end
                
                FINISH: begin
                    cs_n <= 1;
                    data_out <= rx_reg;
                    done <= 1;
                    state <= IDLE;
                end
            endcase
        end
    end
    
    assign mosi = tx_reg[WIDTH-1];
endmodule

module simple_spi_slave #(parameter WIDTH=8) (
    input clk, rst_n,
    input [WIDTH-1:0] data_in,
    output reg [WIDTH-1:0] data_out,
    output reg done,
    input sclk, mosi, cs_n,
    output miso
);
    reg [WIDTH-1:0] tx_reg, rx_reg;
    reg [3:0] bit_cnt;
    reg sclk_prev, cs_prev;
    
    wire sclk_rise = !sclk_prev && sclk;
    wire sclk_fall = sclk_prev && !sclk;
    wire cs_fall = cs_prev && !cs_n;
    wire cs_rise = !cs_prev && cs_n;
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sclk_prev <= 0;
            cs_prev <= 1;
            bit_cnt <= 0;
            done <= 0;
        end else begin
            sclk_prev <= sclk;
            cs_prev <= cs_n;
            done <= 0;
            
            if (cs_fall) begin
                // Start of transaction
                tx_reg <= data_in;
                bit_cnt <= 0;
            end else if (!cs_n) begin
                // Active transaction
                if (sclk_rise) begin
                    // Sample MOSI on rising edge (Mode 0)
                    rx_reg <= {rx_reg[WIDTH-2:0], mosi};
                    bit_cnt <= bit_cnt + 1;
                end else if (sclk_fall) begin
                    // Shift TX on falling edge
                    tx_reg <= {tx_reg[WIDTH-2:0], 1'b0};
                end
            end else if (cs_rise) begin
                // End of transaction
                if (bit_cnt == WIDTH) begin
                    data_out <= rx_reg;
                    done <= 1;
                end
            end
        end
    end
    
    assign miso = cs_n ? 1'bz : tx_reg[WIDTH-1];
endmodule

module simple_spi_tb;
    reg clk, rst_n;
    reg [7:0] m_tx, s_tx;
    wire [7:0] m_rx, s_rx;
    reg m_start;
    wire m_done, s_done;
    wire sclk, mosi, miso, cs_n;
    
    simple_spi_master master (
        .clk(clk), .rst_n(rst_n),
        .data_in(m_tx), .start(m_start), .data_out(m_rx), .done(m_done),
        .sclk(sclk), .mosi(mosi), .cs_n(cs_n), .miso(miso)
    );
    
    simple_spi_slave slave (
        .clk(clk), .rst_n(rst_n),
        .data_in(s_tx), .data_out(s_rx), .done(s_done),
        .sclk(sclk), .mosi(mosi), .cs_n(cs_n), .miso(miso)
    );
    
    initial clk = 0;
    always #5 clk = ~clk;
    
    initial begin
        $dumpfile("simple_spi.vcd");
        $dumpvars(0, simple_spi_tb);
        
        rst_n = 0;
        m_start = 0;
        m_tx = 0;
        s_tx = 0;
        
        #20 rst_n = 1;
        #50;
        
        $display("Test 1: Master sends 0xA5, Slave sends 0x5A");
        m_tx = 8'hA5;
        s_tx = 8'h5A;
        m_start = 1;
        #10 m_start = 0;
        
        wait(m_done);
        #10;
        
        if (m_rx == 8'h5A && s_rx == 8'hA5)
            $display("PASS: Master RX=0x%h, Slave RX=0x%h", m_rx, s_rx);
        else
            $display("FAIL: Master RX=0x%h (exp 0x5A), Slave RX=0x%h (exp 0xA5)", m_rx, s_rx);
        
        #100;
        
        $display("\nTest 2: Master sends 0x3C, Slave sends 0xC3");
        m_tx = 8'h3C;
        s_tx = 8'hC3;
        m_start = 1;
        #10 m_start = 0;
        
        wait(m_done);
        #10;
        
        if (m_rx == 8'hC3 && s_rx == 8'h3C)
            $display("PASS: Master RX=0x%h, Slave RX=0x%h", m_rx, s_rx);
        else
            $display("FAIL: Master RX=0x%h (exp 0xC3), Slave RX=0x%h (exp 0x3C)", m_rx, s_rx);
        
        #100;
        $display("\nSimulation Complete");
        $finish;
    end
    
    initial #10000 $finish;  // Timeout
endmodule
