/*******************************************************************************
 * Working SPI Implementation - Verified with iverilog
 * Mode 0: CPOL=0, CPHA=0
 * Sample on rising edge, change on falling edge
 ******************************************************************************/

`timescale 1ns/1ps

//=============================================================================
// SPI Master - Fully commented for understanding
//=============================================================================
module spi_master_v2 #(parameter WIDTH=8) (
    input  wire clk,              // System clock (100MHz in testbench)
    input  wire rst_n,            // Active-low reset
    input  wire [WIDTH-1:0] data_in,  // Data to transmit
    input  wire start,            // Start transfer (pulse high for 1 clock)
    output reg  [WIDTH-1:0] data_out, // Received data
    output reg  done,             // Transfer complete (pulses for 1 clock)
    output reg  sclk,             // SPI clock output
    output wire mosi,             // Master Out Slave In
    input  wire miso,             // Master In Slave Out
    output reg  cs_n              // Chip Select (active low)
);

    // Internal registers
    reg [WIDTH-1:0] tx_shift_reg;  // Transmit shift register (shifts left, MSB first)
    reg [WIDTH-1:0] rx_shift_reg;  // Receive shift register (shifts left)
    reg [3:0] bit_counter;         // Counts bits transferred (0 to WIDTH-1)
    reg [2:0] clk_divider;         // Divides system clock for SPI clock
    reg [1:0] state;               // State machine: IDLE, ACTIVE, FINISH
    
    // State definitions
    localparam IDLE   = 2'd0;  // Waiting for start signal
    localparam ACTIVE = 2'd1;  // Transferring data
    localparam FINISH = 2'd2;  // Transfer complete, present results
    
    // Main control logic
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Reset all registers
            state <= IDLE;
            sclk <= 1'b0;           // CPOL=0: clock idles low
            cs_n <= 1'b1;           // CS inactive (high)
            done <= 1'b0;
            bit_counter <= 4'd0;
            clk_divider <= 3'd0;
            tx_shift_reg <= {WIDTH{1'b0}};
            rx_shift_reg <= {WIDTH{1'b0}};
            data_out <= {WIDTH{1'b0}};
        end else begin
            done <= 1'b0;  // Default: done is a single-cycle pulse
            
            case (state)
                //-------------------------------------------------------------
                // IDLE State: Wait for start signal
                //-------------------------------------------------------------
                IDLE: begin
                    cs_n <= 1'b1;              // Keep CS high (inactive)
                    sclk <= 1'b0;              // Keep clock low
                    bit_counter <= 4'd0;       // Reset bit counter
                    clk_divider <= 3'd0;       // Reset clock divider
                    
                    if (start) begin
                        tx_shift_reg <= data_in;  // Load data to transmit
                        cs_n <= 1'b0;              // Assert CS (start transaction)
                        state <= ACTIVE;
                    end
                end
                
                //-------------------------------------------------------------
                // ACTIVE State: Transfer data bits
                //-------------------------------------------------------------
                ACTIVE: begin
                    clk_divider <= clk_divider + 1;
                    
                    // Divide system clock by 8 (toggle sclk every 4 system clocks)
                    if (clk_divider == 3'd3) begin
                        clk_divider <= 3'd0;
                        
                        if (!sclk) begin
                            //--------------------------------------------------
                            // SCLK Rising Edge (0→1)
                            // Action: Sample MISO (Mode 0: sample on rising)
                            //--------------------------------------------------
                            sclk <= 1'b1;
                            rx_shift_reg <= {rx_shift_reg[WIDTH-2:0], miso};
                            
                        end else begin
                            //--------------------------------------------------
                            // SCLK Falling Edge (1→0)
                            // Action: Change MOSI, increment bit counter
                            //--------------------------------------------------
                            sclk <= 1'b0;
                            tx_shift_reg <= {tx_shift_reg[WIDTH-2:0], 1'b0};  // Shift left
                            bit_counter <= bit_counter + 1;
                            
                            // Check if all bits transferred
                            if (bit_counter == (WIDTH - 1)) begin
                                state <= FINISH;
                            end
                        end
                    end
                end
                
                //-------------------------------------------------------------
                // FINISH State: Deassert CS, present results
                //-------------------------------------------------------------
                FINISH: begin
                    cs_n <= 1'b1;              // Deassert CS
                    sclk <= 1'b0;              // Return clock to idle
                    data_out <= rx_shift_reg;  // Present received data
                    done <= 1'b1;              // Signal completion
                    state <= IDLE;             // Return to idle
                end
                
                default: state <= IDLE;
            endcase
        end
    end
    
    // MOSI always shows MSB of shift register
    assign mosi = tx_shift_reg[WIDTH-1];
    
endmodule

//=============================================================================
// SPI Slave - Fully commented for understanding
//=============================================================================
module spi_slave_v2 #(parameter WIDTH=8) (
    input  wire clk,              // System clock
    input  wire rst_n,            // Active-low reset
    input  wire [WIDTH-1:0] data_in,  // Data to send to master
    output reg  [WIDTH-1:0] data_out, // Data received from master
    output reg  done,             // Transfer complete
    input  wire sclk,             // SPI clock from master
    input  wire mosi,             // Master Out Slave In
    input  wire cs_n,             // Chip Select from master
    output wire miso              // Master In Slave Out
);

    // Internal registers
    reg [WIDTH-1:0] tx_shift_reg;  // Transmit shift register
    reg [WIDTH-1:0] rx_shift_reg;  // Receive shift register
    reg [3:0] bit_counter;         // Counts received bits
    reg sclk_prev;                 // Previous SCLK for edge detection
    reg cs_n_prev;                 // Previous CS for edge detection
    
    // Edge detection
    wire sclk_rising  = !sclk_prev && sclk;   // Rising edge: 0→1
    wire sclk_falling = sclk_prev && !sclk;   // Falling edge: 1→0
    wire cs_falling   = cs_n_prev && !cs_n;   // CS asserted
    wire cs_rising    = !cs_n_prev && cs_n;   // CS deasserted
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sclk_prev <= 1'b0;
            cs_n_prev <= 1'b1;
            bit_counter <= 4'd0;
            done <= 1'b0;
            tx_shift_reg <= {WIDTH{1'b0}};
            rx_shift_reg <= {WIDTH{1'b0}};
            data_out <= {WIDTH{1'b0}};
        end else begin
            // Update edge detection registers
            sclk_prev <= sclk;
            cs_n_prev <= cs_n;
            done <= 1'b0;  // Default: done is a pulse
            
            //------------------------------------------------------------------
            // CS Falling Edge: Transaction Start
            //------------------------------------------------------------------
            if (cs_falling) begin
                tx_shift_reg <= data_in;  // Load data to transmit
                bit_counter <= 4'd0;      // Reset bit counter
            end
            
            //------------------------------------------------------------------
            // During Active Transaction (CS is low)
            //------------------------------------------------------------------
            else if (!cs_n) begin
                
                // SCLK Rising Edge: Sample MOSI (Mode 0)
                if (sclk_rising) begin
                    rx_shift_reg <= {rx_shift_reg[WIDTH-2:0], mosi};
                    bit_counter <= bit_counter + 1;
                end
                
                // SCLK Falling Edge: Shift TX register
                else if (sclk_falling) begin
                    tx_shift_reg <= {tx_shift_reg[WIDTH-2:0], 1'b0};
                end
            end
            
            //------------------------------------------------------------------
            // CS Rising Edge: Transaction End
            //------------------------------------------------------------------
            else if (cs_rising) begin
                if (bit_counter == WIDTH) begin
                    data_out <= rx_shift_reg;  // Present received data
                    done <= 1'b1;              // Signal completion
                end
            end
        end
    end
    
    // MISO: Drive MSB when CS active, high-Z when inactive
    assign miso = cs_n ? 1'bz : tx_shift_reg[WIDTH-1];
    
endmodule

//=============================================================================
// Testbench - Tests multiple transfers
//=============================================================================
module spi_testbench;

    // Testbench signals
    reg clk, rst_n;
    reg [7:0] master_tx, slave_tx;
    wire [7:0] master_rx, slave_rx;
    reg master_start;
    wire master_done, slave_done;
    wire sclk, mosi, miso, cs_n;
    
    // Instantiate Master
    spi_master_v2 #(.WIDTH(8)) master (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(master_tx),
        .start(master_start),
        .data_out(master_rx),
        .done(master_done),
        .sclk(sclk),
        .mosi(mosi),
        .miso(miso),
        .cs_n(cs_n)
    );
    
    // Instantiate Slave
    spi_slave_v2 #(.WIDTH(8)) slave (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(slave_tx),
        .data_out(slave_rx),
        .done(slave_done),
        .sclk(sclk),
        .mosi(mosi),
        .cs_n(cs_n),
        .miso(miso)
    );
    
    // Clock generation: 100 MHz (10ns period)
    initial clk = 0;
    always #5 clk = ~clk;
    
    // Test stimulus
    integer pass_count = 0;
    integer fail_count = 0;
    
    initial begin
        $dumpfile("spi_working.vcd");
        $dumpvars(0, spi_testbench);
        
        $display("\n========================================");
        $display(" SPI Master-Slave Test (Mode 0)");
        $display("========================================\n");
        
        // Initialize
        rst_n = 0;
        master_start = 0;
        master_tx = 0;
        slave_tx = 0;
        
        // Release reset
        #20 rst_n = 1;
        #50;
        
        //=====================================================================
        // Test 1: Master sends 0xA5, Slave sends 0x5A
        //=====================================================================
        $display("Test 1: Master TX=0xA5, Slave TX=0x5A");
        master_tx = 8'hA5;
        slave_tx = 8'h5A;
        master_start = 1;
        @(posedge clk) master_start = 0;
        
        wait(master_done);
        #20;
        
        if (master_rx == 8'h5A && slave_rx == 8'hA5) begin
            $display("  ✓ PASS: Master RX=0x%02h, Slave RX=0x%02h\n", master_rx, slave_rx);
            pass_count = pass_count + 1;
        end else begin
            $display("  ✗ FAIL: Master RX=0x%02h (exp 0x5A), Slave RX=0x%02h (exp 0xA5)\n",
                     master_rx, slave_rx);
            fail_count = fail_count + 1;
        end
        
        #100;
        
        //=====================================================================
        // Test 2: Master sends 0x3C, Slave sends 0xC3
        //=====================================================================
        $display("Test 2: Master TX=0x3C, Slave TX=0xC3");
        master_tx = 8'h3C;
        slave_tx = 8'hC3;
        master_start = 1;
        @(posedge clk) master_start = 0;
        
        wait(master_done);
        #20;
        
        if (master_rx == 8'hC3 && slave_rx == 8'h3C) begin
            $display("  ✓ PASS: Master RX=0x%02h, Slave RX=0x%02h\n", master_rx, slave_rx);
            pass_count = pass_count + 1;
        end else begin
            $display("  ✗ FAIL: Master RX=0x%02h (exp 0xC3), Slave RX=0x%02h (exp 0x3C)\n",
                     master_rx, slave_rx);
            fail_count = fail_count + 1;
        end
        
        #100;
        
        //=====================================================================
        // Test 3: Master sends 0xFF, Slave sends 0x00
        //=====================================================================
        $display("Test 3: Master TX=0xFF, Slave TX=0x00");
        master_tx = 8'hFF;
        slave_tx = 8'h00;
        master_start = 1;
        @(posedge clk) master_start = 0;
        
        wait(master_done);
        #20;
        
        if (master_rx == 8'h00 && slave_rx == 8'hFF) begin
            $display("  ✓ PASS: Master RX=0x%02h, Slave RX=0x%02h\n", master_rx, slave_rx);
            pass_count = pass_count + 1;
        end else begin
            $display("  ✗ FAIL: Master RX=0x%02h (exp 0x00), Slave RX=0x%02h (exp 0xFF)\n",
                     master_rx, slave_rx);
            fail_count = fail_count + 1;
        end
        
        #100;
        
        //=====================================================================
        // Test 4-8: Sequential transfers
        //=====================================================================
        $display("Tests 4-8: Sequential transfers");
        for (int i = 0; i < 5; i++) begin
            master_tx = i * 16;
            slave_tx = 255 - (i * 16);
            master_start = 1;
            @(posedge clk) master_start = 0;
            
            wait(master_done);
            #20;
            
            if (master_rx == (255 - i*16) && slave_rx == (i*16)) begin
                $display("  ✓ Test %0d PASS: M_RX=0x%02h, S_RX=0x%02h",
                         i+4, master_rx, slave_rx);
                pass_count = pass_count + 1;
            end else begin
                $display("  ✗ Test %0d FAIL: M_RX=0x%02h (exp 0x%02h), S_RX=0x%02h (exp 0x%02h)",
                         i+4, master_rx, 255-i*16, slave_rx, i*16);
                fail_count = fail_count + 1;
            end
            #50;
        end
        
        #100;
        
        //=====================================================================
        // Summary
        //=====================================================================
        $display("\n========================================");
        $display(" Test Summary");
        $display("========================================");
        $display(" Passed: %0d", pass_count);
        $display(" Failed: %0d", fail_count);
        $display("========================================\n");
        
        $finish;
    end
    
    // Timeout watchdog
    initial #50000 begin
        $display("\nERROR: Simulation timeout!");
        $finish;
    end
    
endmodule
