// I2C Master Testbench
`timescale 1ns/1ps

module i2c_tb;
    reg clk;
    reg rst_n;
    reg start;
    reg stop;
    reg read;
    reg write;
    reg [6:0] addr;
    reg [7:0] tx_data;
    wire [7:0] rx_data;
    wire ack_received;
    wire busy;
    wire ready;
    wire scl;
    wire sda;

    // SDA pullup (simulating external pull-up resistor)
    pullup(sda);

    // Instantiate I2C master
    i2c_master #(
        .CLK_FREQ(1_000_000),   // 1 MHz system clock for faster simulation
        .I2C_FREQ(100_000)       // 100 kHz I2C clock
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .start(start),
        .stop(stop),
        .read(read),
        .write(write),
        .addr(addr),
        .tx_data(tx_data),
        .rx_data(rx_data),
        .ack_received(ack_received),
        .busy(busy),
        .ready(ready),
        .scl(scl),
        .sda(sda)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #500 clk = ~clk;  // 1 MHz clock (1us period)
    end

    // Test stimulus
    initial begin
        $display("Starting I2C Master Test");
        rst_n = 0;
        start = 0;
        stop = 0;
        read = 0;
        write = 0;
        addr = 7'h50;
        tx_data = 8'h00;

        #2000 rst_n = 1;
        #2000;

        // Test 1: Send START condition and address
        $display("Test 1: Sending START and Address 0x50 (Write)");
        @(posedge clk);
        start = 1;
        read = 0;  // Write operation
        @(posedge clk);
        start = 0;

        // Wait for address to be sent
        wait(ready);
        #5000;
        $display("Address sent, ACK status: %b", ack_received);

        // Test 2: Send data byte
        $display("Test 2: Sending data byte 0xA5");
        @(posedge clk);
        write = 1;
        tx_data = 8'hA5;
        @(posedge clk);
        write = 0;

        wait(ready);
        #5000;
        $display("Data sent, ACK status: %b", ack_received);

        // Test 3: Send STOP condition
        $display("Test 3: Sending STOP condition");
        @(posedge clk);
        stop = 1;
        @(posedge clk);
        stop = 0;

        wait(!busy);
        #10000;
        $display("STOP sent, transaction complete");

        #20000;
        $display("I2C Master Test Complete");
        $finish;
    end

    // Monitor
    initial begin
        $monitor("Time=%0t busy=%b ready=%b scl=%b sda=%b ack=%b",
                 $time, busy, ready, scl, sda, ack_received);
    end

    // Optional VCD dump
    initial begin
        $dumpfile("i2c_tb.vcd");
        $dumpvars(0, i2c_tb);
    end

endmodule
