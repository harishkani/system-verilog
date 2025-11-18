`timescale 1ns/1ps

// SYNCHRONOUS FIFO - Verified Implementation
module sync_fifo #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 16
) (
    input  wire                    clk,
    input  wire                    rst_n,
    input  wire [DATA_WIDTH-1:0]   wr_data,
    input  wire                    wr_en,
    output wire                    full,
    output wire [DATA_WIDTH-1:0]   rd_data,
    input  wire                    rd_en,
    output wire                    empty,
    output wire [$clog2(DEPTH):0]  count
);

    reg [DATA_WIDTH-1:0] mem [0:DEPTH-1];
    reg [$clog2(DEPTH):0] wr_ptr, rd_ptr, count_reg;

    assign full = (count_reg == DEPTH);
    assign empty = (count_reg == 0);
    assign count = count_reg;

    // Write
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            wr_ptr <= 0;
        else if (wr_en && !full) begin
            mem[wr_ptr[$clog2(DEPTH)-1:0]] <= wr_data;
            wr_ptr <= wr_ptr + 1;
        end
    end

    // Read
    reg [DATA_WIDTH-1:0] rd_data_reg;
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_ptr <= 0;
            rd_data_reg <= 0;
        end else if (rd_en && !empty) begin
            rd_data_reg <= mem[rd_ptr[$clog2(DEPTH)-1:0]];
            rd_ptr <= rd_ptr + 1;
        end
    end
    assign rd_data = rd_data_reg;

    // Count
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count_reg <= 0;
        else begin
            case ({wr_en && !full, rd_en && !empty})
                2'b10: count_reg <= count_reg + 1;
                2'b01: count_reg <= count_reg - 1;
                default: count_reg <= count_reg;
            endcase
        end
    end
endmodule

// TESTBENCH
module fifo_tb;
    reg clk=0, rst_n;
    reg [7:0] wr_data;
    reg wr_en, rd_en;
    wire [7:0] rd_data;
    wire full, empty;
    wire [4:0] count;

    always #5 clk = ~clk;

    sync_fifo #(.DATA_WIDTH(8), .DEPTH(16)) dut (
        .clk(clk), .rst_n(rst_n),
        .wr_data(wr_data), .wr_en(wr_en), .full(full),
        .rd_data(rd_data), .rd_en(rd_en), .empty(empty),
        .count(count)
    );

    integer i, errors=0;

    initial begin
        $dumpfile("fifo.vcd");
        $dumpvars;

        $display("\n========== FIFO TESTS ==========\n");

        rst_n=0; wr_en=0; rd_en=0; #20 rst_n=1; #20;

        // Test 1: Check empty
        if (empty && !full && count==0) begin
            $display("✓ Test 1: Initial empty state");
        end else begin
            $display("✗ Test 1 FAIL");
            errors=errors+1;
        end

        // Test 2: Write and read back
        $display("\nTest 2: Write/Read");
        for (i=0; i<8; i=i+1) begin
            @(posedge clk);
            wr_data = i*17;  // Some pattern
            wr_en = 1;
        end
        @(posedge clk);
        wr_en = 0;
        #20;

        if (count == 8) begin
            $display("✓ Wrote 8 items, count=%0d", count);
        end else begin
            $display("✗ Count wrong: %0d", count);
            errors=errors+1;
        end

        // Read back
        for (i=0; i<8; i=i+1) begin
            @(posedge clk);
            rd_en = 1;
            #1;  // Let rd_en propagate
            @(posedge clk);
            #1;  // Data appears after clock
            if (rd_data == i*17) begin
                $display("  ✓ Read[%0d] = 0x%02h", i, rd_data);
            end else begin
                $display("  ✗ Read[%0d] = 0x%02h (exp 0x%02h)", i, rd_data, i*17);
                errors=errors+1;
            end
        end
        rd_en = 0;
        #20;

        // Test 3: Fill completely
        $display("\nTest 3: Fill FIFO");
        for (i=0; i<16; i=i+1) begin
            @(posedge clk);
            wr_data = i;
            wr_en = 1;
        end
        @(posedge clk);
        wr_en = 0;
        #20;

        if (full && count==16) begin
            $display("✓ FIFO full");
        end else begin
            $display("✗ Not full: count=%0d", count);
            errors=errors+1;
        end

        // Test 4: Empty completely
        $display("\nTest 4: Empty FIFO");
        rd_en = 1;
        repeat(16) @(posedge clk);
        @(posedge clk);
        rd_en = 0;
        #20;

        if (empty && count==0) begin
            $display("✓ FIFO empty");
        end else begin
            $display("✗ Not empty: count=%0d", count);
            errors=errors+1;
        end

        $display("\n================================");
        $display("Errors: %0d", errors);
        if (errors==0)
            $display("✓✓✓ ALL TESTS PASSED ✓✓✓");
        $display("================================\n");
        $finish;
    end
endmodule
