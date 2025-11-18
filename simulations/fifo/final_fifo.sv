`timescale 1ns/1ps

module sync_fifo #(parameter DW=8, D=16) (
    input clk, rst_n,
    input [DW-1:0] wr_data,
    input wr_en,
    output full,
    output reg [DW-1:0] rd_data,
    input rd_en,
    output empty,
    output [$clog2(D):0] count
);
    reg [DW-1:0] mem [0:D-1];
    reg [$clog2(D):0] wr_ptr=0, rd_ptr=0, cnt=0;

    assign full = (cnt == D);
    assign empty = (cnt == 0);
    assign count = cnt;

    always @(posedge clk or negedge rst_n)
        if (!rst_n) wr_ptr <= 0;
        else if (wr_en && !full) begin
            mem[wr_ptr[$clog2(D)-1:0]] <= wr_data;
            wr_ptr <= wr_ptr + 1;
        end

    always @(posedge clk or negedge rst_n)
        if (!rst_n) begin
            rd_ptr <= 0;
            rd_data <= 0;
        end else if (rd_en && !empty) begin
            rd_data <= mem[rd_ptr[$clog2(D)-1:0]];
            rd_ptr <= rd_ptr + 1;
        end

    always @(posedge clk or negedge rst_n)
        if (!rst_n) cnt <= 0;
        else case ({wr_en&&!full, rd_en&&!empty})
            2'b10: cnt <= cnt + 1;
            2'b01: cnt <= cnt - 1;
            default: cnt <= cnt;
        endcase
endmodule

module tb;
    reg clk=0, rst_n;
    reg [7:0] wr_data;
    reg wr_en, rd_en;
    wire [7:0] rd_data;
    wire full, empty;
    wire [4:0] count;
    integer i, err=0;

    always #5 clk=~clk;

    sync_fifo fifo(.clk(clk), .rst_n(rst_n),
                   .wr_data(wr_data), .wr_en(wr_en), .full(full),
                   .rd_data(rd_data), .rd_en(rd_en), .empty(empty),
                   .count(count));

    initial begin
        $dumpfile("fifo.vcd");
        $dumpvars;

        $display("\n===== FIFO TEST =====\n");

        rst_n=0; wr_en=0; rd_en=0;
        #20 rst_n=1; #20;

        // Write 4 values
        $display("Writing 4 values...");
        wr_data=8'hAA; wr_en=1; @(posedge clk);
        wr_data=8'hBB; @(posedge clk);
        wr_data=8'hCC; @(posedge clk);
        wr_data=8'hDD; @(posedge clk);
        wr_en=0; #20;

        if (count==4) $display("✓ Count=4 after write");
        else begin $display("✗ Count=%0d", count); err=err+1; end

        // Read 4 values
        $display("\nReading 4 values...");
        rd_en=1; #1; @(posedge clk); #1;
        if (rd_data==8'hAA) $display("✓ Read 0xAA");
        else begin $display("✗ Got 0x%h", rd_data); err=err+1; end

        @(posedge clk); #1;
        if (rd_data==8'hBB) $display("✓ Read 0xBB");
        else begin $display("✗ Got 0x%h", rd_data); err=err+1; end

        @(posedge clk); #1;
        if (rd_data==8'hCC) $display("✓ Read 0xCC");
        else begin $display("✗ Got 0x%h", rd_data); err=err+1; end

        @(posedge clk); #1;
        if (rd_data==8'hDD) $display("✓ Read 0xDD");
        else begin $display("✗ Got 0x%h", rd_data); err=err+1; end

        rd_en=0; #20;

        if (empty) $display("✓ Empty after reading all");
        else begin $display("✗ Not empty"); err=err+1; end

        // Fill test
        $display("\nFilling FIFO...");
        wr_en=1;
        for (i=0; i<16; i=i+1) begin
            wr_data = i;
            @(posedge clk);
        end
        wr_en=0; #20;

        if (full) $display("✓ Full after 16 writes");
        else begin $display("✗ Not full"); err=err+1; end

        $display("\n=====================");
        $display("ERRORS: %0d", err);
        if (err==0) $display("✓✓✓ ALL PASS ✓✓✓");
        $display("=====================\n");
        $finish;
    end
endmodule
