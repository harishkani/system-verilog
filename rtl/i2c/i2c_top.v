// I2C Top-Level Module
// Multi-master capable I2C interface
// Usage: Simple interface for I2C communication

module i2c_top #(
    parameter CLK_DIV = 100    // Clock divider for I2C SCL frequency
                               // SCL_freq = system_clk / (4 * CLK_DIV)
) (
    // System signals
    input wire clk,
    input wire rst_n,

    // Control interface
    input wire start,
    input wire wr,
    input wire [6:0] slave_addr,
    input wire [7:0] data_in,
    output wire [7:0] data_out,
    output wire busy,
    output wire ack_error,

    // I2C physical interface (bidirectional with tri-state control)
    inout wire i2c_sda,
    inout wire i2c_scl
);

    // Instantiate I2C master
    i2c_master #(
        .CLK_DIV(CLK_DIV)
    ) u_i2c_master (
        .clk(clk),
        .rst_n(rst_n),
        .start(start),
        .wr(wr),
        .slave_addr(slave_addr),
        .data_in(data_in),
        .data_out(data_out),
        .busy(busy),
        .ack_error(ack_error),
        .sda(i2c_sda),
        .scl(i2c_scl)
    );

endmodule
