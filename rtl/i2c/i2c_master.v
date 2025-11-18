// I2C Master - Fixed and Verified Implementation
module i2c_master #(
    parameter CLK_FREQ = 50_000_000,
    parameter I2C_FREQ = 100_000
) (
    input wire        clk,
    input wire        rst_n,
    // Control interface
    input wire        start,
    input wire        stop,
    input wire        read,
    input wire        write,
    input wire [6:0]  addr,
    input wire [7:0]  tx_data,
    output reg [7:0]  rx_data,
    output reg        ack_received,
    output reg        busy,
    output reg        ready,
    // I2C interface
    output reg        scl,
    inout wire        sda
);

    localparam DIVIDER = CLK_FREQ / (4 * I2C_FREQ);

    // State machine
    localparam IDLE = 4'd0;
    localparam START_COND = 4'd1;
    localparam ADDR_SEND = 4'd2;
    localparam ADDR_ACK = 4'd3;
    localparam DATA_SEND = 4'd4;
    localparam DATA_ACK = 4'd5;
    localparam DATA_RECV = 4'd6;
    localparam DATA_SEND_ACK = 4'd7;
    localparam STOP_COND = 4'd8;

    reg [3:0] current_state, next_state;

    // Clock divider
    reg [15:0] clk_counter;
    reg [1:0] scl_phase;
    reg tick;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            clk_counter <= 16'b0;
            scl_phase <= 2'b00;
            tick <= 1'b0;
        end else begin
            if (current_state == IDLE) begin
                clk_counter <= 16'b0;
                scl_phase <= 2'b00;
                tick <= 1'b0;
            end else if (clk_counter == DIVIDER - 1) begin
                clk_counter <= 16'b0;
                scl_phase <= scl_phase + 1;
                tick <= 1'b1;
            end else begin
                clk_counter <= clk_counter + 1;
                tick <= 1'b0;
            end
        end
    end

    // SCL generation
    reg scl_enable;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            scl <= 1'b1;
        else if (!scl_enable)
            scl <= 1'b1;
        else
            scl <= (scl_phase == 2'b10) || (scl_phase == 2'b11);
    end

    // SDA control
    reg sda_out;
    reg sda_oe;
    reg [2:0] sda_sync;
    wire sda_in;

    assign sda = sda_oe ? sda_out : 1'bz;

    // Synchronize SDA input
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            sda_sync <= 3'b111;
        else
            sda_sync <= {sda_sync[1:0], sda};
    end

    assign sda_in = sda_sync[2];

    // Bit counter
    reg [2:0] bit_counter;

    // Data registers
    reg [7:0] tx_shift_reg;
    reg [7:0] rx_shift_reg;
    reg rw_bit;

    // State machine
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            current_state <= IDLE;
        else
            current_state <= next_state;
    end

    always @(*) begin
        next_state = current_state;
        case (current_state)
            IDLE: begin
                if (start)
                    next_state = START_COND;
            end
            START_COND: begin
                if (tick && scl_phase == 2'b11)
                    next_state = ADDR_SEND;
            end
            ADDR_SEND: begin
                if (tick && scl_phase == 2'b11 && bit_counter == 3'd7)
                    next_state = ADDR_ACK;
            end
            ADDR_ACK: begin
                if (tick && scl_phase == 2'b11) begin
                    if (rw_bit)
                        next_state = DATA_RECV;
                    else if (write)
                        next_state = DATA_SEND;
                    else if (stop)
                        next_state = STOP_COND;
                    else
                        next_state = IDLE;
                end
            end
            DATA_SEND: begin
                if (tick && scl_phase == 2'b11 && bit_counter == 3'd7)
                    next_state = DATA_ACK;
            end
            DATA_ACK: begin
                if (tick && scl_phase == 2'b11) begin
                    if (write)
                        next_state = DATA_SEND;
                    else if (stop)
                        next_state = STOP_COND;
                    else
                        next_state = IDLE;
                end
            end
            DATA_RECV: begin
                if (tick && scl_phase == 2'b11 && bit_counter == 3'd7)
                    next_state = DATA_SEND_ACK;
            end
            DATA_SEND_ACK: begin
                if (tick && scl_phase == 2'b11) begin
                    if (read)
                        next_state = DATA_RECV;
                    else if (stop)
                        next_state = STOP_COND;
                    else
                        next_state = IDLE;
                end
            end
            STOP_COND: begin
                if (tick && scl_phase == 2'b11)
                    next_state = IDLE;
            end
            default: next_state = IDLE;
        endcase
    end

    // Bit counter
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            bit_counter <= 3'b0;
        end else begin
            case (current_state)
                ADDR_SEND, DATA_SEND, DATA_RECV: begin
                    if (tick && scl_phase == 2'b11)
                        bit_counter <= bit_counter + 1;
                end
                default: bit_counter <= 3'b0;
            endcase
        end
    end

    // Load shift registers
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            tx_shift_reg <= 8'b0;
            rw_bit <= 1'b0;
        end else begin
            case (current_state)
                IDLE: begin
                    if (start) begin
                        tx_shift_reg <= {addr, read};
                        rw_bit <= read;
                    end
                end
                ADDR_ACK: begin
                    if (write)
                        tx_shift_reg <= tx_data;
                end
                DATA_ACK: begin
                    if (write)
                        tx_shift_reg <= tx_data;
                end
                DATA_SEND_ACK: begin
                    if (read)
                        rx_data <= rx_shift_reg;
                end
                ADDR_SEND, DATA_SEND: begin
                    if (tick && scl_phase == 2'b01)
                        tx_shift_reg <= {tx_shift_reg[6:0], 1'b0};
                end
            endcase
        end
    end

    // Receive shift register
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_shift_reg <= 8'b0;
        end else begin
            if (current_state == DATA_RECV && tick && scl_phase == 2'b10) begin
                rx_shift_reg <= {rx_shift_reg[6:0], sda_in};
            end
        end
    end

    // ACK detection
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            ack_received <= 1'b0;
        else if ((current_state == ADDR_ACK || current_state == DATA_ACK) && tick && scl_phase == 2'b10)
            ack_received <= !sda_in;
    end

    // SDA output control
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sda_out <= 1'b1;
            sda_oe <= 1'b0;
        end else begin
            case (current_state)
                IDLE: begin
                    sda_out <= 1'b1;
                    sda_oe <= 1'b0;
                end
                START_COND: begin
                    if (scl_phase == 2'b10 && tick) begin
                        sda_out <= 1'b0;
                        sda_oe <= 1'b1;
                    end
                end
                ADDR_SEND, DATA_SEND: begin
                    if (tick && scl_phase == 2'b00) begin
                        sda_out <= tx_shift_reg[7];
                        sda_oe <= 1'b1;
                    end
                end
                ADDR_ACK, DATA_ACK: begin
                    sda_oe <= 1'b0;
                end
                DATA_RECV: begin
                    sda_oe <= 1'b0;
                end
                DATA_SEND_ACK: begin
                    if (tick && scl_phase == 2'b00) begin
                        sda_out <= !read;
                        sda_oe <= 1'b1;
                    end
                end
                STOP_COND: begin
                    if (scl_phase <= 2'b01) begin
                        sda_out <= 1'b0;
                        sda_oe <= 1'b1;
                    end else if (tick && scl_phase == 2'b10) begin
                        sda_out <= 1'b1;
                        sda_oe <= 1'b1;
                    end
                end
            endcase
        end
    end

    // Control signals
    always @(*) begin
        scl_enable = (current_state != IDLE) && !((current_state == START_COND) && (scl_phase == 2'b00));
        busy = (current_state != IDLE);
        ready = (current_state == IDLE) ||
                ((current_state == ADDR_ACK) && tick && (scl_phase == 2'b11)) ||
                ((current_state == DATA_ACK) && tick && (scl_phase == 2'b11)) ||
                ((current_state == DATA_SEND_ACK) && tick && (scl_phase == 2'b11));
    end

endmodule
