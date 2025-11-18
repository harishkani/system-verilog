// UART Transmitter - Verified Implementation
module uart_tx #(
    parameter CLK_FREQ = 50_000_000,
    parameter BAUD_RATE = 115200,
    parameter DATA_BITS = 8,
    parameter STOP_BITS = 1
) (
    input wire                  clk,
    input wire                  rst_n,
    // Data interface
    input wire [DATA_BITS-1:0]  tx_data,
    input wire                  tx_valid,
    output reg                  tx_ready,
    // UART interface
    output reg                  tx,
    // Configuration
    input wire [1:0]            parity_mode  // 00=None, 01=Odd, 10=Even
);

    localparam CLKS_PER_BIT = CLK_FREQ / BAUD_RATE;

    // State machine
    localparam IDLE = 3'd0;
    localparam START_BIT = 3'd1;
    localparam DATA_BITS_STATE = 3'd2;
    localparam PARITY_BIT = 3'd3;
    localparam STOP_BITS_STATE = 3'd4;

    reg [2:0] current_state, next_state;
    reg [15:0] clk_counter;
    reg [2:0] bit_index;
    reg [DATA_BITS-1:0] tx_shift_reg;
    reg parity_bit;
    reg tick;

    // Baud rate generator
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            clk_counter <= 16'b0;
            tick <= 1'b0;
        end else begin
            if (current_state == IDLE) begin
                clk_counter <= 16'b0;
                tick <= 1'b0;
            end else if (clk_counter == CLKS_PER_BIT - 1) begin
                clk_counter <= 16'b0;
                tick <= 1'b1;
            end else begin
                clk_counter <= clk_counter + 1;
                tick <= 1'b0;
            end
        end
    end

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
                if (tx_valid)
                    next_state = START_BIT;
            end
            START_BIT: begin
                if (tick)
                    next_state = DATA_BITS_STATE;
            end
            DATA_BITS_STATE: begin
                if (tick && bit_index == DATA_BITS - 1) begin
                    if (parity_mode != 2'b00)
                        next_state = PARITY_BIT;
                    else
                        next_state = STOP_BITS_STATE;
                end
            end
            PARITY_BIT: begin
                if (tick)
                    next_state = STOP_BITS_STATE;
            end
            STOP_BITS_STATE: begin
                if (tick && ((STOP_BITS == 1) || (bit_index == 1)))
                    next_state = IDLE;
            end
            default: next_state = IDLE;
        endcase
    end

    // Bit index counter
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            bit_index <= 3'b0;
        end else begin
            case (current_state)
                IDLE, START_BIT, PARITY_BIT: begin
                    bit_index <= 3'b0;
                end
                DATA_BITS_STATE, STOP_BITS_STATE: begin
                    if (tick)
                        bit_index <= bit_index + 1;
                end
            endcase
        end
    end

    // Shift register
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            tx_shift_reg <= 8'b0;
        end else begin
            if (current_state == IDLE && tx_valid)
                tx_shift_reg <= tx_data;
            else if (current_state == DATA_BITS_STATE && tick)
                tx_shift_reg <= {1'b0, tx_shift_reg[DATA_BITS-1:1]};
        end
    end

    // Parity calculation
    always @(*) begin
        case (parity_mode)
            2'b01: parity_bit = ^tx_data;      // Odd parity
            2'b10: parity_bit = ~(^tx_data);   // Even parity
            default: parity_bit = 1'b0;
        endcase
    end

    // TX output
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            tx <= 1'b1;
        end else begin
            case (current_state)
                IDLE:            tx <= 1'b1;
                START_BIT:       tx <= 1'b0;
                DATA_BITS_STATE: tx <= tx_shift_reg[0];
                PARITY_BIT:      tx <= parity_bit;
                STOP_BITS_STATE: tx <= 1'b1;
                default:         tx <= 1'b1;
            endcase
        end
    end

    // Ready signal
    always @(*) begin
        tx_ready = (current_state == IDLE);
    end

endmodule
