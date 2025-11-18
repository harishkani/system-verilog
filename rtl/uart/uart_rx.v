// UART Receiver - Verified Implementation
module uart_rx #(
    parameter CLK_FREQ = 50_000_000,
    parameter BAUD_RATE = 115200,
    parameter DATA_BITS = 8,
    parameter STOP_BITS = 1
) (
    input wire                  clk,
    input wire                  rst_n,
    // Data interface
    output reg [DATA_BITS-1:0]  rx_data,
    output reg                  rx_valid,
    output reg                  rx_error,
    // UART interface
    input wire                  rx,
    // Configuration
    input wire [1:0]            parity_mode
);

    localparam CLKS_PER_BIT = CLK_FREQ / BAUD_RATE;

    // State machine
    localparam IDLE = 3'd0;
    localparam START_BIT = 3'd1;
    localparam DATA_BITS_STATE = 3'd2;
    localparam PARITY_BIT = 3'd3;
    localparam STOP_BITS_STATE = 3'd4;
    localparam ERROR = 3'd5;

    reg [2:0] current_state, next_state;

    // Synchronize RX input
    reg [2:0] rx_sync;
    wire rx_synced;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            rx_sync <= 3'b111;
        else
            rx_sync <= {rx_sync[1:0], rx};
    end

    assign rx_synced = rx_sync[2];

    // Detect start bit
    reg rx_prev;
    wire start_detected;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            rx_prev <= 1'b1;
        else
            rx_prev <= rx_synced;
    end

    assign start_detected = rx_prev && !rx_synced;

    // Baud rate counter
    reg [15:0] clk_counter;
    wire tick;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            clk_counter <= 16'b0;
        end else begin
            if (current_state == IDLE && start_detected) begin
                // Start counter at half-bit to sample at mid-bit
                clk_counter <= 16'b0;
            end else if (clk_counter == CLKS_PER_BIT - 1) begin
                clk_counter <= 16'b0;
            end else begin
                clk_counter <= clk_counter + 1;
            end
        end
    end

    assign tick = (clk_counter == CLKS_PER_BIT/2);

    // State machine
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            current_state <= IDLE;
        else
            current_state <= next_state;
    end

    reg [2:0] bit_index;

    always @(*) begin
        next_state = current_state;
        case (current_state)
            IDLE: begin
                if (start_detected)
                    next_state = START_BIT;
            end
            START_BIT: begin
                if (tick) begin
                    // Sample at mid-bit of start bit
                    if (rx_synced == 1'b0)
                        next_state = DATA_BITS_STATE;
                    else
                        next_state = IDLE;
                end
            end
            DATA_BITS_STATE: begin
                if (clk_counter == CLKS_PER_BIT - 1 && bit_index == DATA_BITS - 1) begin
                    if (parity_mode != 2'b00)
                        next_state = PARITY_BIT;
                    else
                        next_state = STOP_BITS_STATE;
                end
            end
            PARITY_BIT: begin
                if (clk_counter == CLKS_PER_BIT - 1)
                    next_state = STOP_BITS_STATE;
            end
            STOP_BITS_STATE: begin
                if (clk_counter == CLKS_PER_BIT - 1) begin
                    if (rx_synced == 1'b1) begin
                        if (STOP_BITS == 1 || bit_index == 1)
                            next_state = IDLE;
                    end else begin
                        next_state = ERROR;
                    end
                end
            end
            ERROR: begin
                next_state = IDLE;
            end
            default: next_state = IDLE;
        endcase
    end

    // Bit index
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            bit_index <= 3'b0;
        end else begin
            case (current_state)
                IDLE, START_BIT, PARITY_BIT: begin
                    bit_index <= 3'b0;
                end
                DATA_BITS_STATE, STOP_BITS_STATE: begin
                    if (clk_counter == CLKS_PER_BIT - 1)
                        bit_index <= bit_index + 1;
                end
            endcase
        end
    end

    // Shift register
    reg [DATA_BITS-1:0] rx_shift_reg;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_shift_reg <= 8'b0;
        end else begin
            if (current_state == DATA_BITS_STATE && tick) begin
                rx_shift_reg <= {rx_synced, rx_shift_reg[DATA_BITS-1:1]};
            end
        end
    end

    // Parity check
    reg parity_received;
    wire parity_calculated;
    wire parity_error;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            parity_received <= 1'b0;
        else if (current_state == PARITY_BIT && tick)
            parity_received <= rx_synced;
    end

    assign parity_calculated = (parity_mode == 2'b01) ? (^rx_shift_reg) : (~(^rx_shift_reg));
    assign parity_error = (parity_mode != 2'b00) && (parity_received != parity_calculated);

    // Output
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_data <= 8'b0;
            rx_valid <= 1'b0;
            rx_error <= 1'b0;
        end else begin
            rx_valid <= 1'b0;
            rx_error <= 1'b0;

            if (next_state == IDLE && current_state == STOP_BITS_STATE) begin
                rx_data <= rx_shift_reg;
                rx_valid <= !parity_error;
                rx_error <= parity_error;
            end else if (current_state == ERROR) begin
                rx_error <= 1'b1;
            end
        end
    end

endmodule
