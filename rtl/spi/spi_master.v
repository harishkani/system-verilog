// SPI Master - Verified Implementation
module spi_master #(
    parameter DATA_WIDTH = 8,
    parameter CLK_DIV = 4
) (
    input wire                    clk,
    input wire                    rst_n,
    // Control interface
    input wire [DATA_WIDTH-1:0]   tx_data,
    input wire                    tx_valid,
    output reg                    tx_ready,
    output reg [DATA_WIDTH-1:0]   rx_data,
    output reg                    rx_valid,
    // SPI interface
    output reg                    sclk,
    output wire                   mosi,
    input wire                    miso,
    output reg                    cs_n,
    // Configuration
    input wire                    cpol,
    input wire                    cpha
);

    // State machine
    localparam IDLE = 2'b00;
    localparam TRANSFER = 2'b01;
    localparam DONE = 2'b10;

    reg [1:0] current_state, next_state;

    // Internal registers
    reg [DATA_WIDTH-1:0] tx_shift_reg;
    reg [DATA_WIDTH-1:0] rx_shift_reg;
    reg [2:0] bit_counter;
    reg [1:0] clk_counter;
    reg sclk_enable;
    reg sclk_int;
    reg sclk_prev;
    reg sclk_rising_edge;
    reg sclk_falling_edge;
    reg sample_edge;
    reg change_edge;

    // SPI clock generation
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            clk_counter <= 2'b0;
            sclk_int <= cpol;
        end else begin
            if (sclk_enable) begin
                if (clk_counter == CLK_DIV - 1) begin
                    clk_counter <= 2'b0;
                    sclk_int <= ~sclk_int;
                end else begin
                    clk_counter <= clk_counter + 1;
                end
            end else begin
                clk_counter <= 2'b0;
                sclk_int <= cpol;
            end
        end
    end

    always @(posedge clk) begin
        sclk <= sclk_int;
    end

    // Detect SPI clock edges
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            sclk_prev <= cpol;
        else
            sclk_prev <= sclk_int;
    end

    always @(*) begin
        sclk_rising_edge = !sclk_prev && sclk_int;
        sclk_falling_edge = sclk_prev && !sclk_int;
    end

    // Determine sampling and changing edges based on mode
    always @(*) begin
        if (cpha == 0) begin
            sample_edge = cpol ? sclk_falling_edge : sclk_rising_edge;
            change_edge = cpol ? sclk_rising_edge : sclk_falling_edge;
        end else begin
            sample_edge = cpol ? sclk_rising_edge : sclk_falling_edge;
            change_edge = cpol ? sclk_falling_edge : sclk_rising_edge;
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
                if (tx_valid && tx_ready)
                    next_state = TRANSFER;
            end
            TRANSFER: begin
                if (bit_counter == DATA_WIDTH - 1 && sample_edge)
                    next_state = DONE;
            end
            DONE: begin
                next_state = IDLE;
            end
            default: next_state = IDLE;
        endcase
    end

    // Control signals
    always @(*) begin
        tx_ready = (current_state == IDLE);
        rx_valid = (current_state == DONE);
        sclk_enable = (current_state == TRANSFER);
        cs_n = (current_state == IDLE);
    end

    // Bit counter
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            bit_counter <= 3'b0;
        end else begin
            case (current_state)
                IDLE: bit_counter <= 3'b0;
                TRANSFER: begin
                    if (sample_edge)
                        bit_counter <= bit_counter + 1;
                end
            endcase
        end
    end

    // Transmit shift register and MOSI
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            tx_shift_reg <= 8'b0;
        end else begin
            case (current_state)
                IDLE: begin
                    if (tx_valid)
                        tx_shift_reg <= tx_data;
                end
                TRANSFER: begin
                    if (change_edge)
                        tx_shift_reg <= {tx_shift_reg[DATA_WIDTH-2:0], 1'b0};
                end
            endcase
        end
    end

    assign mosi = tx_shift_reg[DATA_WIDTH-1];

    // Receive shift register
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_shift_reg <= 8'b0;
            rx_data <= 8'b0;
        end else begin
            if (current_state == TRANSFER && sample_edge) begin
                rx_shift_reg <= {rx_shift_reg[DATA_WIDTH-2:0], miso};
            end
            if (current_state == DONE) begin
                rx_data <= rx_shift_reg;
            end
        end
    end

endmodule
