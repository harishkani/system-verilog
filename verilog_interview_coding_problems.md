# Verilog Interview Coding Problems
## Common Questions Asked in Placement Exams (2024-2025)

Based on top interview resources and placement exam patterns.

---

## Section 1: Combinational Circuits

### 1. 4-to-1 Multiplexer (Most Common!)
```verilog
module mux_4to1 (
    input [3:0] in,
    input [1:0] sel,
    output reg out
);
    always @(*) begin
        case(sel)
            2'b00: out = in[0];
            2'b01: out = in[1];
            2'b10: out = in[2];
            2'b11: out = in[3];
        endcase
    end
endmodule
```

### 2. 8-to-1 Multiplexer Using 4-to-1 MUX
```verilog
module mux_8to1 (
    input [7:0] in,
    input [2:0] sel,
    output out
);
    wire mux0_out, mux1_out;

    mux_4to1 m0 (.in(in[3:0]), .sel(sel[1:0]), .out(mux0_out));
    mux_4to1 m1 (.in(in[7:4]), .sel(sel[1:0]), .out(mux1_out));

    assign out = sel[2] ? mux1_out : mux0_out;
endmodule
```

### 3. 2-to-4 Decoder
```verilog
module decoder_2to4 (
    input [1:0] in,
    input enable,
    output reg [3:0] out
);
    always @(*) begin
        if (enable) begin
            case(in)
                2'b00: out = 4'b0001;
                2'b01: out = 4'b0010;
                2'b10: out = 4'b0100;
                2'b11: out = 4'b1000;
                default: out = 4'b0000;
            endcase
        end else
            out = 4'b0000;
    end
endmodule
```

### 4. 3-to-8 Decoder
```verilog
module decoder_3to8 (
    input [2:0] in,
    output reg [7:0] out
);
    always @(*) begin
        out = 8'b0;
        out[in] = 1'b1;
    end
endmodule
```

### 5. 4-to-2 Priority Encoder (Very Common!)
```verilog
module priority_encoder_4to2 (
    input [3:0] in,
    output reg [1:0] out,
    output reg valid
);
    always @(*) begin
        casex(in)
            4'b1xxx: begin out = 2'b11; valid = 1'b1; end
            4'b01xx: begin out = 2'b10; valid = 1'b1; end
            4'b001x: begin out = 2'b01; valid = 1'b1; end
            4'b0001: begin out = 2'b00; valid = 1'b1; end
            default: begin out = 2'b00; valid = 1'b0; end
        endcase
    end
endmodule
```

### 6. 8-to-3 Priority Encoder
```verilog
module priority_encoder_8to3 (
    input [7:0] in,
    output reg [2:0] out
);
    always @(*) begin
        if      (in[7]) out = 3'd7;
        else if (in[6]) out = 3'd6;
        else if (in[5]) out = 3'd5;
        else if (in[4]) out = 3'd4;
        else if (in[3]) out = 3'd3;
        else if (in[2]) out = 3'd2;
        else if (in[1]) out = 3'd1;
        else            out = 3'd0;
    end
endmodule
```

### 7. 4-bit Comparator
```verilog
module comparator_4bit (
    input [3:0] a, b,
    output reg equal, greater, less
);
    always @(*) begin
        equal   = (a == b);
        greater = (a > b);
        less    = (a < b);
    end
endmodule
```

### 8. Parity Generator (Even/Odd)
```verilog
module parity_gen (
    input [7:0] data,
    output even_parity,
    output odd_parity
);
    assign even_parity = ^data;      // XOR reduction
    assign odd_parity  = ~(^data);   // XNOR reduction
endmodule
```

### 9. 4-bit Adder/Subtractor
```verilog
module adder_subtractor_4bit (
    input [3:0] a, b,
    input mode,  // 0=add, 1=subtract
    output [3:0] result,
    output carry_out
);
    wire [3:0] b_xor;

    assign b_xor = b ^ {4{mode}};
    assign {carry_out, result} = a + b_xor + mode;
endmodule
```

### 10. Barrel Shifter (4-bit)
```verilog
module barrel_shifter_4bit (
    input [3:0] data_in,
    input [1:0] shift_amt,
    input direction,  // 0=left, 1=right
    output reg [3:0] data_out
);
    always @(*) begin
        if (direction == 0)  // Left shift
            data_out = data_in << shift_amt;
        else                 // Right shift
            data_out = data_in >> shift_amt;
    end
endmodule
```

### 11. 4-bit ALU (Common Interview Question!)
```verilog
module alu_4bit (
    input [3:0] a, b,
    input [2:0] op,
    output reg [3:0] result,
    output reg zero
);
    always @(*) begin
        case(op)
            3'b000: result = a + b;      // ADD
            3'b001: result = a - b;      // SUB
            3'b010: result = a & b;      // AND
            3'b011: result = a | b;      // OR
            3'b100: result = a ^ b;      // XOR
            3'b101: result = ~a;         // NOT
            3'b110: result = a << 1;     // SLL
            3'b111: result = a >> 1;     // SRL
        endcase
        zero = (result == 0);
    end
endmodule
```

---

## Section 2: Sequential Circuits - Flip-Flops

### 12. D Flip-Flop with Asynchronous Reset
```verilog
module dff_async_reset (
    input clk, rst_n, d,
    output reg q
);
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            q <= 1'b0;
        else
            q <= d;
    end
endmodule
```

### 13. D Flip-Flop with Synchronous Reset
```verilog
module dff_sync_reset (
    input clk, rst, d,
    output reg q
);
    always @(posedge clk) begin
        if (rst)
            q <= 1'b0;
        else
            q <= d;
    end
endmodule
```

### 14. D Flip-Flop with Enable
```verilog
module dff_enable (
    input clk, rst_n, en, d,
    output reg q
);
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            q <= 1'b0;
        else if (en)
            q <= d;
    end
endmodule
```

### 15. T Flip-Flop
```verilog
module tff (
    input clk, rst_n, t,
    output reg q
);
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            q <= 1'b0;
        else if (t)
            q <= ~q;
    end
endmodule
```

### 16. JK Flip-Flop
```verilog
module jkff (
    input clk, rst_n, j, k,
    output reg q
);
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            q <= 1'b0;
        else
            case({j, k})
                2'b00: q <= q;
                2'b01: q <= 1'b0;
                2'b10: q <= 1'b1;
                2'b11: q <= ~q;
            endcase
    end
endmodule
```

---

## Section 3: Counters (Very Common!)

### 17. 4-bit Binary Up Counter
```verilog
module counter_4bit_up (
    input clk, rst_n,
    output reg [3:0] count
);
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= 4'b0;
        else
            count <= count + 1;
    end
endmodule
```

### 18. 4-bit Up/Down Counter
```verilog
module counter_up_down (
    input clk, rst_n, up_down,  // 1=up, 0=down
    output reg [3:0] count
);
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= 4'b0;
        else if (up_down)
            count <= count + 1;
        else
            count <= count - 1;
    end
endmodule
```

### 19. Modulo-N Counter (Mod-10 BCD Counter)
```verilog
module bcd_counter (
    input clk, rst_n,
    output reg [3:0] count
);
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= 4'b0;
        else if (count == 4'd9)
            count <= 4'b0;
        else
            count <= count + 1;
    end
endmodule
```

### 20. Gray Code Counter
```verilog
module gray_counter (
    input clk, rst_n,
    output reg [3:0] gray_count
);
    reg [3:0] bin_count;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            bin_count <= 4'b0;
        else
            bin_count <= bin_count + 1;
    end

    // Binary to Gray conversion
    always @(*) begin
        gray_count = bin_count ^ (bin_count >> 1);
    end
endmodule
```

### 21. Johnson Counter (Ring Counter)
```verilog
module johnson_counter (
    input clk, rst_n,
    output reg [3:0] count
);
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= 4'b0;
        else
            count <= {~count[0], count[3:1]};
    end
endmodule
```

### 22. Ring Counter
```verilog
module ring_counter (
    input clk, rst_n,
    output reg [3:0] count
);
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= 4'b0001;
        else
            count <= {count[2:0], count[3]};
    end
endmodule
```

---

## Section 4: Shift Registers

### 23. SISO (Serial In Serial Out)
```verilog
module siso_shift_register (
    input clk, rst_n, serial_in,
    output serial_out
);
    reg [7:0] shift_reg;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            shift_reg <= 8'b0;
        else
            shift_reg <= {shift_reg[6:0], serial_in};
    end

    assign serial_out = shift_reg[7];
endmodule
```

### 24. SIPO (Serial In Parallel Out)
```verilog
module sipo_shift_register (
    input clk, rst_n, serial_in,
    output [7:0] parallel_out
);
    reg [7:0] shift_reg;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            shift_reg <= 8'b0;
        else
            shift_reg <= {shift_reg[6:0], serial_in};
    end

    assign parallel_out = shift_reg;
endmodule
```

### 25. PISO (Parallel In Serial Out)
```verilog
module piso_shift_register (
    input clk, rst_n, load,
    input [7:0] parallel_in,
    output serial_out
);
    reg [7:0] shift_reg;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            shift_reg <= 8'b0;
        else if (load)
            shift_reg <= parallel_in;
        else
            shift_reg <= {shift_reg[6:0], 1'b0};
    end

    assign serial_out = shift_reg[7];
endmodule
```

### 26. Universal Shift Register
```verilog
module universal_shift_register (
    input clk, rst_n,
    input [1:0] mode,  // 00=hold, 01=left, 10=right, 11=load
    input serial_in_left, serial_in_right,
    input [7:0] parallel_in,
    output reg [7:0] q
);
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            q <= 8'b0;
        else
            case(mode)
                2'b00: q <= q;                              // Hold
                2'b01: q <= {q[6:0], serial_in_right};     // Shift left
                2'b10: q <= {serial_in_left, q[7:1]};      // Shift right
                2'b11: q <= parallel_in;                    // Load
            endcase
    end
endmodule
```

---

## Section 5: FSM (Finite State Machines)

### 27. Sequence Detector - "1011" (Non-Overlapping, Moore)
```verilog
module seq_detector_1011_moore (
    input clk, rst_n, din,
    output reg detected
);
    typedef enum reg [2:0] {
        S0 = 3'b000,  // Initial
        S1 = 3'b001,  // Got 1
        S2 = 3'b010,  // Got 10
        S3 = 3'b011,  // Got 101
        S4 = 3'b100   // Got 1011 (detected)
    } state_t;

    state_t state, next_state;

    // State register
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= S0;
        else
            state <= next_state;
    end

    // Next state logic
    always @(*) begin
        case(state)
            S0: next_state = din ? S1 : S0;
            S1: next_state = din ? S1 : S2;
            S2: next_state = din ? S3 : S0;
            S3: next_state = din ? S4 : S0;
            S4: next_state = din ? S1 : S0;
            default: next_state = S0;
        endcase
    end

    // Output logic (Moore)
    always @(*) begin
        detected = (state == S4);
    end
endmodule
```

### 28. Sequence Detector - "1011" (Overlapping)
```verilog
module seq_detector_1011_overlap (
    input clk, rst_n, din,
    output reg detected
);
    typedef enum reg [2:0] {
        S0, S1, S10, S101, S1011
    } state_t;

    state_t state, next_state;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) state <= S0;
        else state <= next_state;
    end

    always @(*) begin
        case(state)
            S0:    next_state = din ? S1 : S0;
            S1:    next_state = din ? S1 : S10;
            S10:   next_state = din ? S101 : S0;
            S101:  next_state = din ? S1011 : S10;  // Overlap here!
            S1011: next_state = din ? S1 : S10;
            default: next_state = S0;
        endcase
    end

    always @(*) detected = (state == S1011);
endmodule
```

### 29. Mealy FSM - 101 Detector
```verilog
module seq_detector_101_mealy (
    input clk, rst_n, din,
    output reg detected
);
    typedef enum reg [1:0] {S0, S1, S10} state_t;
    state_t state, next_state;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) state <= S0;
        else state <= next_state;
    end

    always @(*) begin
        detected = 1'b0;
        case(state)
            S0: next_state = din ? S1 : S0;
            S1: next_state = din ? S1 : S10;
            S10: begin
                next_state = din ? S1 : S0;
                if (din) detected = 1'b1;  // Mealy output
            end
            default: next_state = S0;
        endcase
    end
endmodule
```

### 30. Traffic Light Controller (Simple)
```verilog
module traffic_light (
    input clk, rst_n,
    output reg [2:0] light  // [2]=Red, [1]=Yellow, [0]=Green
);
    typedef enum reg [1:0] {RED, YELLOW, GREEN} state_t;
    state_t state;
    reg [3:0] counter;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= RED;
            counter <= 0;
        end else begin
            counter <= counter + 1;
            case(state)
                RED: if (counter == 9) begin
                    state <= GREEN;
                    counter <= 0;
                end
                GREEN: if (counter == 9) begin
                    state <= YELLOW;
                    counter <= 0;
                end
                YELLOW: if (counter == 3) begin
                    state <= RED;
                    counter <= 0;
                end
            endcase
        end
    end

    always @(*) begin
        case(state)
            RED:    light = 3'b100;
            YELLOW: light = 3'b010;
            GREEN:  light = 3'b001;
            default: light = 3'b100;
        endcase
    end
endmodule
```

---

## Section 6: Memory Elements

### 31. Simple RAM (16x8)
```verilog
module ram_16x8 (
    input clk, we,
    input [3:0] addr,
    input [7:0] din,
    output reg [7:0] dout
);
    reg [7:0] mem [0:15];

    always @(posedge clk) begin
        if (we)
            mem[addr] <= din;
        dout <= mem[addr];
    end
endmodule
```

### 32. Dual Port RAM
```verilog
module dual_port_ram (
    input clk,
    // Port A
    input we_a,
    input [3:0] addr_a,
    input [7:0] din_a,
    output reg [7:0] dout_a,
    // Port B
    input we_b,
    input [3:0] addr_b,
    input [7:0] din_b,
    output reg [7:0] dout_b
);
    reg [7:0] mem [0:15];

    always @(posedge clk) begin
        if (we_a) mem[addr_a] <= din_a;
        dout_a <= mem[addr_a];
    end

    always @(posedge clk) begin
        if (we_b) mem[addr_b] <= din_b;
        dout_b <= mem[addr_b];
    end
endmodule
```

### 33. Synchronous FIFO (Simple Version)
```verilog
module sync_fifo #(
    parameter DEPTH = 8,
    parameter WIDTH = 8
)(
    input clk, rst_n,
    input wr_en, rd_en,
    input [WIDTH-1:0] wr_data,
    output reg [WIDTH-1:0] rd_data,
    output full, empty
);
    reg [WIDTH-1:0] mem [0:DEPTH-1];
    reg [$clog2(DEPTH):0] wr_ptr, rd_ptr;

    assign full = (wr_ptr[$clog2(DEPTH)] != rd_ptr[$clog2(DEPTH)]) &&
                  (wr_ptr[$clog2(DEPTH)-1:0] == rd_ptr[$clog2(DEPTH)-1:0]);
    assign empty = (wr_ptr == rd_ptr);

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_ptr <= 0;
            rd_ptr <= 0;
        end else begin
            if (wr_en && !full) begin
                mem[wr_ptr[$clog2(DEPTH)-1:0]] <= wr_data;
                wr_ptr <= wr_ptr + 1;
            end
            if (rd_en && !empty) begin
                rd_data <= mem[rd_ptr[$clog2(DEPTH)-1:0]];
                rd_ptr <= rd_ptr + 1;
            end
        end
    end
endmodule
```

---

## Section 7: Miscellaneous (Interview Favorites!)

### 34. Edge Detector (Positive Edge)
```verilog
module edge_detector_pos (
    input clk, rst_n, signal,
    output pulse
);
    reg signal_d;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            signal_d <= 1'b0;
        else
            signal_d <= signal;
    end

    assign pulse = signal & ~signal_d;
endmodule
```

### 35. Pulse Stretcher
```verilog
module pulse_stretcher #(
    parameter STRETCH_CYCLES = 4
)(
    input clk, rst_n, pulse_in,
    output reg pulse_out
);
    reg [$clog2(STRETCH_CYCLES)-1:0] counter;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            counter <= 0;
            pulse_out <= 0;
        end else if (pulse_in) begin
            counter <= STRETCH_CYCLES - 1;
            pulse_out <= 1;
        end else if (counter > 0) begin
            counter <= counter - 1;
            pulse_out <= 1;
        end else
            pulse_out <= 0;
    end
endmodule
```

### 36. Debounce Circuit
```verilog
module debounce (
    input clk, rst_n, button_in,
    output reg button_out
);
    reg [15:0] counter;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            counter <= 0;
            button_out <= 0;
        end else if (button_in != button_out) begin
            counter <= counter + 1;
            if (counter == 16'hFFFF)
                button_out <= button_in;
        end else
            counter <= 0;
    end
endmodule
```

### 37. Clock Divider (Divide by N)
```verilog
module clock_divider #(
    parameter DIV_FACTOR = 4
)(
    input clk_in, rst_n,
    output reg clk_out
);
    reg [$clog2(DIV_FACTOR)-1:0] counter;

    always @(posedge clk_in or negedge rst_n) begin
        if (!rst_n) begin
            counter <= 0;
            clk_out <= 0;
        end else if (counter == DIV_FACTOR/2 - 1) begin
            counter <= 0;
            clk_out <= ~clk_out;
        end else
            counter <= counter + 1;
    end
endmodule
```

### 38. Parameterized Up Counter
```verilog
module param_counter #(
    parameter WIDTH = 8
)(
    input clk, rst_n, en,
    output reg [WIDTH-1:0] count
);
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= 0;
        else if (en)
            count <= count + 1;
    end
endmodule
```

### 39. One-Hot Encoder
```verilog
module one_hot_encoder (
    input [3:0] binary_in,
    output reg [15:0] one_hot_out
);
    always @(*) begin
        one_hot_out = 16'b0;
        one_hot_out[binary_in] = 1'b1;
    end
endmodule
```

### 40. Binary to BCD Converter (4-bit)
```verilog
module bin_to_bcd_4bit (
    input [3:0] binary,
    output reg [3:0] ones,
    output reg [3:0] tens
);
    always @(*) begin
        tens = binary / 10;
        ones = binary % 10;
    end
endmodule
```

---

## Most Asked Interview Patterns

**TOP 5 MOST COMMON:**
1. ✅ 4-bit ALU with multiple operations
2. ✅ Sequence detector FSM (101 or 1011)
3. ✅ BCD counter (Mod-10)
4. ✅ Priority encoder (4:2 or 8:3)
5. ✅ Synchronous FIFO

**COMMON FOLLOW-UP QUESTIONS:**
- Explain blocking vs non-blocking
- How to avoid latches?
- What is synthesis vs simulation mismatch?
- Optimize for area vs speed
- Add testbench for any design

---

*Based on placement exam patterns from Intel, AMD, NVIDIA, Qualcomm, Broadcom, and top semiconductor companies (2024-2025)*
