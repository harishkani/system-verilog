# HDLBits Workbook
## Digital Design with Verilog - Problems, Explanations, and Solutions

---

## Table of Contents

- [Preface](#preface)
- [Chapter 1: Getting Started](#chapter-1-getting-started)
  - [Introduction to Verilog](#introduction-to-verilog)
  - [Basic Gates](#basic-gates)
- [Chapter 2: Verilog Language](#chapter-2-verilog-language)
  - [Vectors](#vectors)
  - [Modules and Hierarchy](#modules-and-hierarchy)
- [Chapter 3: Combinational Logic](#chapter-3-combinational-logic)
  - [Basic Combinational Circuits](#basic-combinational-circuits)
  - [Multiplexers](#multiplexers)
- [Chapter 4: Sequential Logic](#chapter-4-sequential-logic)
  - [Flip-Flops and Latches](#flip-flops-and-latches)
  - [Counters](#counters)
  - [Finite State Machines](#finite-state-machines)
- [Chapter 5: Building Larger Circuits](#chapter-5-building-larger-circuits)
  - [Shift Registers](#shift-registers)
- [Chapter 6: Practice Problems](#chapter-6-practice-problems)
- [Appendix A: Verilog Quick Reference](#appendix-a-verilog-quick-reference)
- [Appendix B: Tips and Best Practices](#appendix-b-tips-and-best-practices)

---

## Preface

This workbook is designed as a comprehensive guide to learning digital design through HDLBits problem sets. Each problem includes:

- **Problem Statement:** Clear description of what needs to be implemented
- **Explanation:** Theoretical background and key concepts
- **Hints:** Guidance to help you solve the problem independently
- **Solution:** Complete working Verilog code with detailed comments

The problems are organized by difficulty and topic, progressing from basic gates to complex sequential circuits.

---

# Chapter 1: Getting Started

## Introduction to Verilog

### 1.1 Simple Wire

#### 📘 Problem
Create a module with one input and one output that acts as a wire connecting them.

**Module Declaration:**
```verilog
module top_module(
    input in,
    output out
);
```

#### 💡 Explanation
In Verilog, an `assign` statement creates a continuous assignment. It's used for combinational logic where the output is always equal to the value of the right-hand side expression. This is the simplest form of combinational logic - a direct connection.

**Key Concepts:**
- Continuous assignment using `assign`
- Module ports (input/output)
- Wire connections

#### 💭 Hint
Use a continuous assignment statement: `assign output_signal = input_signal;`

#### ✅ Solution
```verilog
module top_module(
    input in,
    output out
);
    // Direct connection using continuous assignment
    assign out = in;

endmodule
```

---

### 1.2 Four Wires

#### 📘 Problem
Create a module with 3 inputs and 4 outputs that connects them as follows:
- a connects to w
- b connects to x
- b also connects to y
- c connects to z

**Module Declaration:**
```verilog
module top_module(
    input a, b, c,
    output w, x, y, z
);
```

#### 💡 Explanation
This problem demonstrates that:
- Multiple outputs can be driven by different inputs
- The same input can drive multiple outputs
- Each `assign` statement operates independently

#### ✅ Solution
```verilog
module top_module(
    input a, b, c,
    output w, x, y, z
);
    assign w = a;
    assign x = b;
    assign y = b;  // b drives both x and y
    assign z = c;

endmodule
```

---

### 1.3 Inverter (NOT Gate)

#### 📘 Problem
Create a module that implements a NOT gate (inverter).

**Module Declaration:**
```verilog
module top_module(
    input in,
    output out
);
```

#### 💡 Explanation
The NOT gate inverts its input. In Verilog:
- `!` is the logical NOT operator
- `~` is the bitwise NOT operator
- For single-bit signals, both operators give the same result

#### ✅ Solution
```verilog
module top_module(
    input in,
    output out
);
    assign out = ~in;  // Bitwise NOT
    // OR: assign out = !in;  // Logical NOT

endmodule
```

---

## Basic Gates

### 1.4 AND Gate

#### 📘 Problem
Create a module that implements a 2-input AND gate.

**Module Declaration:**
```verilog
module top_module(
    input a, b,
    output out
);
```

#### 💡 Explanation
The AND gate outputs 1 only when both inputs are 1.

**Truth Table:**
| a | b | out |
|---|---|-----|
| 0 | 0 | 0   |
| 0 | 1 | 0   |
| 1 | 0 | 0   |
| 1 | 1 | 1   |

In Verilog: `&` is bitwise AND, `&&` is logical AND.

#### ✅ Solution
```verilog
module top_module(
    input a, b,
    output out
);
    assign out = a & b;

endmodule
```

---

### 1.5 NOR Gate

#### 📘 Problem
Create a module that implements a 2-input NOR gate.

#### 💡 Explanation
NOR = NOT OR. The output is 1 only when both inputs are 0.

**Truth Table:**
| a | b | out |
|---|---|-----|
| 0 | 0 | 1   |
| 0 | 1 | 0   |
| 1 | 0 | 0   |
| 1 | 1 | 0   |

#### ✅ Solution
```verilog
module top_module(
    input a, b,
    output out
);
    assign out = ~(a | b);  // NOT of OR

endmodule
```

---

### 1.6 XNOR Gate

#### 📘 Problem
Create a module that implements a 2-input XNOR gate (equivalence gate).

#### 💡 Explanation
XNOR outputs 1 when both inputs are equal (both 0 or both 1).

**Truth Table:**
| a | b | out |
|---|---|-----|
| 0 | 0 | 1   |
| 0 | 1 | 0   |
| 1 | 0 | 0   |
| 1 | 1 | 1   |

This is also called the equality operator.

#### ✅ Solution
```verilog
module top_module(
    input a, b,
    output out
);
    assign out = ~(a ^ b);  // NOT of XOR
    // OR: assign out = a ~^ b;  // XNOR operator

endmodule
```

---

# Chapter 2: Verilog Language

## Vectors

### 2.1 Vector Basics

#### 📘 Problem
Build a circuit with one 3-bit input and four outputs:
- `out_vec`: Output the input vector
- `out_bit0`: Output bit 0 of the input
- `out_bit1`: Output bit 1 of the input
- `out_bit2`: Output bit 2 of the input

**Module Declaration:**
```verilog
module top_module (
    input wire [2:0] vec,
    output wire [2:0] out_vec,
    output wire out_bit0,
    output wire out_bit1,
    output wire out_bit2
);
```

#### 💡 Explanation
**Vector Notation in Verilog:**
- `[2:0]` declares a 3-bit vector (bits 2, 1, 0)
- `[0:2]` would also be 3 bits, but with reversed indexing
- Bit selection: `vec[0]` accesses the least significant bit
- Range selection: `vec[2:1]` selects bits 2 and 1

#### ✅ Solution
```verilog
module top_module (
    input wire [2:0] vec,
    output wire [2:0] out_vec,
    output wire out_bit0,
    output wire out_bit1,
    output wire out_bit2
);
    assign out_vec = vec;
    assign out_bit0 = vec[0];
    assign out_bit1 = vec[1];
    assign out_bit2 = vec[2];

endmodule
```

---

### 2.2 Vector Part Select

#### 📘 Problem
A 32-bit vector can be viewed as containing 4 bytes (bits [31:24], [23:16], [15:8], [7:0]).
Build a circuit that reverses the byte ordering of the 4-byte word.

**Example:**
- Input: `AaBbCcDd`
- Output: `DdCcBbAa`

#### 💡 Explanation
**Byte Reversal (Endianness Conversion):**

This is commonly needed when converting between:
- Big-endian: Most significant byte at lowest address
- Little-endian: Least significant byte at lowest address

Use part-select to extract each byte and concatenate in reverse order.

#### ✅ Solution
```verilog
module top_module(
    input [31:0] in,
    output [31:0] out
);
    // Reverse byte ordering using concatenation
    assign out = {in[7:0], in[15:8], in[23:16], in[31:24]};

endmodule
```

---

### 2.3 Bitwise Operators

#### 📘 Problem
Build a circuit that has two 3-bit inputs and produces four 3-bit outputs:
- `out_or`: Bitwise OR of inputs
- `out_and`: Bitwise AND of inputs
- `out_xor`: Bitwise XOR of inputs
- `out_not`: Bitwise NOT of input a

#### 💡 Explanation
**Bitwise vs. Logical Operators:**

- Bitwise: `&`, `|`, `~`, `^` - operate bit-by-bit
- Logical: `&&`, `||`, `!` - treat operands as boolean

Example: `3'b101 & 3'b011 = 3'b001`

#### ✅ Solution
```verilog
module top_module(
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_or,
    output [2:0] out_and,
    output [2:0] out_xor,
    output [2:0] out_not
);
    assign out_or = a | b;
    assign out_and = a & b;
    assign out_xor = a ^ b;
    assign out_not = ~a;

endmodule
```

---

### 2.4 Reduction Operators

#### 📘 Problem
Build a circuit that computes the parity bit of an 8-bit input vector.
The parity bit should be 1 if there's an odd number of 1s in the input.

#### 💡 Explanation
**Reduction Operators:**

Reduction operators perform operation on all bits of a vector:
- `&vec` - AND all bits (all bits are 1?)
- `|vec` - OR all bits (any bit is 1?)
- `^vec` - XOR all bits (odd number of 1s?)

Parity is computed using XOR reduction: `^in`

#### ✅ Solution
```verilog
module top_module(
    input [7:0] in,
    output parity
);
    // XOR reduction - results in 1 for odd number of 1s
    assign parity = ^in;

endmodule
```

---

## Modules and Hierarchy

### 2.5 Module Instantiation

#### 📘 Problem
You are given a module `mod_a` with 2 outputs and 4 inputs:

```verilog
module mod_a (
    output out1, output out2,
    input in1, input in2, input in3, input in4
);
```

Instantiate this module to connect:
- Inputs: a, b, c, d (from top module)
- Outputs: out1, out2 (to top module)

#### 💡 Explanation
**Module Instantiation Methods:**

**1. By Position (order matters):**
```verilog
mod_a instance1 ( out1, out2, in1, in2, in3, in4 );
```

**2. By Name (explicit, preferred):**
```verilog
mod_a instance1 (
    .out1(wire1),
    .in1(wire2)
);
```

#### ✅ Solution
```verilog
module top_module (
    input a, b, c, d,
    output out1, out2
);
    // Named port connection (recommended)
    mod_a instance1 (
        .out1(out1),
        .out2(out2),
        .in1(a),
        .in2(b),
        .in3(c),
        .in4(d)
    );

endmodule
```

---

# Chapter 3: Combinational Logic

## Basic Combinational Circuits

### 3.1 Half Adder

#### 📘 Problem
Create a half adder. A half adder adds two 1-bit numbers and produces:
- `sum`: The sum bit (XOR)
- `cout`: The carry-out bit (AND)

#### 💡 Explanation
**Half Adder Truth Table:**

| a | b | sum | cout |
|---|---|-----|------|
| 0 | 0 | 0   | 0    |
| 0 | 1 | 1   | 0    |
| 1 | 0 | 1   | 0    |
| 1 | 1 | 0   | 1    |

**Logic:**
- Sum = a XOR b (different inputs produce 1)
- Carry = a AND b (both inputs are 1)

#### ✅ Solution
```verilog
module top_module(
    input a, b,
    output cout, sum
);
    assign sum = a ^ b;   // XOR for sum
    assign cout = a & b;  // AND for carry

endmodule
```

---

### 3.2 Full Adder

#### 📘 Problem
Create a full adder. A full adder adds three 1-bit numbers (a, b, cin) and produces:
- `sum`: The sum bit
- `cout`: The carry-out bit

#### 💡 Explanation
**Full Adder:**

A full adder extends the half adder by including a carry-in (`cin`).

**Boolean Equations:**
- sum = a ⊕ b ⊕ cin
- cout = (a & b) | (a & cin) | (b & cin)

Can be built from two half adders and an OR gate.

#### ✅ Solution
```verilog
module top_module(
    input a, b, cin,
    output cout, sum
);
    // Full adder logic
    assign sum = a ^ b ^ cin;
    assign cout = (a & b) | (a & cin) | (b & cin);

    // Alternative using intermediate signals:
    // wire sum_ab, cout_ab, cout_sum;
    // assign sum_ab = a ^ b;
    // assign sum = sum_ab ^ cin;
    // assign cout_ab = a & b;
    // assign cout_sum = sum_ab & cin;
    // assign cout = cout_ab | cout_sum;

endmodule
```

---

### 3.3 3-Bit Binary Adder

#### 📘 Problem
Create a 3-bit binary adder by instantiating three full adders. Chain the carry output of each adder to the carry input of the next.

**Given:**
```verilog
module full_adder(
    input a, b, cin,
    output cout, sum
);
```

#### 💡 Explanation
**Ripple Carry Adder:**

A ripple carry adder chains multiple full adders together:
- Carry propagates from LSB to MSB
- Simple but slower for large bit widths
- Alternative: Carry lookahead adder (faster)

For n-bit addition: connect cout[i] to cin[i+1]

#### ✅ Solution
```verilog
module top_module(
    input [2:0] a, b,
    input cin,
    output [2:0] sum,
    output cout
);
    wire cout0, cout1;  // Intermediate carry signals

    // Instantiate three full adders
    full_adder fa0 (
        .a(a[0]),
        .b(b[0]),
        .cin(cin),
        .sum(sum[0]),
        .cout(cout0)
    );

    full_adder fa1 (
        .a(a[1]),
        .b(b[1]),
        .cin(cout0),
        .sum(sum[1]),
        .cout(cout1)
    );

    full_adder fa2 (
        .a(a[2]),
        .b(b[2]),
        .cin(cout1),
        .sum(sum[2]),
        .cout(cout)
    );

endmodule
```

---

## Multiplexers

### 3.4 2-to-1 Multiplexer

#### 📘 Problem
Create a 2-to-1 multiplexer. When `sel=0`, output `a`. When `sel=1`, output `b`.

#### 💡 Explanation
**Multiplexer (MUX):**

A multiplexer selects one of multiple inputs based on a select signal.

**2-to-1 MUX:**
- 2 data inputs
- 1 select signal
- 1 output

**Boolean equation:** out = (sel' · a) + (sel · b)

Verilog: Use conditional operator `?:`

#### ✅ Solution
```verilog
module top_module(
    input a, b, sel,
    output out
);
    // Ternary operator: condition ? true_value : false_value
    assign out = sel ? b : a;

    // Alternative using case statement:
    // always @(*) begin
    //     case(sel)
    //         1'b0: out = a;
    //         1'b1: out = b;
    //     endcase
    // end

endmodule
```

---

### 3.5 4-to-1 Multiplexer

#### 📘 Problem
Create a 4-to-1 multiplexer with:
- 4 data inputs: a, b, c, d
- 2-bit select: sel[1:0]
- 1 output: out

#### 💡 Explanation
**n-to-1 MUX requires ⌈log₂(n)⌉ select bits**

For 4 inputs: need 2 select bits

| sel[1:0] | out |
|----------|-----|
| 00       | a   |
| 01       | b   |
| 10       | c   |
| 11       | d   |

#### ✅ Solution
```verilog
module top_module(
    input a, b, c, d,
    input [1:0] sel,
    output out
);
    // Using case statement
    always @(*) begin
        case(sel)
            2'b00: out = a;
            2'b01: out = b;
            2'b10: out = c;
            2'b11: out = d;
        endcase
    end

    // Alternative: nested ternary operators
    // assign out = sel[1] ? (sel[0] ? d : c) :
    //                       (sel[0] ? b : a);

endmodule
```

---

# Chapter 4: Sequential Logic

## Flip-Flops and Latches

### 4.1 D Flip-Flop

#### 📘 Problem
Create a D flip-flop that:
- Captures input `d` on the positive edge of `clk`
- Outputs the captured value on `q`

#### 💡 Explanation
**D Flip-Flop:**

The D (Data) flip-flop is the most common flip-flop type:
- Stores one bit of data
- Updates on clock edge (typically positive edge)
- Output follows input after clock edge

**Verilog Coding:**
- Use `always @(posedge clk)` for positive edge
- Use non-blocking assignment `<=` in sequential blocks

#### ✅ Solution
```verilog
module top_module(
    input clk, d,
    output reg q
);
    // D flip-flop: capture d on positive clock edge
    always @(posedge clk) begin
        q <= d;
    end

endmodule
```

---

### 4.2 D Flip-Flop with Reset

#### 📘 Problem
Create a D flip-flop with synchronous reset:
- When `reset=1`, output should be 0 on next clock edge
- Otherwise, capture input `d`

#### 💡 Explanation
**Synchronous vs. Asynchronous Reset:**

**Synchronous Reset:**
- Reset occurs on clock edge
- Included in sensitivity list as a data signal
- Better for FPGA designs

**Asynchronous Reset:**
- Reset occurs immediately
- Added to sensitivity list: `@(posedge clk or posedge reset)`
- Can cause timing issues

#### ✅ Solution
```verilog
module top_module(
    input clk, d, reset,
    output reg q
);
    // Synchronous reset D flip-flop
    always @(posedge clk) begin
        if (reset)
            q <= 1'b0;
        else
            q <= d;
    end

endmodule
```

---

### 4.3 D Flip-Flop with Asynchronous Reset

#### 📘 Problem
Create a D flip-flop with asynchronous active-high reset.

#### ✅ Solution
```verilog
module top_module(
    input clk, d, areset,
    output reg q
);
    // Asynchronous reset D flip-flop
    always @(posedge clk or posedge areset) begin
        if (areset)
            q <= 1'b0;  // Reset immediately
        else
            q <= d;     // Capture on clock edge
    end

endmodule
```

---

### 4.4 8-bit Register

#### 📘 Problem
Create an 8-bit register with:
- Asynchronous reset (active high)
- 8-bit data input and output

#### 💡 Explanation
**Register:**

A register is a group of flip-flops that store multiple bits:
- All flip-flops share the same clock and control signals
- Can be implemented as a vector in Verilog
- Forms the basis of CPU registers, pipeline stages, etc.

#### ✅ Solution
```verilog
module top_module(
    input clk, areset,
    input [7:0] d,
    output reg [7:0] q
);
    // 8-bit register with asynchronous reset
    always @(posedge clk or posedge areset) begin
        if (areset)
            q <= 8'b0;
        else
            q <= d;
    end

endmodule
```

---

## Counters

### 4.5 4-bit Binary Counter

#### 📘 Problem
Create a 4-bit binary counter with:
- Asynchronous reset (active high) to 0
- Counts from 0 to 15, then wraps around

#### 💡 Explanation
**Binary Counter:**

A counter increments its value on each clock cycle:
- n-bit counter: counts from 0 to 2ⁿ-1
- Overflow: automatically wraps using arithmetic overflow
- Used for: timing, addressing, sequencing

**Implementation:** Use `count <= count + 1`

#### ✅ Solution
```verilog
module top_module(
    input clk, areset,
    output reg [3:0] q
);
    // 4-bit binary counter
    always @(posedge clk or posedge areset) begin
        if (areset)
            q <= 4'b0;
        else
            q <= q + 1;  // Increment (wraps automatically)
    end

endmodule
```

---

### 4.6 Decade Counter (BCD)

#### 📘 Problem
Create a decade counter that:
- Counts from 0 to 9
- Resets to 0 after 9
- Has asynchronous reset

#### 💡 Explanation
**Decade Counter (BCD Counter):**

Counts in decimal (0-9) using binary representation:
- Requires explicit check for maximum value
- Used in BCD arithmetic, decimal displays
- 4 bits can represent 0-15, but we use only 0-9

#### ✅ Solution
```verilog
module top_module(
    input clk, areset,
    output reg [3:0] q
);
    // Decade counter (0-9)
    always @(posedge clk or posedge areset) begin
        if (areset)
            q <= 4'b0;
        else if (q == 4'd9)
            q <= 4'b0;  // Reset to 0 after 9
        else
            q <= q + 1;
    end

endmodule
```

---

## Finite State Machines

### 4.7 Simple FSM - Moore Machine

#### 📘 Problem
Implement a 2-state Moore FSM with:
- States: A, B
- Input: `in`
- Output: `out` (1 in state B, 0 in state A)
- Transitions: A→B when in=1, B→A when in=0
- Reset to state A

#### 💡 Explanation
**Moore vs. Mealy FSM:**

**Moore Machine:**
- Output depends only on current state
- Outputs are registered (synchronized with clock)
- More stable, glitch-free

**Mealy Machine:**
- Output depends on current state and inputs
- Can have fewer states
- Outputs may have glitches

**FSM Coding Style:**
Use separate always blocks for:
1. State register (sequential)
2. Next state logic (combinational)
3. Output logic (combinational for Mealy, can be either for Moore)

#### ✅ Solution
```verilog
module top_module(
    input clk, areset, in,
    output out
);
    // State encoding
    parameter A = 1'b0, B = 1'b1;

    reg state, next_state;

    // State register (sequential logic)
    always @(posedge clk or posedge areset) begin
        if (areset)
            state <= A;
        else
            state <= next_state;
    end

    // Next state logic (combinational)
    always @(*) begin
        case (state)
            A: next_state = in ? B : A;
            B: next_state = in ? B : A;
            default: next_state = A;
        endcase
    end

    // Output logic (Moore: depends only on state)
    assign out = (state == B);

endmodule
```

---

### 4.8 Sequence Detector (Mealy)

#### 📘 Problem
Implement a Mealy machine that detects the sequence "101":
- Input: serial bit stream `in`
- Output: `out` = 1 when "101" detected
- Overlapping sequences allowed

#### 💡 Explanation
**Sequence Detector FSM:**

States represent "how much of the sequence we've seen":
- S0: Initial / no match
- S1: Seen "1"
- S2: Seen "10"
- S3: Seen "101" (output 1)

For overlapping: after "101", "01" is already seen for next match.

#### ✅ Solution
```verilog
module top_module(
    input clk, areset, in,
    output reg out
);
    // State encoding
    parameter S0=2'b00, S1=2'b01, S2=2'b10;

    reg [1:0] state, next_state;

    // State register
    always @(posedge clk or posedge areset) begin
        if (areset)
            state <= S0;
        else
            state <= next_state;
    end

    // Next state logic
    always @(*) begin
        case (state)
            S0: next_state = in ? S1 : S0;
            S1: next_state = in ? S1 : S2;
            S2: next_state = in ? S1 : S0;
            default: next_state = S0;
        endcase
    end

    // Output logic (Mealy: depends on state and input)
    always @(*) begin
        case (state)
            S2: out = in;  // Output 1 when in S2 and in=1
            default: out = 0;
        endcase
    end

endmodule
```

---

# Chapter 5: Building Larger Circuits

## Shift Registers

### 5.1 4-bit Shift Register

#### 📘 Problem
Build a 4-bit shift register with:
- Serial input `in`
- Parallel output `q[3:0]`
- Shifts left (q[3] gets new data, q[0] is shifted out)
- Asynchronous reset

#### 💡 Explanation
**Shift Register:**

A shift register moves data one position on each clock:
- Serial-in, Parallel-out (SIPO)
- Parallel-in, Serial-out (PISO)
- Universal shift register (both directions)

**Applications:**
- Serial communication
- Delay lines
- Pseudo-random number generation (LFSR)

#### ✅ Solution
```verilog
module top_module(
    input clk, areset, in,
    output reg [3:0] q
);
    // 4-bit left shift register
    always @(posedge clk or posedge areset) begin
        if (areset)
            q <= 4'b0;
        else
            q <= {q[2:0], in};  // Shift left, insert new bit
    end

endmodule
```

---

### 5.2 LFSR (Linear Feedback Shift Register)

#### 📘 Problem
Build a 5-bit Galois LFSR with taps at positions 5 and 3:
- Generates pseudo-random sequence
- Feedback polynomial: x⁵ + x³ + 1
- Reset to `5'h1`

#### 💡 Explanation
**LFSR (Linear Feedback Shift Register):**

An LFSR generates pseudo-random numbers using XOR feedback:

**Types:**
- **Fibonacci:** XORs happen before the register
- **Galois:** XORs happen along the shift path

**Properties:**
- Maximum sequence length: 2ⁿ-1 (with proper taps)
- Deterministic but appears random
- Used in: CRC, scrambling, testing

#### ✅ Solution
```verilog
module top_module(
    input clk, areset,
    output reg [4:0] q
);
    // 5-bit Galois LFSR with taps at 5 and 3
    always @(posedge clk or posedge areset) begin
        if (areset)
            q <= 5'h1;
        else begin
            q[4] <= q[0];           // Shift from LSB
            q[3] <= q[4];
            q[2] <= q[3] ^ q[0];    // XOR tap at position 3
            q[1] <= q[2];
            q[0] <= q[1] ^ q[0];    // XOR tap at position 1
        end
    end

endmodule
```

---

# Chapter 6: Practice Problems

## Challenge Problems

### 6.1 7-Segment Display Decoder

#### 📘 Problem
Create a BCD to 7-segment display decoder:
- Input: 4-bit BCD (0-9)
- Output: 7 segments [6:0] (a-g)
- Active high outputs
- Segment order: gfedcba

**Segment Layout:**
```
  aaa
 f   b
  ggg
 e   c
  ddd
```

#### 💡 Explanation
**7-Segment Display:**

Each digit requires a specific pattern:
- 0: segments a,b,c,d,e,f
- 1: segments b,c
- 8: all segments

Implementation options:
- Case statement (clear and maintainable)
- Truth table with assign statements
- ROM/LUT

#### ✅ Solution
```verilog
module top_module(
    input [3:0] bcd,
    output reg [6:0] seg  // seg[6]=g, seg[0]=a
);
    always @(*) begin
        case(bcd)
            4'd0: seg = 7'b0111111;  // 0
            4'd1: seg = 7'b0000110;  // 1
            4'd2: seg = 7'b1011011;  // 2
            4'd3: seg = 7'b1001111;  // 3
            4'd4: seg = 7'b1100110;  // 4
            4'd5: seg = 7'b1101101;  // 5
            4'd6: seg = 7'b1111101;  // 6
            4'd7: seg = 7'b0000111;  // 7
            4'd8: seg = 7'b1111111;  // 8
            4'd9: seg = 7'b1101111;  // 9
            default: seg = 7'b0000000;  // blank
        endcase
    end

endmodule
```

---

### 6.2 Priority Encoder

#### 📘 Problem
Create an 8-bit priority encoder:
- Input: 8-bit vector `in[7:0]`
- Output: 3-bit position `pos[2:0]` of highest priority 1
- Output: `valid` = 1 if any bit is set
- Priority: bit 7 (MSB) has highest priority

#### 💡 Explanation
**Priority Encoder:**

Finds the position of the highest-priority active input:
- Opposite of decoder
- Multiple inputs can be active
- Outputs position of highest-priority active input
- Used in interrupt controllers

**Example:**
- Input: 8'b00010100
- Output: pos=3'd4 (highest 1 is at bit 4)

#### ✅ Solution
```verilog
module top_module(
    input [7:0] in,
    output reg [2:0] pos,
    output reg valid
);
    always @(*) begin
        valid = |in;  // Any bit set?

        // Priority encoder: check from MSB to LSB
        casez (in)
            8'b1???????: pos = 3'd7;
            8'b01??????: pos = 3'd6;
            8'b001?????: pos = 3'd5;
            8'b0001????: pos = 3'd4;
            8'b00001???: pos = 3'd3;
            8'b000001??: pos = 3'd2;
            8'b0000001?: pos = 3'd1;
            8'b00000001: pos = 3'd0;
            default:     pos = 3'd0;
        endcase
    end

endmodule
```

---

# Appendix A: Verilog Quick Reference

## Data Types

```verilog
// Nets (continuous assignment)
wire        // Single bit wire
wire [7:0]  // 8-bit vector wire

// Variables (procedural assignment)
reg         // Single bit register
reg [7:0]   // 8-bit register

// SystemVerilog
logic [7:0] // Can be used anywhere
```

## Operators

| Operator | Description |
|----------|-------------|
| `&, |, ^, ~` | Bitwise AND, OR, XOR, NOT |
| `&&, ||, !` | Logical AND, OR, NOT |
| `==, !=` | Equality, inequality |
| `<, >, <=, >=` | Relational operators |
| `<<, >>` | Shift left, shift right |
| `+, -, *, /` | Arithmetic operators |
| `?:` | Conditional (ternary) |
| `{}` | Concatenation |
| `{n{x}}` | Replication |

## Always Blocks

```verilog
// Combinational logic
always @(*) begin
    // Use blocking assignments =
end

// Sequential logic (positive edge)
always @(posedge clk) begin
    // Use non-blocking assignments <=
end

// Async reset
always @(posedge clk or posedge areset) begin
    if (areset)
        // reset logic
    else
        // normal logic
end
```

---

# Appendix B: Tips and Best Practices

## Coding Guidelines

1. **Use meaningful names:** `counter` not `c`
2. **Blocking vs. Non-blocking:**
   - Combinational: use `=`
   - Sequential: use `<=`
3. **Complete sensitivity lists:** Use `@(*)` for combinational
4. **Avoid latches:** Assign all outputs in all branches
5. **Default cases:** Always include in case statements
6. **Synchronous design:** Minimize asynchronous logic
7. **One clock per module:** Simplifies timing analysis
8. **Named port connections:** More maintainable than positional

## Common Pitfalls

1. **Missing else clause:** Creates unwanted latches
2. **Mixing blocking and non-blocking:** Causes simulation/synthesis mismatch
3. **Incomplete sensitivity list:** Causes simulation errors
4. **Using delays in synthesizable code:** `#10` not synthesizable
5. **X and Z in synthesis:** Only for simulation

## Debugging Tips

1. **Simulate before synthesize**
2. **Check for warnings:** They're usually important
3. **Use assertions:** Catch errors early
4. **Waveform analysis:** Visual debugging
5. **Divide and conquer:** Test modules independently

---

## Index

- Always block
- AND gate
- Asynchronous reset
- Blocking assignment
- Combinational logic
- Counter
- D flip-flop
- Finite State Machine
- Full adder
- Half adder
- LFSR
- Module instantiation
- Multiplexer
- Non-blocking assignment
- OR gate
- Priority encoder
- Reduction operators
- Register
- Sequential logic
- Shift register
- Synchronous reset
- Vector
- XOR gate

---

**End of Workbook**

*For more problems and interactive practice, visit [HDLBits](https://hdlbits.01xz.net/)*
