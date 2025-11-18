# Finite State Machines (FSM) - Complete Guide
### From Beginner to Advanced Mastery

---

## Table of Contents
1. [Introduction](#1-introduction)
2. [What is a Finite State Machine?](#2-what-is-a-finite-state-machine)
3. [Real-Life Examples](#3-real-life-examples)
4. [Basic Components of FSM](#4-basic-components-of-fsm)
5. [Types of FSMs](#5-types-of-fsms)
6. [FSM Representation Methods](#6-fsm-representation-methods)
7. [Simple Examples - Step by Step](#7-simple-examples---step-by-step)
8. [SystemVerilog Implementation Basics](#8-systemverilog-implementation-basics)
9. [Coding Styles for FSMs](#9-coding-styles-for-fsms)
10. [Intermediate Examples](#10-intermediate-examples)
11. [Advanced FSM Concepts](#11-advanced-fsm-concepts)
12. [Advanced Examples](#12-advanced-examples)
13. [FSM Design Best Practices](#13-fsm-design-best-practices)
14. [Common Pitfalls and How to Avoid Them](#14-common-pitfalls-and-how-to-avoid-them)
15. [Debugging FSMs](#15-debugging-fsms)
16. [Practice Problems](#16-practice-problems)
17. [Summary and Next Steps](#17-summary-and-next-steps)

---

## 1. Introduction

Welcome to the comprehensive guide on Finite State Machines (FSMs)! Whether you're a complete beginner or looking to master advanced concepts, this guide will take you through everything you need to know about FSMs, with a special focus on digital design and SystemVerilog implementation.

### Why Learn FSMs?

- **Universal Concept**: FSMs are used in computer science, digital design, software engineering, and many other fields
- **Hardware Design**: Essential for designing control logic in digital circuits
- **Problem Solving**: Provides a structured way to solve sequential logic problems
- **Industry Standard**: Used extensively in ASIC/FPGA design, protocol implementations, and embedded systems

---

## 2. What is a Finite State Machine?

### Simple Definition

A **Finite State Machine (FSM)** is a mathematical model of computation that can be in exactly **one** of a **finite** number of **states** at any given time. It can change from one state to another in response to some inputs; the change from one state to another is called a **transition**.

Think of it as a system that:
1. Has a limited (finite) number of conditions or "states"
2. Can be in only ONE state at a time
3. Changes states based on inputs/events
4. Produces outputs based on current state and/or inputs

### Analogy: A Light Switch

Imagine a simple light switch:
- **States**: ON, OFF (2 states)
- **Input**: Press the switch
- **Transitions**:
  - If current state is OFF and you press → go to ON
  - If current state is ON and you press → go to OFF
- **Output**: Light is lit (when ON) or dark (when OFF)

This is one of the simplest FSMs!

---

## 3. Real-Life Examples

Before diving into technical details, let's understand FSMs through everyday examples:

### Example 1: Traffic Light System

**States**:
- RED
- YELLOW
- GREEN

**Transitions**:
- RED → GREEN (after timer expires)
- GREEN → YELLOW (after timer expires)
- YELLOW → RED (after timer expires)

**Inputs**: Timer signals
**Outputs**: Which light is illuminated

### Example 2: Vending Machine

**States**:
- IDLE (0 cents inserted)
- CENTS_25 (25 cents inserted)
- CENTS_50 (50 cents inserted)
- DISPENSE (enough money to dispense item)

**Inputs**: Coin insertion (nickel, dime, quarter)
**Outputs**: Dispense item, return change, display amount

### Example 3: Door Lock System

**States**:
- LOCKED
- UNLOCKED
- ALARM

**Inputs**: Correct code, wrong code, timeout
**Transitions**:
- LOCKED → UNLOCKED (correct code entered)
- LOCKED → ALARM (wrong code 3 times)
- UNLOCKED → LOCKED (timeout or user locks)

### Example 4: Smartphone Screen

**States**:
- SCREEN_OFF
- SCREEN_ON_LOCKED
- SCREEN_ON_UNLOCKED
- SCREEN_DIM

**Inputs**: Power button press, touch input, face recognition, timeout

### Example 5: Washing Machine

**States**:
- IDLE
- FILLING
- WASHING
- RINSING
- SPINNING
- COMPLETE

**Inputs**: Start button, water level sensor, timer
**Outputs**: Motor control, valve control, display status

---

## 4. Basic Components of FSM

Every FSM consists of the following components:

### 4.1 States (S)
- A finite set of conditions the system can be in
- Represented by circles in state diagrams
- Must have at least one state
- Example: {IDLE, RUNNING, STOPPED}

### 4.2 Inputs/Events (I)
- Signals or events that trigger transitions
- Can be external (user input) or internal (timer, sensor)
- Example: {start_button, stop_button, reset}

### 4.3 Outputs (O)
- Signals or actions produced by the FSM
- Can depend on state only (Moore) or state+input (Mealy)
- Example: {motor_on, alarm_sound, led_green}

### 4.4 Transitions (δ - delta)
- Rules for changing from one state to another
- Defined by: Current State + Input → Next State
- Represented by arrows in state diagrams

### 4.5 Initial State (S₀)
- The state the FSM starts in when powered on or reset
- Usually marked with an arrow pointing to it
- Example: IDLE or RESET state

### 4.6 Current State
- The state the FSM is currently in
- Only ONE state can be current at any time
- Stored in state registers in hardware

---

## 5. Types of FSMs

There are two main types of FSMs based on how they generate outputs:

### 5.1 Moore Machine

**Definition**: Output depends ONLY on the current state.

**Characteristics**:
- Outputs are associated with states
- Outputs change only on state transitions (synchronized with clock)
- Generally more stable and glitch-free
- May require more states than Mealy machines

**Example**: Traffic light - the light color depends only on which state you're in.

```
State: RED    → Output: Red light ON
State: GREEN  → Output: Green light ON
State: YELLOW → Output: Yellow light ON
```

**State Diagram Notation**:
```
   ┌─────────────┐
   │   STATE     │
   │   ------    │
   │   output    │
   └─────────────┘
```

### 5.2 Mealy Machine

**Definition**: Output depends on BOTH current state AND current input.

**Characteristics**:
- Outputs are associated with transitions
- Can respond faster to inputs (combinational output)
- May use fewer states than Moore machines
- More susceptible to glitches

**Example**: Vending machine - output (dispense) depends on both current money state AND new coin input.

**State Diagram Notation**:
```
         input / output
   ───────────────────────→
```

### Comparison Table

| Feature | Moore Machine | Mealy Machine |
|---------|---------------|---------------|
| Output depends on | Current state only | Current state + Input |
| Output changes | With clock (state change) | Can change immediately with input |
| Glitches | Less prone | More prone |
| Number of states | May need more | Usually fewer |
| Design complexity | Simpler | More complex |
| Response time | Slower (one clock cycle) | Faster (combinational) |

### Which to Use?

- **Use Moore** when:
  - You need glitch-free outputs
  - Outputs should be synchronized with clock
  - Simplicity is important
  - State-based actions are natural

- **Use Mealy** when:
  - You need faster response
  - You want to minimize states
  - Outputs are naturally event-driven
  - You can handle potential glitches

---

## 6. FSM Representation Methods

FSMs can be represented in several ways:

### 6.1 State Diagram (Graphical)

The most intuitive representation:

**Moore Machine Example**:
```
                    input=1
    ┌────────┐                 ┌────────┐
    │   S0   │────────────────>│   S1   │
    │output=0│                 │output=1│
    └────────┘                 └────────┘
        ^                           │
        │        input=0            │
        └───────────────────────────┘
```

**Mealy Machine Example**:
```
                 input=1/output=1
    ┌────────┐                      ┌────────┐
    │   S0   │─────────────────────>│   S1   │
    │        │                      │        │
    └────────┘                      └────────┘
        ^                                │
        │      input=0/output=0          │
        └────────────────────────────────┘
```

### 6.2 State Table (Tabular)

A table showing all transitions:

**For Moore Machine**:
| Current State | Input | Next State | Output |
|---------------|-------|------------|--------|
| S0            | 0     | S0         | 0      |
| S0            | 1     | S1         | 0      |
| S1            | 0     | S0         | 1      |
| S1            | 1     | S1         | 1      |

**For Mealy Machine**:
| Current State | Input | Next State | Output |
|---------------|-------|------------|--------|
| S0            | 0     | S0         | 0      |
| S0            | 1     | S1         | 1      |
| S1            | 0     | S0         | 0      |
| S1            | 1     | S1         | 1      |

### 6.3 State Transition Table

Simplified table format:

| Current State | Next State (Input=0) | Next State (Input=1) |
|---------------|---------------------|---------------------|
| S0            | S0                  | S1                  |
| S1            | S0                  | S1                  |

### 6.4 ASM (Algorithmic State Machine) Chart

Used in digital design, similar to flowchart:
- State boxes (rectangles)
- Decision boxes (diamonds)
- Conditional output boxes

---

## 7. Simple Examples - Step by Step

Let's build understanding with simple examples, solving them step by step.

### Example 7.1: Simple 1-bit Sequence Detector (Detect '1')

**Problem**: Design an FSM that outputs '1' when input is '1', else outputs '0'.

**Step 1: Understand Requirements**
- Input: 1-bit serial data
- Output: 1 when input is 1, else 0
- This is essentially a wire, but let's design it as FSM for learning

**Step 2: Identify States**
We actually need only 1 state since there's no sequence to remember.
- State: S0 (only state)

**Step 3: Define Transitions**
- S0 with input=0 → stay in S0, output=0
- S0 with input=1 → stay in S0, output=1

**Step 4: This is a Mealy Machine** (output depends on input)

**State Diagram**:
```
           input=0/output=0
              ┌──────┐
              ↓      │
         ┌────────┐  │
    ────>│   S0   │──┘
         └────────┘
              ^  │
              └──┘
           input=1/output=1
```

### Example 7.2: Toggle Detection (Moore Machine)

**Problem**: Design an FSM with output that toggles between 0 and 1 on every input '1'. Input '0' has no effect.

**Step 1: Understand**
- Start with output = 0
- Every time input=1, toggle output
- Input=0 does nothing

**Step 2: Identify States**
We need 2 states to remember which output to produce:
- S0: Output is 0
- S1: Output is 1

**Step 3: Define Transitions**
- S0 with input=0 → stay in S0
- S0 with input=1 → go to S1
- S1 with input=0 → stay in S1
- S1 with input=1 → go to S0

**Step 4: State Diagram** (Moore Machine)
```
         input=1              input=1
    ┌────────┐           ┌────────┐
    │   S0   │──────────>│   S1   │
    │output=0│           │output=1│
    └────────┘           └────────┘
        ^                     │
        │      input=0        │
        │<────────────────────┘
        │                     │
        └─────────┘           │
        input=0               │
                    input=0   │
                    ──────────┘
```

Simplified:
```
              input=1
    ┌────────┐      ┌────────┐
    │   S0   │─────>│   S1   │
    │out = 0 │      │out = 1 │
    └────────┘      └────────┘
        ^               │
        │               │
        └───────────────┘
            input=1
```

### Example 7.3: Sequence Detector - "101"

**Problem**: Design a Moore FSM that detects the sequence "101" in a serial bit stream. Output should be '1' when sequence is detected.

**Step 1: Understand**
- Need to remember what we've seen so far
- When we see complete "101", output 1

**Step 2: Identify States**
- IDLE: Haven't seen anything useful yet
- GOT_1: Seen '1'
- GOT_10: Seen '10'
- GOT_101: Seen '101' (output = 1)

**Step 3: Define Transitions**
From IDLE:
- input=0 → stay in IDLE
- input=1 → go to GOT_1

From GOT_1:
- input=0 → go to GOT_10
- input=1 → stay in GOT_1 (still have one '1')

From GOT_10:
- input=0 → go to IDLE (broken sequence)
- input=1 → go to GOT_101 (complete!)

From GOT_101:
- input=0 → go to GOT_10 (the '0' could be middle of new pattern)
- input=1 → go to GOT_1 (the '1' could be start of new pattern)

**Step 4: State Table**

| Current State | Input=0 | Input=1 | Output |
|---------------|---------|---------|--------|
| IDLE          | IDLE    | GOT_1   | 0      |
| GOT_1         | GOT_10  | GOT_1   | 0      |
| GOT_10        | IDLE    | GOT_101 | 0      |
| GOT_101       | GOT_10  | GOT_1   | 1      |

**Step 5: State Diagram**
```
                    1                 0                 1
       ┌────────┐  →  ┌────────┐  →  ┌────────┐  →  ┌────────┐
  ────>│  IDLE  │     │ GOT_1  │     │ GOT_10 │     │GOT_101 │
       │out = 0 │     │out = 0 │     │out = 0 │     │out = 1 │
       └────────┘     └────────┘     └────────┘     └────────┘
            ^  │           ^ │            │               │
            │  └───────────┘ │            │               │
            │       1        │            │               │
            │                │            │   1           │ 0
            └────────────────┘            └───────────────┘
                    0
```

**Step 6: Test with Input Sequence**

Input sequence: 1 1 0 1 0 1 0 1

| Clock | Input | Current State | Next State | Output |
|-------|-------|---------------|------------|--------|
| 0     | -     | IDLE          | IDLE       | 0      |
| 1     | 1     | IDLE          | GOT_1      | 0      |
| 2     | 1     | GOT_1         | GOT_1      | 0      |
| 3     | 0     | GOT_1         | GOT_10     | 0      |
| 4     | 1     | GOT_10        | GOT_101    | 0      |
| 5     | 0     | GOT_101       | GOT_10     | 1 ✓    |
| 6     | 1     | GOT_10        | GOT_101    | 0      |
| 7     | 0     | GOT_101       | GOT_10     | 1 ✓    |
| 8     | 1     | GOT_10        | GOT_101    | 0      |

We detected "101" at clocks 5 and 7! ✓

---

## 8. SystemVerilog Implementation Basics

Now let's learn how to implement FSMs in SystemVerilog/Verilog.

### 8.1 Basic Structure

Every FSM in hardware needs:
1. **State register** - stores current state
2. **Next state logic** - combinational logic to determine next state
3. **Output logic** - generates outputs (combinational or registered)

### 8.2 State Encoding

States must be encoded as binary values:

**Binary Encoding**:
```systemverilog
typedef enum logic [1:0] {
    IDLE   = 2'b00,
    STATE1 = 2'b01,
    STATE2 = 2'b10,
    STATE3 = 2'b11
} state_t;
```

**One-Hot Encoding** (one bit per state):
```systemverilog
typedef enum logic [3:0] {
    IDLE   = 4'b0001,
    STATE1 = 4'b0010,
    STATE2 = 4'b0100,
    STATE3 = 4'b1000
} state_t;
```

**Gray Encoding** (only one bit changes between states):
```systemverilog
typedef enum logic [1:0] {
    IDLE   = 2'b00,
    STATE1 = 2'b01,
    STATE2 = 2'b11,
    STATE3 = 2'b10
} state_t;
```

### 8.3 Simple Example: Toggle FSM in SystemVerilog

Let's implement Example 7.2 (Toggle Detection):

```systemverilog
module toggle_fsm (
    input  logic clk,
    input  logic rst_n,    // Active low reset
    input  logic toggle,   // Input to toggle
    output logic out       // Output
);

    // State definition
    typedef enum logic {
        S0 = 1'b0,
        S1 = 1'b1
    } state_t;

    state_t current_state, next_state;

    // State register (sequential logic)
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            current_state <= S0;
        else
            current_state <= next_state;
    end

    // Next state logic (combinational)
    always_comb begin
        case (current_state)
            S0: begin
                if (toggle)
                    next_state = S1;
                else
                    next_state = S0;
            end

            S1: begin
                if (toggle)
                    next_state = S0;
                else
                    next_state = S1;
            end

            default: next_state = S0;
        endcase
    end

    // Output logic (Moore machine - depends on state only)
    always_comb begin
        case (current_state)
            S0: out = 1'b0;
            S1: out = 1'b1;
            default: out = 1'b0;
        endcase
    end

endmodule
```

### 8.4 Explanation of the Code

**1. Module Interface:**
```systemverilog
module toggle_fsm (
    input  logic clk,      // Clock signal
    input  logic rst_n,    // Reset (active low)
    input  logic toggle,   // Input
    output logic out       // Output
);
```

**2. State Type Definition:**
```systemverilog
typedef enum logic {
    S0 = 1'b0,
    S1 = 1'b1
} state_t;
```
This creates a new type `state_t` with two states.

**3. State Variables:**
```systemverilog
state_t current_state, next_state;
```
- `current_state`: Holds the present state (registered)
- `next_state`: Holds the next state to transition to (combinational)

**4. State Register (Sequential Block):**
```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        current_state <= S0;  // Reset to initial state
    else
        current_state <= next_state;  // Normal operation
end
```
This is the **only sequential part** - it updates the state register on clock edge.

**5. Next State Logic (Combinational Block):**
```systemverilog
always_comb begin
    case (current_state)
        S0: next_state = toggle ? S1 : S0;
        S1: next_state = toggle ? S0 : S1;
        default: next_state = S0;
    endcase
end
```
Determines what the next state should be based on current state and inputs.

**6. Output Logic (Combinational Block):**
```systemverilog
always_comb begin
    case (current_state)
        S0: out = 1'b0;
        S1: out = 1'b1;
        default: out = 1'b0;
    endcase
end
```
For Moore machine, output depends only on current state.

---

## 9. Coding Styles for FSMs

There are three common coding styles for FSMs in SystemVerilog:

### Style 1: Three Always Blocks (Most Common & Recommended)

**Structure:**
- Always block 1: State register (sequential)
- Always block 2: Next state logic (combinational)
- Always block 3: Output logic (combinational)

**Advantages:**
- Clear separation of concerns
- Easy to understand and debug
- Follows standard FSM model
- Best for Moore machines

**Example:**
```systemverilog
module fsm_3_block (
    input  logic clk, rst_n, input_signal,
    output logic output_signal
);
    typedef enum logic [1:0] {IDLE, ACTIVE, DONE} state_t;
    state_t current_state, next_state;

    // Block 1: State register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            current_state <= IDLE;
        else
            current_state <= next_state;
    end

    // Block 2: Next state logic
    always_comb begin
        next_state = current_state; // Default
        case (current_state)
            IDLE:   if (input_signal) next_state = ACTIVE;
            ACTIVE: next_state = DONE;
            DONE:   next_state = IDLE;
        endcase
    end

    // Block 3: Output logic
    always_comb begin
        case (current_state)
            IDLE:   output_signal = 1'b0;
            ACTIVE: output_signal = 1'b1;
            DONE:   output_signal = 1'b0;
        endcase
    end
endmodule
```

### Style 2: Two Always Blocks

**Structure:**
- Always block 1: State register (sequential)
- Always block 2: Combined next state + output logic (combinational)

**Advantages:**
- Slightly more compact
- Good for Mealy machines
- Fewer lines of code

**Example:**
```systemverilog
module fsm_2_block (
    input  logic clk, rst_n, input_signal,
    output logic output_signal
);
    typedef enum logic [1:0] {IDLE, ACTIVE, DONE} state_t;
    state_t current_state, next_state;

    // Block 1: State register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            current_state <= IDLE;
        else
            current_state <= next_state;
    end

    // Block 2: Next state and output logic combined
    always_comb begin
        // Defaults
        next_state = current_state;
        output_signal = 1'b0;

        case (current_state)
            IDLE: begin
                if (input_signal) begin
                    next_state = ACTIVE;
                    output_signal = 1'b0;
                end
            end

            ACTIVE: begin
                next_state = DONE;
                output_signal = 1'b1;
            end

            DONE: begin
                next_state = IDLE;
                output_signal = 1'b0;
            end
        endcase
    end
endmodule
```

### Style 3: One Always Block (Not Recommended)

**Structure:**
- Single sequential block containing everything

**Disadvantages:**
- Hard to verify timing
- Outputs may be delayed by one clock
- Difficult to distinguish Moore vs Mealy
- Not recommended for synthesis

**Example (for reference only):**
```systemverilog
module fsm_1_block (
    input  logic clk, rst_n, input_signal,
    output logic output_signal
);
    typedef enum logic [1:0] {IDLE, ACTIVE, DONE} state_t;
    state_t current_state;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_state <= IDLE;
            output_signal <= 1'b0;
        end else begin
            case (current_state)
                IDLE: begin
                    if (input_signal) begin
                        current_state <= ACTIVE;
                        output_signal <= 1'b1;
                    end
                end
                ACTIVE: begin
                    current_state <= DONE;
                    output_signal <= 1'b0;
                end
                DONE: begin
                    current_state <= IDLE;
                    output_signal <= 1'b0;
                end
            endcase
        end
    end
endmodule
```

### Recommendation

**Use Style 1 (Three Always Blocks)** for:
- Moore machines (most cases)
- Clean, maintainable code
- Easy debugging
- Industry standard

**Use Style 2 (Two Always Blocks)** for:
- Mealy machines
- When next state and output are closely related

**Avoid Style 3** unless you have specific requirements.

---

## 10. Intermediate Examples

### Example 10.1: Sequence Detector "101" in SystemVerilog

Let's implement Example 7.3 in hardware:

```systemverilog
module sequence_detector_101 (
    input  logic clk,
    input  logic rst_n,
    input  logic data_in,
    output logic detected
);
    // State encoding
    typedef enum logic [1:0] {
        IDLE    = 2'b00,
        GOT_1   = 2'b01,
        GOT_10  = 2'b10,
        GOT_101 = 2'b11
    } state_t;

    state_t current_state, next_state;

    // State register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            current_state <= IDLE;
        else
            current_state <= next_state;
    end

    // Next state logic
    always_comb begin
        case (current_state)
            IDLE: begin
                if (data_in)
                    next_state = GOT_1;
                else
                    next_state = IDLE;
            end

            GOT_1: begin
                if (data_in)
                    next_state = GOT_1;  // Stay, still have a '1'
                else
                    next_state = GOT_10;
            end

            GOT_10: begin
                if (data_in)
                    next_state = GOT_101;
                else
                    next_state = IDLE;
            end

            GOT_101: begin
                if (data_in)
                    next_state = GOT_1;  // This '1' could start new pattern
                else
                    next_state = GOT_10; // This '0' could be middle of new pattern
            end

            default: next_state = IDLE;
        endcase
    end

    // Output logic (Moore machine)
    assign detected = (current_state == GOT_101);

endmodule
```

**Testbench:**
```systemverilog
module tb_sequence_detector_101;
    logic clk, rst_n, data_in, detected;

    // Instantiate DUT
    sequence_detector_101 dut (.*);

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Test stimulus
    initial begin
        // Reset
        rst_n = 0;
        data_in = 0;
        @(posedge clk);
        rst_n = 1;

        // Test sequence: 1_1_0_1_0_1
        @(posedge clk) data_in = 1;
        @(posedge clk) data_in = 1;
        @(posedge clk) data_in = 0;
        @(posedge clk) data_in = 1;  // Should detect here
        @(posedge clk) begin
            if (detected)
                $display("✓ Detected 101 at time %0t", $time);
            else
                $display("✗ Failed to detect");
            data_in = 0;
        end
        @(posedge clk) data_in = 1;  // Should detect again
        @(posedge clk) begin
            if (detected)
                $display("✓ Detected 101 at time %0t", $time);
            data_in = 0;
        end

        #50 $finish;
    end

    // Monitor
    initial begin
        $monitor("Time=%0t rst_n=%b data_in=%b state=%s detected=%b",
                 $time, rst_n, data_in, dut.current_state.name(), detected);
    end
endmodule
```

### Example 10.2: Traffic Light Controller

A more practical example:

```systemverilog
module traffic_light (
    input  logic clk,
    input  logic rst_n,
    input  logic sensor,      // Car detected on side road
    output logic [2:0] lights // {Red, Yellow, Green}
);
    // State encoding
    typedef enum logic [1:0] {
        GREEN  = 2'b00,
        YELLOW = 2'b01,
        RED    = 2'b10
    } state_t;

    state_t current_state, next_state;
    logic [3:0] counter;  // Timer counter

    // Parameters for timing (in clock cycles)
    parameter GREEN_TIME  = 10;
    parameter YELLOW_TIME = 3;
    parameter RED_TIME    = 10;

    // State register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            current_state <= GREEN;
        else
            current_state <= next_state;
    end

    // Timer counter
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            counter <= 0;
        else if (current_state != next_state)
            counter <= 0;  // Reset counter on state change
        else
            counter <= counter + 1;
    end

    // Next state logic
    always_comb begin
        next_state = current_state; // Default: stay in current state

        case (current_state)
            GREEN: begin
                if (counter >= GREEN_TIME && sensor)
                    next_state = YELLOW;
            end

            YELLOW: begin
                if (counter >= YELLOW_TIME)
                    next_state = RED;
            end

            RED: begin
                if (counter >= RED_TIME)
                    next_state = GREEN;
            end

            default: next_state = GREEN;
        endcase
    end

    // Output logic
    always_comb begin
        case (current_state)
            GREEN:  lights = 3'b001;  // Green on
            YELLOW: lights = 3'b010;  // Yellow on
            RED:    lights = 3'b100;  // Red on
            default: lights = 3'b100; // Default to red (safe)
        endcase
    end

endmodule
```

### Example 10.3: Vending Machine (25 cents, dispenses at 50 cents)

```systemverilog
module vending_machine (
    input  logic       clk,
    input  logic       rst_n,
    input  logic       nickel,   // 5 cents
    input  logic       dime,     // 10 cents
    input  logic       quarter,  // 25 cents
    output logic       dispense,
    output logic [5:0] change    // Amount to return
);
    // States represent amount deposited
    typedef enum logic [2:0] {
        CENTS_0  = 3'b000,
        CENTS_5  = 3'b001,
        CENTS_10 = 3'b010,
        CENTS_15 = 3'b011,
        CENTS_20 = 3'b100,
        CENTS_25 = 3'b101,
        CENTS_30 = 3'b110,
        CENTS_35 = 3'b111
    } state_t;

    state_t current_state, next_state;

    // State register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            current_state <= CENTS_0;
        else
            current_state <= next_state;
    end

    // Next state logic
    always_comb begin
        next_state = current_state;

        case (current_state)
            CENTS_0: begin
                if (nickel)       next_state = CENTS_5;
                else if (dime)    next_state = CENTS_10;
                else if (quarter) next_state = CENTS_25;
            end

            CENTS_5: begin
                if (nickel)       next_state = CENTS_10;
                else if (dime)    next_state = CENTS_15;
                else if (quarter) next_state = CENTS_30;
            end

            CENTS_10: begin
                if (nickel)       next_state = CENTS_15;
                else if (dime)    next_state = CENTS_20;
                else if (quarter) next_state = CENTS_35;
            end

            CENTS_15: begin
                if (nickel)       next_state = CENTS_20;
                else if (dime)    next_state = CENTS_25;
                else if (quarter) next_state = CENTS_0; // Dispense with 15 change
            end

            CENTS_20: begin
                if (nickel)       next_state = CENTS_25;
                else if (dime)    next_state = CENTS_30;
                else if (quarter) next_state = CENTS_0; // Dispense with 20 change
            end

            CENTS_25: begin
                if (nickel)       next_state = CENTS_30;
                else if (dime)    next_state = CENTS_35;
                else if (quarter) next_state = CENTS_0; // Dispense with 25 change
            end

            CENTS_30: begin
                if (nickel)       next_state = CENTS_35;
                else if (dime)    next_state = CENTS_0; // Dispense with 15 change
                else if (quarter) next_state = CENTS_0; // Dispense with 30 change
            end

            CENTS_35: begin
                if (nickel)       next_state = CENTS_0; // Dispense with 15 change
                else if (dime)    next_state = CENTS_0; // Dispense with 20 change
                else if (quarter) next_state = CENTS_0; // Dispense with 35 change
            end

            default: next_state = CENTS_0;
        endcase
    end

    // Output logic
    always_comb begin
        dispense = 1'b0;
        change = 6'd0;

        // Dispense when we have >= 50 cents
        case (current_state)
            CENTS_0, CENTS_5, CENTS_10, CENTS_15, CENTS_20, CENTS_25: begin
                dispense = 1'b0;
                change = 6'd0;
            end

            CENTS_30: begin
                if (dime || quarter) begin
                    dispense = 1'b1;
                    change = (dime) ? 6'd0 : 6'd5;
                end
            end

            CENTS_35: begin
                if (nickel || dime || quarter) begin
                    dispense = 1'b1;
                    if (nickel)      change = 6'd0;
                    else if (dime)   change = 6'd5;
                    else if (quarter) change = 6'd10;
                end
            end

            default: begin
                dispense = 1'b0;
                change = 6'd0;
            end
        endcase

        // Special cases for earlier states with quarter
        if ((current_state == CENTS_15 && quarter) ||
            (current_state == CENTS_20 && quarter) ||
            (current_state == CENTS_25 && quarter)) begin
            dispense = 1'b1;
        end
    end

endmodule
```

---

## 11. Advanced FSM Concepts

### 11.1 Overlapping vs Non-Overlapping Detection

When detecting sequences, there are two approaches:

**Non-Overlapping**: After detecting a pattern, start fresh
**Overlapping**: After detecting a pattern, continue from current position

**Example**: Detect "101" in stream "1 0 1 0 1"

Non-overlapping:
```
1 0 1 0 1
^^^^^       First detection
      ^^^   Cannot use the last '1' from first - NO second detection
```

Overlapping:
```
1 0 1 0 1
^^^^^       First detection
    ^^^^^   Can reuse the '1' - Second detection!
```

**Implementation Difference**:
In overlapping detection, when you detect the pattern, you transition to a state that allows reusing part of the pattern. We already implemented this in Example 7.3!

### 11.2 Hierarchical State Machines

For complex systems, use hierarchical FSMs:

```
Top Level State Machine
    ├── State A
    │   └── Sub-FSM for State A
    │       ├── A1
    │       ├── A2
    │       └── A3
    ├── State B
    └── State C
        └── Sub-FSM for State C
            ├── C1
            └── C2
```

**Example**: Washing machine
```
Main FSM: {IDLE, RUNNING, PAUSED}
    └── When in RUNNING:
        Sub-FSM: {FILL, WASH, RINSE, SPIN, DRAIN}
```

### 11.3 FSM with Datapath

Complex designs separate control and data:
- **FSM (Control)**: Manages states and control signals
- **Datapath**: Performs actual data operations (ALU, registers, etc.)

```
┌─────────────┐         Control Signals        ┌─────────────┐
│             │──────────────────────────────>│             │
│   FSM       │                                │  Datapath   │
│  (Control)  │<──────────────────────────────│             │
└─────────────┘         Status Signals         └─────────────┘
```

**Example**: Simple processor
```systemverilog
// FSM controls what operations to do
// Datapath performs the operations

module simple_processor (
    input logic clk, rst_n,
    input logic [7:0] instruction,
    output logic done
);
    // FSM States
    typedef enum logic [1:0] {
        FETCH, DECODE, EXECUTE, WRITEBACK
    } state_t;

    state_t state, next_state;

    // Datapath signals (controlled by FSM)
    logic [7:0] reg_a, reg_b, alu_out;
    logic load_a, load_b, alu_op;

    // FSM (Control)
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) state <= FETCH;
        else state <= next_state;

    always_comb begin
        // Default control signals
        load_a = 0; load_b = 0; alu_op = 0; done = 0;
        next_state = state;

        case (state)
            FETCH: begin
                next_state = DECODE;
            end
            DECODE: begin
                load_a = 1;
                next_state = EXECUTE;
            end
            EXECUTE: begin
                alu_op = 1;
                next_state = WRITEBACK;
            end
            WRITEBACK: begin
                load_b = 1;
                done = 1;
                next_state = FETCH;
            end
        endcase
    end

    // Datapath (simplified)
    always_ff @(posedge clk) begin
        if (load_a) reg_a <= instruction;
        if (load_b) reg_b <= alu_out;
    end

    assign alu_out = (alu_op) ? reg_a + 8'd1 : reg_a;

endmodule
```

### 11.4 Safe FSM Design

**Problem**: What if FSM enters an undefined state due to SEU (Single Event Upset) or other errors?

**Solution 1: Default case**
```systemverilog
always_comb begin
    case (current_state)
        STATE0: next_state = STATE1;
        STATE1: next_state = STATE2;
        STATE2: next_state = STATE0;
        default: next_state = STATE0;  // Safe state
    endcase
end
```

**Solution 2: Full case coverage**
Use one-hot encoding and check for errors:
```systemverilog
always_comb begin
    // Check if exactly one bit is set
    if ($countones(current_state) != 1)
        next_state = IDLE;  // Error recovery
    else
        // Normal state transitions
        ...
end
```

### 11.5 Performance Optimizations

**1. One-Hot Encoding for Speed**
- Faster state decoding
- More flip-flops but simpler logic
- Better for high-speed designs

**2. Gray Coding for Low Power**
- Only one bit changes per transition
- Reduces switching power
- Good for low-power designs

**3. Pipeline FSM**
For high-throughput, process multiple items:
```systemverilog
// Instead of: IDLE → PROC1 → PROC2 → PROC3 → IDLE
// Use pipeline: Item1 in PROC3, Item2 in PROC2, Item3 in PROC1
```

---

## 12. Advanced Examples

### Example 12.1: UART Receiver FSM

A practical industry example - receiving serial data:

```systemverilog
module uart_rx_fsm #(
    parameter CLKS_PER_BIT = 87  // For 115200 baud at 10MHz clock
)(
    input  logic       clk,
    input  logic       rst_n,
    input  logic       rx,           // Serial input
    output logic [7:0] rx_data,      // Received byte
    output logic       rx_valid      // Data valid pulse
);
    // States
    typedef enum logic [2:0] {
        IDLE       = 3'b000,
        START_BIT  = 3'b001,
        DATA_BITS  = 3'b010,
        STOP_BIT   = 3'b011,
        CLEANUP    = 3'b100
    } state_t;

    state_t state, next_state;

    // Internal registers
    logic [7:0] clk_count;
    logic [2:0] bit_index;
    logic [7:0] rx_byte;

    // State register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next_state;
    end

    // Clock counter for bit timing
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            clk_count <= 0;
        else if (state != next_state)
            clk_count <= 0;
        else
            clk_count <= clk_count + 1;
    end

    // Bit index counter
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            bit_index <= 0;
        else if (state == DATA_BITS && clk_count == CLKS_PER_BIT - 1)
            bit_index <= bit_index + 1;
        else if (state != DATA_BITS)
            bit_index <= 0;
    end

    // Data sampling
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            rx_byte <= 0;
        else if (state == DATA_BITS && clk_count == CLKS_PER_BIT/2)
            rx_byte[bit_index] <= rx;  // Sample in middle of bit
    end

    // Next state logic
    always_comb begin
        next_state = state;

        case (state)
            IDLE: begin
                if (rx == 0)  // Start bit detected
                    next_state = START_BIT;
            end

            START_BIT: begin
                if (clk_count == CLKS_PER_BIT - 1) begin
                    if (rx == 0)  // Verify it's still low
                        next_state = DATA_BITS;
                    else
                        next_state = IDLE;  // False start
                end
            end

            DATA_BITS: begin
                if (bit_index == 7 && clk_count == CLKS_PER_BIT - 1)
                    next_state = STOP_BIT;
            end

            STOP_BIT: begin
                if (clk_count == CLKS_PER_BIT - 1)
                    next_state = CLEANUP;
            end

            CLEANUP: begin
                next_state = IDLE;
            end

            default: next_state = IDLE;
        endcase
    end

    // Output logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_data <= 0;
            rx_valid <= 0;
        end else begin
            rx_valid <= (state == CLEANUP);  // Pulse for one cycle
            if (state == CLEANUP)
                rx_data <= rx_byte;
        end
    end

endmodule
```

### Example 12.2: Memory Controller FSM

```systemverilog
module memory_controller (
    input  logic        clk,
    input  logic        rst_n,
    // CPU Interface
    input  logic        req,          // Request
    input  logic        wr_en,        // Write enable (1=write, 0=read)
    input  logic [31:0] addr,         // Address
    input  logic [31:0] wr_data,      // Write data
    output logic [31:0] rd_data,      // Read data
    output logic        ready,        // Ready for new request
    // Memory Interface
    output logic        mem_req,
    output logic        mem_wr,
    output logic [31:0] mem_addr,
    output logic [31:0] mem_wr_data,
    input  logic [31:0] mem_rd_data,
    input  logic        mem_ready
);
    // States
    typedef enum logic [2:0] {
        IDLE         = 3'b000,
        DECODE       = 3'b001,
        MEM_READ     = 3'b010,
        MEM_WRITE    = 3'b011,
        WAIT_READY   = 3'b100,
        COMPLETE     = 3'b101
    } state_t;

    state_t state, next_state;

    // Internal registers to latch request
    logic [31:0] latched_addr;
    logic [31:0] latched_data;
    logic        latched_wr;

    // State register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next_state;
    end

    // Latch request when accepted
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            latched_addr <= 0;
            latched_data <= 0;
            latched_wr <= 0;
        end else if (state == IDLE && req) begin
            latched_addr <= addr;
            latched_data <= wr_data;
            latched_wr <= wr_en;
        end
    end

    // Next state logic
    always_comb begin
        next_state = state;

        case (state)
            IDLE: begin
                if (req)
                    next_state = DECODE;
            end

            DECODE: begin
                if (latched_wr)
                    next_state = MEM_WRITE;
                else
                    next_state = MEM_READ;
            end

            MEM_READ: begin
                next_state = WAIT_READY;
            end

            MEM_WRITE: begin
                next_state = WAIT_READY;
            end

            WAIT_READY: begin
                if (mem_ready)
                    next_state = COMPLETE;
            end

            COMPLETE: begin
                next_state = IDLE;
            end

            default: next_state = IDLE;
        endcase
    end

    // Output logic
    always_comb begin
        // Defaults
        mem_req = 0;
        mem_wr = 0;
        mem_addr = latched_addr;
        mem_wr_data = latched_data;
        ready = 0;

        case (state)
            IDLE: begin
                ready = 1;
            end

            MEM_READ: begin
                mem_req = 1;
                mem_wr = 0;
            end

            MEM_WRITE: begin
                mem_req = 1;
                mem_wr = 1;
            end

            WAIT_READY: begin
                mem_req = 1;
                mem_wr = latched_wr;
            end

            COMPLETE: begin
                ready = 1;
            end
        endcase
    end

    // Read data register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            rd_data <= 0;
        else if (state == WAIT_READY && mem_ready && !latched_wr)
            rd_data <= mem_rd_data;
    end

endmodule
```

### Example 12.3: Elevator Controller

A fun and comprehensive example:

```systemverilog
module elevator_controller #(
    parameter NUM_FLOORS = 4
)(
    input  logic                      clk,
    input  logic                      rst_n,
    input  logic [NUM_FLOORS-1:0]     floor_request,  // Request from each floor
    input  logic [NUM_FLOORS-1:0]     door_sensor,    // Door obstruction sensor
    output logic [NUM_FLOORS-1:0]     current_floor,  // One-hot encoded
    output logic                      door_open,
    output logic                      moving_up,
    output logic                      moving_down
);
    // States
    typedef enum logic [2:0] {
        IDLE            = 3'b000,
        DOOR_OPENING    = 3'b001,
        DOOR_OPEN       = 3'b010,
        DOOR_CLOSING    = 3'b011,
        MOVING_UP       = 3'b100,
        MOVING_DOWN     = 3'b101
    } state_t;

    state_t state, next_state;

    // Current floor register (one-hot)
    logic [NUM_FLOORS-1:0] floor;

    // Timer for door operations and movement
    logic [7:0] timer;
    parameter DOOR_TIME = 50;    // Cycles for door operation
    parameter MOVE_TIME = 100;   // Cycles to move between floors
    parameter WAIT_TIME = 150;   // Time to wait with door open

    // Pending requests
    logic [NUM_FLOORS-1:0] requests;

    // State register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next_state;
    end

    // Floor register - initialized to floor 0
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            floor <= 4'b0001;  // Start at floor 0
        else if (state == MOVING_UP && timer == MOVE_TIME - 1)
            floor <= {floor[NUM_FLOORS-2:0], 1'b0};  // Shift up
        else if (state == MOVING_DOWN && timer == MOVE_TIME - 1)
            floor <= {1'b0, floor[NUM_FLOORS-1:1]};  // Shift down
    end

    // Request register - latch requests, clear when serviced
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            requests <= 0;
        else begin
            requests <= requests | floor_request;  // Latch new requests
            if (state == DOOR_OPEN && timer == WAIT_TIME - 1)
                requests <= requests & ~floor;  // Clear current floor request
        end
    end

    // Timer
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            timer <= 0;
        else if (state != next_state)
            timer <= 0;
        else
            timer <= timer + 1;
    end

    // Check if there are requests above or below
    wire requests_above = |(requests & ~((floor << 1) - 1));
    wire requests_below = |(requests & (floor - 1));
    wire request_here = |(requests & floor);

    // Next state logic
    always_comb begin
        next_state = state;

        case (state)
            IDLE: begin
                if (request_here)
                    next_state = DOOR_OPENING;
                else if (requests_above)
                    next_state = MOVING_UP;
                else if (requests_below)
                    next_state = MOVING_DOWN;
            end

            DOOR_OPENING: begin
                if (timer >= DOOR_TIME - 1)
                    next_state = DOOR_OPEN;
            end

            DOOR_OPEN: begin
                if (timer >= WAIT_TIME - 1 && !door_sensor[0])  // No obstruction
                    next_state = DOOR_CLOSING;
            end

            DOOR_CLOSING: begin
                if (door_sensor[0])  // Obstruction detected
                    next_state = DOOR_OPENING;
                else if (timer >= DOOR_TIME - 1)
                    next_state = IDLE;
            end

            MOVING_UP: begin
                if (timer >= MOVE_TIME - 1) begin
                    if (request_here || !requests_above)
                        next_state = DOOR_OPENING;
                end
            end

            MOVING_DOWN: begin
                if (timer >= MOVE_TIME - 1) begin
                    if (request_here || !requests_below)
                        next_state = DOOR_OPENING;
                end
            end

            default: next_state = IDLE;
        endcase
    end

    // Output logic
    assign current_floor = floor;
    assign door_open = (state == DOOR_OPEN || state == DOOR_OPENING);
    assign moving_up = (state == MOVING_UP);
    assign moving_down = (state == MOVING_DOWN);

endmodule
```

---

## 13. FSM Design Best Practices

### 13.1 General Design Principles

1. **Keep It Simple**
   - Use minimum number of states needed
   - Clear state names (IDLE, ACTIVE, not S0, S1)
   - One FSM per function

2. **Always Have Reset**
   ```systemverilog
   always_ff @(posedge clk or negedge rst_n) begin
       if (!rst_n)
           state <= INITIAL_STATE;  // Always define reset behavior
       else
           state <= next_state;
   end
   ```

3. **Always Have Default**
   ```systemverilog
   always_comb begin
       case (state)
           STATE0: ...
           STATE1: ...
           default: next_state = SAFE_STATE;  // ALWAYS include default
       endcase
   end
   ```

4. **Use Enumerated Types**
   ```systemverilog
   // Good
   typedef enum logic [1:0] {IDLE, RUN, STOP} state_t;

   // Bad
   logic [1:0] state;
   parameter IDLE = 2'b00, RUN = 2'b01;
   ```

### 13.2 Coding Best Practices

1. **Separate Sequential and Combinational Logic**
   ```systemverilog
   // Sequential: state register only
   always_ff @(posedge clk) begin
       state <= next_state;
   end

   // Combinational: next state logic
   always_comb begin
       next_state = f(state, inputs);
   end
   ```

2. **Avoid Latches**
   ```systemverilog
   // Good - all cases covered
   always_comb begin
       next_state = state;  // Default assignment
       case (state)
           ...
       endcase
   end

   // Bad - can infer latches
   always_comb begin
       case (state)
           STATE0: next_state = STATE1;
           // Missing other cases!
       endcase
   end
   ```

3. **Register Outputs When Possible**
   ```systemverilog
   // Good - registered output (glitch-free)
   always_ff @(posedge clk) begin
       if (state == ACTIVE)
           output_signal <= 1;
       else
           output_signal <= 0;
   end

   // Acceptable but may glitch
   assign output_signal = (state == ACTIVE);
   ```

4. **Use Meaningful State Names**
   ```systemverilog
   // Good
   typedef enum {
       WAIT_FOR_REQUEST,
       PROCESS_DATA,
       SEND_RESPONSE,
       ERROR_HANDLER
   } state_t;

   // Bad
   typedef enum {S0, S1, S2, S3} state_t;
   ```

### 13.3 Timing and Performance

1. **Minimize Logic Depth in Combinational Blocks**
   - Deep logic in next_state logic increases critical path
   - Consider pipelining if needed

2. **Be Careful with Complex Conditions**
   ```systemverilog
   // Can create long paths
   if (input_a && input_b && input_c && !input_d && counter > 100) begin
       next_state = STATE1;
   end

   // Better: pre-compute complex conditions
   wire complex_condition = (input_a && input_b && input_c && !input_d && counter > 100);
   if (complex_condition) begin
       next_state = STATE1;
   end
   ```

3. **Choose Encoding Based on Requirements**
   - **Binary**: Minimum flip-flops
   - **One-Hot**: Fastest, simple decode
   - **Gray**: Low power, good for crossing clock domains

### 13.4 Verification Best Practices

1. **Coverage**
   - Test all states
   - Test all transitions
   - Test edge cases (reset during operation, etc.)

2. **Assertions**
   ```systemverilog
   // State must be one-hot
   assert property (@(posedge clk) $onehot(state));

   // Should never reach illegal state
   assert property (@(posedge clk) state != ILLEGAL_STATE);
   ```

3. **Create Self-Checking Testbenches**
   ```systemverilog
   // Check expected behavior
   if (state == COMPLETE && output_signal != expected_value) begin
       $error("Output mismatch at time %0t", $time);
   end
   ```

### 13.5 Documentation

1. **Include State Diagram in Comments**
   ```systemverilog
   /*
    * State Machine: Traffic Light Controller
    *
    *     GREEN ──timer──> YELLOW ──timer──> RED ──timer──> GREEN
    *      (30s)             (5s)            (30s)
    */
   ```

2. **Document Each State's Purpose**
   ```systemverilog
   typedef enum {
       IDLE,         // Waiting for new request
       PROCESSING,   // Computing result
       DONE          // Result ready, waiting for acknowledgment
   } state_t;
   ```

---

## 14. Common Pitfalls and How to Avoid Them

### 14.1 Latch Inference

**Problem:**
```systemverilog
// BAD - Creates latch!
always_comb begin
    case (state)
        STATE0: next_state = STATE1;
        STATE1: next_state = STATE2;
        // Missing STATE2 case!
    endcase
end
```

**Solution:**
```systemverilog
// GOOD
always_comb begin
    next_state = state;  // Default assignment
    case (state)
        STATE0: next_state = STATE1;
        STATE1: next_state = STATE2;
        STATE2: next_state = STATE0;
        default: next_state = STATE0;
    endcase
end
```

### 14.2 Mixing Sequential and Combinational

**Problem:**
```systemverilog
// BAD - Mixing blocking and non-blocking
always_ff @(posedge clk) begin
    state <= next_state;
    output_signal = (state == ACTIVE);  // Wrong assignment type
end
```

**Solution:**
```systemverilog
// GOOD - Separate blocks
always_ff @(posedge clk) begin
    state <= next_state;
end

always_comb begin
    output_signal = (state == ACTIVE);
end
```

### 14.3 Forgetting Reset

**Problem:**
```systemverilog
// BAD - No reset
always_ff @(posedge clk) begin
    state <= next_state;
end
```

**Solution:**
```systemverilog
// GOOD
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        state <= IDLE;
    else
        state <= next_state;
end
```

### 14.4 Race Conditions in Mealy Machines

**Problem:** Output can glitch when input changes

**Solution:** Register the output or use Moore machine

```systemverilog
// Mealy output (may glitch)
assign output = (state == S0 && input == 1);

// Better - registered
always_ff @(posedge clk) begin
    output <= (state == S0 && input == 1);
end
```

### 14.5 Not Handling All Input Combinations

**Problem:**
```systemverilog
// What if both input_a and input_b are high?
case (state)
    IDLE: begin
        if (input_a) next_state = STATE_A;
        if (input_b) next_state = STATE_B;
    end
endcase
```

**Solution:**
```systemverilog
// Explicitly handle priorities
case (state)
    IDLE: begin
        if (input_a)
            next_state = STATE_A;
        else if (input_b)
            next_state = STATE_B;
        else
            next_state = IDLE;
    end
endcase
```

### 14.6 Overly Complex FSMs

**Problem:** Too many states, hard to understand

**Solution:**
- Break into multiple FSMs
- Use hierarchical FSMs
- Consider FSM + Datapath separation

### 14.7 Not Considering Invalid States

**Problem:** FSM in undefined state due to corruption

**Solution:**
```systemverilog
always_comb begin
    // Check for valid state
    case (state)
        STATE0, STATE1, STATE2: begin
            // Normal logic
        end
        default: begin
            // Error recovery
            next_state = SAFE_STATE;
            error_flag = 1;
        end
    endcase
end
```

---

## 15. Debugging FSMs

### 15.1 Common Debug Techniques

1. **Add State Display in Simulation**
   ```systemverilog
   // In testbench
   always @(state) begin
       $display("Time %0t: State changed to %s", $time, state.name());
   end
   ```

2. **Create Waveform Markers**
   ```systemverilog
   // Mark important transitions
   always @(posedge clk) begin
       if (state == CRITICAL_STATE)
           $display("MARKER: Entered critical state at %0t", $time);
   end
   ```

3. **Use Assertions**
   ```systemverilog
   // Check FSM properties
   property valid_transition;
       @(posedge clk)
       (state == STATE0) |=> (next_state inside {STATE1, STATE2});
   endproperty
   assert property (valid_transition);
   ```

4. **State History Buffer**
   ```systemverilog
   // Keep history for debugging
   logic [2:0] state_history [0:7];
   integer hist_ptr = 0;

   always_ff @(posedge clk) begin
       if (state != next_state) begin
           state_history[hist_ptr] <= state;
           hist_ptr <= (hist_ptr + 1) % 8;
       end
   end
   ```

### 15.2 Debug Checklist

When FSM doesn't work:

- [ ] Check reset: Does FSM properly initialize?
- [ ] Check state transitions: Are all paths covered?
- [ ] Check default cases: Any missing cases?
- [ ] Check for latches: Did you assign defaults?
- [ ] Check timing: Are signals sampled at right time?
- [ ] Check inputs: Are they stable when sampled?
- [ ] Check outputs: Registered or combinational?
- [ ] Check for race conditions: Any async logic?
- [ ] Verify state encoding: Correct bit widths?
- [ ] Check for stuck states: Can FSM always progress?

### 15.3 Example Debug Session

```systemverilog
module debug_fsm (
    input  logic clk,
    input  logic rst_n,
    input  logic go,
    output logic done
);
    typedef enum logic [1:0] {IDLE, WORK, FINISH} state_t;
    state_t state, next_state;

    // Debug signals
    logic state_changed;
    assign state_changed = (state != next_state);

    // State register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            // Debug output
            $display("DEBUG: Reset - going to IDLE");
        end else begin
            state <= next_state;
            // Debug output
            if (state_changed)
                $display("DEBUG: Time=%0t State: %s -> %s",
                         $time, state.name(), next_state.name());
        end
    end

    // Next state logic with debug
    always_comb begin
        next_state = state;

        case (state)
            IDLE: begin
                if (go) begin
                    next_state = WORK;
                    $display("DEBUG: Go signal received in IDLE");
                end
            end

            WORK: begin
                next_state = FINISH;
            end

            FINISH: begin
                next_state = IDLE;
            end

            default: begin
                next_state = IDLE;
                $display("ERROR: Invalid state detected!");
            end
        endcase
    end

    // Output
    assign done = (state == FINISH);

endmodule
```

---

## 16. Practice Problems

### Problem 1: Even Parity Detector (Easy)

**Description:** Design a Moore FSM that outputs '1' when the number of '1's in the input stream is even (including zero).

**Hint:** You need 2 states: EVEN and ODD

<details>
<summary>Click for solution</summary>

```systemverilog
module even_parity (
    input  logic clk, rst_n, data_in,
    output logic parity_even
);
    typedef enum logic {EVEN = 0, ODD = 1} state_t;
    state_t state, next_state;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) state <= EVEN;
        else state <= next_state;

    always_comb begin
        case (state)
            EVEN: next_state = data_in ? ODD : EVEN;
            ODD:  next_state = data_in ? EVEN : ODD;
        endcase
    end

    assign parity_even = (state == EVEN);
endmodule
```
</details>

### Problem 2: Sequence Detector "1011" Non-Overlapping (Medium)

**Description:** Design a Moore FSM that detects "1011" sequence. After detection, must see the complete sequence again (non-overlapping).

**Hint:** Need states for IDLE, GOT_1, GOT_10, GOT_101, DETECTED

<details>
<summary>Click for solution</summary>

```systemverilog
module seq_1011_nonoverlap (
    input  logic clk, rst_n, din,
    output logic detected
);
    typedef enum logic [2:0] {
        IDLE, GOT_1, GOT_10, GOT_101, DETECTED
    } state_t;
    state_t state, next_state;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) state <= IDLE;
        else state <= next_state;

    always_comb begin
        case (state)
            IDLE:     next_state = din ? GOT_1 : IDLE;
            GOT_1:    next_state = din ? GOT_1 : GOT_10;
            GOT_10:   next_state = din ? GOT_101 : IDLE;
            GOT_101:  next_state = din ? DETECTED : GOT_10;
            DETECTED: next_state = din ? GOT_1 : IDLE;
            default:  next_state = IDLE;
        endcase
    end

    assign detected = (state == DETECTED);
endmodule
```
</details>

### Problem 3: Two-Way Traffic Light (Medium)

**Description:** Design a traffic light controller for two intersecting roads (Main and Side). Main road gets green by default. When a car is detected on the side road, give it green for some time.

**Hint:** States: MAIN_GREEN, MAIN_YELLOW, SIDE_GREEN, SIDE_YELLOW

### Problem 4: Serial Adder (Hard)

**Description:** Design an FSM that adds two serial numbers (LSB first) and produces serial output with carry.

**Hint:** States based on carry: NO_CARRY, CARRY

### Problem 5: Pattern Matcher with Wildcards (Hard)

**Description:** Detect pattern "1X01" where X can be either 0 or 1.
Example matches: 1001, 1101

**Hint:** States: IDLE, GOT_1, GOT_1X, GOT_1X0, DETECTED

---

## 17. Summary and Next Steps

### What You've Learned

1. **Fundamentals**
   - What FSMs are and why they're important
   - States, transitions, inputs, outputs
   - Moore vs Mealy machines

2. **Design Skills**
   - How to design FSMs from specifications
   - State diagrams and state tables
   - Best coding practices

3. **Implementation**
   - SystemVerilog coding styles
   - State encoding methods
   - Real-world examples

4. **Advanced Topics**
   - Hierarchical FSMs
   - FSM with datapath
   - Safe FSM design
   - Performance optimization

5. **Practical Skills**
   - Debugging techniques
   - Common pitfalls
   - Industry best practices

### Next Steps

1. **Practice More**
   - Solve all practice problems
   - Implement classic FSMs (e.g., coin counter, string matcher)
   - Try HDLBits FSM problems

2. **Study Real Designs**
   - Look at UART, SPI, I2C controllers
   - Study CPU control units
   - Examine memory controllers

3. **Advanced Topics to Explore**
   - Formal verification of FSMs
   - FSM optimization algorithms
   - FSM synthesis and timing closure
   - Power-aware FSM design

4. **Related Concepts**
   - Regular expressions and automata theory
   - Pushdown automata
   - Turing machines
   - Model checking

### Resources for Further Learning

1. **Books**
   - "Digital Design and Computer Architecture" by Harris & Harris
   - "RTL Modeling with SystemVerilog for Simulation and Synthesis" by Stuart Sutherland
   - "Finite State Machines in Hardware" by Volnei A. Pedroni

2. **Online Resources**
   - HDLBits (practice problems)
   - ASIC World tutorials
   - ChipVerify SystemVerilog tutorials

3. **Tools**
   - ModelSim/QuestaSim for simulation
   - Vivado/Quartus for synthesis
   - GTKWave for waveform viewing

### Final Tips

- **Start Simple**: Master basic FSMs before complex ones
- **Draw First**: Always draw state diagram before coding
- **Test Thoroughly**: Good testbenches are crucial
- **Learn from Errors**: Debug sessions teach the most
- **Read Code**: Study well-written FSM examples
- **Ask Questions**: Join communities (Reddit, Stack Overflow)

---

## Congratulations! 🎉

You've completed the comprehensive FSM guide! You now have the knowledge to design, implement, and debug finite state machines from simple to complex. Remember:

> "The best way to learn FSMs is to design them!"

Keep practicing, and soon FSM design will become second nature. Good luck with your digital design journey!

---

**Document Version:** 1.0
**Last Updated:** 2025
**Author:** SystemVerilog Learning Repository
**License:** MIT

---

## Appendix: Quick Reference

### State Diagram Symbols
```
┌─────────┐
│  STATE  │    State (Moore machine - output inside)
│ output  │
└─────────┘

  input/output
─────────────→  Transition (Mealy machine - output on arrow)

──→             Transition (Moore machine - only input)

───────→  │     Initial state indicator
        STATE
```

### Coding Template (3-Block)
```systemverilog
module fsm_template (
    input  logic clk, rst_n, [inputs],
    output logic [outputs]
);
    typedef enum logic [...] {...} state_t;
    state_t state, next_state;

    // Block 1: State register
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) state <= INITIAL;
        else state <= next_state;

    // Block 2: Next state logic
    always_comb begin
        next_state = state;
        case (state)
            // ... state transitions
        endcase
    end

    // Block 3: Output logic
    always_comb begin
        case (state)
            // ... output assignments
        endcase
    end
endmodule
```

### Common State Encodings
```systemverilog
// Binary
typedef enum logic [1:0] {S0=2'b00, S1=2'b01, S2=2'b10, S3=2'b11} state_t;

// One-hot
typedef enum logic [3:0] {S0=4'b0001, S1=4'b0010, S2=4'b0100, S3=4'b1000} state_t;

// Gray
typedef enum logic [1:0] {S0=2'b00, S1=2'b01, S2=2'b11, S3=2'b10} state_t;
```

---
