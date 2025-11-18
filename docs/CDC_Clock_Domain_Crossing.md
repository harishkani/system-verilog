# Clock Domain Crossing (CDC) - Complete Guide

## Table of Contents
1. [Introduction](#introduction)
2. [Fundamental Concepts](#fundamental-concepts)
3. [CDC Problems and Metastability](#cdc-problems-and-metastability)
4. [CDC Synchronization Techniques](#cdc-synchronization-techniques)
5. [Single-Bit CDC Synchronizers](#single-bit-cdc-synchronizers)
6. [Multi-Bit CDC Techniques](#multi-bit-cdc-techniques)
7. [FIFO-Based CDC](#fifo-based-cdc)
8. [Handshaking Protocols](#handshaking-protocols)
9. [Advanced CDC Techniques](#advanced-cdc-techniques)
10. [CDC Verification](#cdc-verification)
11. [Best Practices](#best-practices)
12. [Common Pitfalls](#common-pitfalls)
13. [Industry Standards](#industry-standards)

---

## Introduction

### What is Clock Domain Crossing?

Clock Domain Crossing (CDC) occurs when a signal generated in one clock domain is sampled by a register in another clock domain. This is one of the most critical and error-prone aspects of digital design in modern SoCs.

### Why CDC Matters

- **Metastability Risk**: Can cause unpredictable circuit behavior
- **Data Loss**: Improper synchronization can lose data
- **System Failures**: CDC bugs are hard to detect and can cause intermittent failures
- **Timing Issues**: Can violate setup/hold times leading to functional failures

### Clock Domain Types

1. **Synchronous Domains**: Related by a fixed frequency ratio
2. **Asynchronous Domains**: No fixed relationship
3. **Mesochronous**: Same frequency, different phase

---

## Fundamental Concepts

### What is Metastability?

When a flip-flop's setup or hold time is violated, the output can enter a metastable state where:
- Output voltage is between logic 0 and 1
- Output oscillates
- Resolution time is unpredictable

**Metastability Visualization:**
```
Voltage Levels:
                VDD ─────────────────────────────────────

                              Metastable Region
                     ╔═══════════════════════════╗
                     ║  ≈≈≈≈≈  Oscillation  ≈≈≈≈≈║
                     ╚═══════════════════════════╝

                VSS ─────────────────────────────────────

                     |←  Tsu  →|← Th →|
                clk  ────┐      |      |──────
                         └──────┘

                data ─────────X─────────────  (X = uncertainty)
```

**Setup/Hold Violation Timing:**
```
Case 1: Setup Violation
                     |← Tsu →|
clk_a        ───┐    ↓    ┌───────
                └─────────┘

data_a       ────────╱╲────────── (changes too close to clock)
                    ↑ violation!

clk_b        ──┐       ┌──────
               └───────┘    ← Samples during violation

data_b       ─────────XXXX─────── (metastable!)


Case 2: Hold Violation
                         |← Th →|
clk_a        ───┐        ↓    ┌───
                └─────────────┘

data_a       ────────────╱╲────── (changes too soon after clock)
                        ↑ violation!
```

```systemverilog
// Unsafe CDC - Direct connection
module unsafe_cdc (
    input  clk_a,
    input  clk_b,
    input  data_in,
    output logic data_out
);
    logic data_a;

    // Register in domain A
    always_ff @(posedge clk_a)
        data_a <= data_in;

    // UNSAFE: Direct sampling in domain B
    always_ff @(posedge clk_b)
        data_out <= data_a;  // Metastability risk!

endmodule
```

**Waveform - Unsafe CDC:**
```
clk_a (100MHz)   ┐   ┌   ┐   ┌   ┐   ┌   ┐   ┌   ┐   ┌
                 └───┘   └───┘   └───┘   └───┘   └───┘

data_in          ─────┐           ┌─────────────────────
                      └───────────┘

data_a           ─────────┐           ┌─────────────────
                          └───────────┘ (registered on clk_a)

clk_b (75MHz)    ┐     ┌     ┐     ┌     ┐     ┌     ┐
                 └─────┘     └─────┘     └─────┘     └─

                            ↓ clk_b samples here
data_out         ─────────XXXX??????????────────────────
                          ↑ Metastability!

Risk: data_a changes at unpredictable time relative to clk_b
```

### Mean Time Between Failures (MTBF)

MTBF calculation for metastability:

```
MTBF = (e^(Tr/τ)) / (Fc × Fd × T0)

Where:
- Tr = Resolution time available
- τ = Flip-flop time constant
- Fc = Clock frequency
- Fd = Data toggle rate
- T0 = Metastability resolution window
```

### Key Parameters

- **Setup Time (Tsu)**: Minimum time data must be stable before clock edge
- **Hold Time (Th)**: Minimum time data must be stable after clock edge
- **Resolution Time**: Time for metastable state to resolve
- **MTBF**: Average time between metastability-induced failures

---

## CDC Problems and Metastability

### Types of CDC Violations

#### 1. Data Loss
```systemverilog
// Problem: Fast to slow clock domain
// Fast clock pulses may be missed in slow domain
```

#### 2. Data Incoherence
```systemverilog
// Problem: Multi-bit bus crossing
// Bits may be sampled at different times
```

#### 3. Metastability Propagation
```systemverilog
// Problem: Metastable signal used in combinational logic
// Can cause incorrect logic evaluation
```

### Detecting Metastability Issues

Static timing analysis cannot fully detect CDC issues because:
- Clocks are independent
- No timing relationship exists
- Requires specialized CDC verification tools

---

## CDC Synchronization Techniques

### Classification of CDC Techniques

1. **Level Synchronizers**: For slow-changing signals
2. **Edge Synchronizers**: For pulse detection
3. **Handshake Protocols**: For reliable data transfer
4. **FIFO Synchronizers**: For burst data transfer
5. **MUX Recirculation**: For multi-bit buses

---

## Single-Bit CDC Synchronizers

### Two-Flop Synchronizer (Double Synchronizer)

Most common CDC synchronizer for single-bit signals.

**Architecture Diagram:**
```
Source Domain          |  Destination Domain
                      |
data_in ──►[FF]───────┼─────►[FF1]────►[FF2]────► data_out
           clk_a      |      clk_b     clk_b
                      |       ↑         ↑
                      |       └─────────┘
                      |    May go      Resolution
                      |    metastable   stage
```

```systemverilog
module two_flop_sync (
    input  clk_dst,      // Destination clock
    input  rst_n,        // Active-low reset
    input  data_in,      // Asynchronous input
    output logic data_out
);
    logic sync_ff1;

    always_ff @(posedge clk_dst or negedge rst_n) begin
        if (!rst_n) begin
            sync_ff1 <= 1'b0;
            data_out <= 1'b0;
        end else begin
            sync_ff1 <= data_in;     // First stage
            data_out <= sync_ff1;    // Second stage
        end
    end

    // Synthesis constraints to prevent optimization
    // (* ASYNC_REG = "TRUE" *) for Xilinx
    // (* preserve *) for others

endmodule
```

**Detailed Waveform - Two-Flop Synchronizer:**
```
clk_src      ┐   ┌   ┐   ┌   ┐   ┌   ┐   ┌   ┐   ┌   ┐   ┌
             └───┘   └───┘   └───┘   └───┘   └───┘   └───┘

data_in      ─────┐                   ┌─────────────────────
                  └───────────────────┘

clk_dst      ┐     ┌     ┐     ┐     ┐     ┐     ┐     ┐
             └─────┘     └─────┘     └─────┘     └─────┘

                   ↓     ↓     ↓     ↓     ↓
             Sample points in destination domain

sync_ff1     ─────XXXX??┐                   ┌─────────────
                        └───────────────────┘
                   ↑ May be metastable for short time

data_out     ─────────────────┐                   ┌─────────
(stable)                      └───────────────────┘
                              ↑ Stable output (2 cycles latency)

Timing:
T0: data_in changes in source domain
T1: clk_dst samples → sync_ff1 may go metastable
T2: Metastability resolves (typically < 1ns)
T3: clk_dst samples sync_ff1 → data_out stable
```

**MTBF Improvement with Stages:**
```
Single Stage:                Two Stage:                Three Stage:

  MTBF = e^(T/τ)             MTBF = e^(2T/τ)         MTBF = e^(3T/τ)
  ─────────────              ────────────────         ────────────────
   Fc × Fd × T0              Fc × Fd × T0             Fc × Fd × T0

Example @ 100MHz, T=10ns, τ=150ps:
  1 stage:  ~10 years
  2 stages: ~10^28 years ← Industry standard
  3 stages: ~10^56 years ← Safety-critical
```

**Synchronization Delay:**
```
Best Case:  2 clock cycles (clk_dst)
Worst Case: 3 clock cycles (clk_dst)

Depends on when data_in changes relative to clk_dst edges

Case 1 - Data changes just after clk_dst:
clk_dst      ┐     ┌     ┐     ┐     ┐
             └─────┘     └─────┘     └─────┘
                ↑ data changes here
data_in      ──┐
               └────────────────────────────

data_out     ────────────────┐              (2 cycles)
                             └───────────────

Case 2 - Data changes just before clk_dst:
clk_dst      ┐     ┌     ┐     ┐     ┐
             └─────┘     └─────┘     └─────┘
             ↑ data changes here
data_in      ┐
             └────────────────────────────

data_out     ──────────────────────┐        (3 cycles)
                                   └─────────
```

#### Key Points:
- First flip-flop may go metastable
- Second flip-flop provides time for resolution
- MTBF improves exponentially with more stages
- 2-3 stages are typical
- Adds 2-3 cycle latency
- Only for slowly changing signals (not pulses!)

### Three-Flop Synchronizer

For higher reliability requirements:

```systemverilog
module three_flop_sync (
    input  clk_dst,
    input  rst_n,
    input  data_in,
    output logic data_out
);
    (* ASYNC_REG = "TRUE" *) logic [2:0] sync_chain;

    always_ff @(posedge clk_dst or negedge rst_n) begin
        if (!rst_n)
            sync_chain <= 3'b0;
        else
            sync_chain <= {sync_chain[1:0], data_in};
    end

    assign data_out = sync_chain[2];

endmodule
```

### Edge Detector Synchronizer

For detecting edges/pulses crossing clock domains:

**Problem with Direct Pulse Synchronization:**
```
Fast to Slow Domain - Pulse Lost:

clk_src(fast) ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐   (100 MHz)
              └─┘ └─┘ └─┘ └─┘ └─

pulse_in      ──┐ ┌─────────────   (1 cycle pulse)
                └─┘

clk_dst(slow) ┐     ┌     ┐     ┐  (25 MHz)
              └─────┘     └─────┘

pulse_out     ──────────────────   (MISSED! Too short)

Solution: Convert pulse to level (toggle)
```

**Toggle-Based Edge Detection Architecture:**
```
Source Domain              Destination Domain

pulse_in ─►[Toggle]───────►[Sync]────►[Edge    ]──► pulse_out
           Generator   |    2-FF       Detector
           (clk_src)   |   (clk_dst)   (clk_dst)
                      CDC
                   Boundary
```

```systemverilog
module edge_detect_sync (
    input  clk_src,
    input  clk_dst,
    input  rst_n,
    input  pulse_in,     // Pulse in source domain
    output logic pulse_out  // Pulse in destination domain
);
    // Source domain: Convert pulse to level
    logic toggle_src;

    always_ff @(posedge clk_src or negedge rst_n) begin
        if (!rst_n)
            toggle_src <= 1'b0;
        else if (pulse_in)
            toggle_src <= ~toggle_src;
    end

    // Synchronize toggle to destination domain
    logic [2:0] sync_toggle;

    always_ff @(posedge clk_dst or negedge rst_n) begin
        if (!rst_n)
            sync_toggle <= 3'b0;
        else
            sync_toggle <= {sync_toggle[1:0], toggle_src};
    end

    // Detect edge in destination domain
    always_ff @(posedge clk_dst or negedge rst_n) begin
        if (!rst_n)
            pulse_out <= 1'b0;
        else
            pulse_out <= sync_toggle[2] ^ sync_toggle[1];
    end

endmodule
```

**Complete Waveform - Edge Detection:**
```
Source Domain (100 MHz)
─────────────────────────────────────────────────────────

clk_src      ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐
             └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘

pulse_in     ────┐ ┌────────────┐ ┌──────────────────
                 └─┘            └─┘
                 P1             P2  (short pulses)

toggle_src   ────────┐                   ┌───────────
                     └───────────────────┘
                     ↑ toggles on P1     ↑ toggles on P2


Destination Domain (25 MHz)
─────────────────────────────────────────────────────────

clk_dst      ┐     ┌     ┐     ┐     ┐     ┐     ┐
             └─────┘     └─────┘     └─────┘     └─────┘

sync_toggle[0]  ──────────┐                 ┌───────────
(stage 1)                 └─────────────────┘

sync_toggle[1]  ────────────────┐                 ┌─────
(stage 2)                       └─────────────────┘

sync_toggle[2]  ──────────────────────┐                 ┌
(stage 3)                             └─────────────────┘

pulse_out    ────────────────┐ ┌─────────────┐ ┌────────
(XOR detect)                 └─┘             └─┘
                             ↑ Rising edge   ↑ Falling edge
                             detected        detected

Key Benefits:
1. Pulses cannot be missed (converted to level)
2. Works across any clock ratio
3. Both rising and falling edges detected
4. 2-3 cycle latency in destination domain
```

**Multiple Pulse Handling:**
```
Problem - Pulses too close together:

clk_src      ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐
             └─┘ └─┘ └─┘ └─┘ └─┘ └─┘

pulse_in     ──┐ ┌─┐ ┌───────────   (2 pulses, 2 cycles apart)
               └─┘ └─┘

toggle_src   ────┐ ┌─┐ ┌───────────  ⚠ Toggles cancel out!
                 └─┘ └─┘

Solution: Space pulses by ≥ 3 destination clock cycles
OR use separate toggle for each pulse
OR use FIFO for pulse buffering
```

### Level Synchronizer with Enable

```systemverilog
module level_sync_with_enable (
    input  clk_dst,
    input  rst_n,
    input  enable,
    input  data_in,
    output logic data_out
);
    logic [1:0] sync_ff;

    always_ff @(posedge clk_dst or negedge rst_n) begin
        if (!rst_n) begin
            sync_ff <= 2'b0;
            data_out <= 1'b0;
        end else if (enable) begin
            sync_ff <= {sync_ff[0], data_in};
            data_out <= sync_ff[1];
        end
    end

endmodule
```

---

## Multi-Bit CDC Techniques

### Problem with Multi-Bit Crossing

```systemverilog
// WRONG: Direct multi-bit crossing
// Different bits may be sampled at different times
logic [7:0] data_src, data_dst;

always_ff @(posedge clk_src)
    data_src <= /* some value */;

always_ff @(posedge clk_dst)
    data_dst <= data_src;  // UNSAFE!
```

### Gray Code Synchronizer

For counters and addresses (only 1 bit changes at a time):

**Why Gray Code?**
```
Problem with Binary Counter Crossing CDC:

Binary: 3→4 transition (0011 → 0100)
        ║ ║ ║ ║
        ║ ║ ║ ╚═ bit 0: 1→0
        ║ ║ ╚═══ bit 1: 1→0
        ║ ╚═════ bit 2: 0→1
        ╚═══════ bit 3: 0→0

ALL 3 bits change simultaneously!

Sampling during transition can give ANY value:
0011 (3) ──→ 0100 (4)
         ↓ Possible samples:
    0000 (0), 0001 (1), 0010 (2), 0011 (3),
    0100 (4), 0101 (5), 0110 (6), 0111 (7)

Gray Code Solution:

Gray: 3→4 transition (0010 → 0110)
      ║ ║ ║ ║
      ║ ║ ║ ╚═ bit 0: 0→0 (no change)
      ║ ║ ╚═══ bit 1: 1→1 (no change)
      ║ ╚═════ bit 2: 0→1 (ONLY THIS BIT CHANGES!)
      ╚═══════ bit 3: 0→0 (no change)

Only 1 bit changes per increment!
Sampling gives either correct value or previous value - no random values!
```

**Gray Code Conversion:**
```
Binary to Gray:           Gray to Binary:
G[n] = B[n] ^ B[n+1]     B[MSB] = G[MSB]
                         B[i] = B[i+1] ^ G[i]

Decimal  Binary  Gray    Decimal  Binary  Gray
───────────────────────  ───────────────────────
   0     0000   0000        8     1000   1100
   1     0001   0001        9     1001   1101
   2     0010   0011       10     1010   1111
   3     0011   0010       11     1011   1110
   4     0100   0110       12     1100   1010
   5     0101   0111       13     1101   1011
   6     0110   0101       14     1110   1001
   7     0111   0100       15     1111   1000

Notice: Only 1 bit changes between consecutive values!
```

**Gray Code CDC Architecture:**
```
Source Domain          |     Destination Domain
                      |
Binary ─►[Bin→Gray]───┼───►[2-FF  ]──►[Gray→Bin]──► Binary
Counter   Convert     |     Sync       Convert      Output
        (clk_src)     |   (clk_dst)   (clk_dst)
                     CDC
                  Boundary
```

```systemverilog
module gray_sync #(
    parameter WIDTH = 4
)(
    input  clk_src,
    input  clk_dst,
    input  rst_n,
    input  [WIDTH-1:0] binary_in,
    output logic [WIDTH-1:0] binary_out
);
    // Convert binary to Gray in source domain
    logic [WIDTH-1:0] gray_src;

    always_ff @(posedge clk_src or negedge rst_n) begin
        if (!rst_n)
            gray_src <= '0;
        else
            gray_src <= binary_in ^ (binary_in >> 1);
    end

    // Synchronize Gray code
    logic [WIDTH-1:0] gray_sync1, gray_sync2;

    always_ff @(posedge clk_dst or negedge rst_n) begin
        if (!rst_n) begin
            gray_sync1 <= '0;
            gray_sync2 <= '0;
        end else begin
            gray_sync1 <= gray_src;
            gray_sync2 <= gray_sync1;
        end
    end

    // Convert Gray back to binary in destination domain
    logic [WIDTH-1:0] binary_dst;

    always_comb begin
        binary_dst[WIDTH-1] = gray_sync2[WIDTH-1];
        for (int i = WIDTH-2; i >= 0; i--) begin
            binary_dst[i] = binary_dst[i+1] ^ gray_sync2[i];
        end
    end

    always_ff @(posedge clk_dst or negedge rst_n) begin
        if (!rst_n)
            binary_out <= '0;
        else
            binary_out <= binary_dst;
    end

endmodule
```

**Detailed Waveform - Gray Code Counter CDC:**
```
Source Domain (clk_src = 100 MHz)
──────────────────────────────────────────────────────────────────

clk_src      ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐
             └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘

binary_in    ──0───1───2───3───4───5───6───7───8───9──
             (0000)(0001)(0010)(0011)(0100)(0101)(0110)(0111)(1000)(1001)

gray_src     ──0───1───3───2───6───7───5───4───12──13─
             (0000)(0001)(0011)(0010)(0110)(0111)(0101)(0100)(1100)(1101)
                       ↑ Only 1 bit changes each time!


Destination Domain (clk_dst = 60 MHz)
──────────────────────────────────────────────────────────────────

clk_dst      ┐   ┌   ┐   ┌   ┐   ┌   ┐   ┌   ┐   ┌   ┐   ┌
             └───┘   └───┘   └───┘   └───┘   └───┘   └───┘

gray_sync1   ──────0───1───3───2───6───7───5───4──12──13──
             (delayed by 1 clk_dst cycle)

gray_sync2   ────────0───1───3───2───6───7───5───4──12──
             (delayed by 2 clk_dst cycles)

binary_out   ────────0───1───3───2───6───7───5───4──12──
             (converted back to binary)


Bit-level View of 3→4 Transition:
──────────────────────────────────────────────────────────────────

Binary:  0011 (3) ──→ 0100 (4)
         ║║║╚══════════════════ bit[0]: 1→0 ⚠
         ║║╚═══════════════════ bit[1]: 1→0 ⚠
         ║╚════════════════════ bit[2]: 0→1 ⚠
         ╚═════════════════════ bit[3]: 0→0

Gray:    0010 (3) ──→ 0110 (4)
         ║║║╚══════════════════ bit[0]: 0→0 ✓
         ║║╚═══════════════════ bit[1]: 1→1 ✓
         ║╚════════════════════ bit[2]: 0→1 ← ONLY THIS CHANGES
         ╚═════════════════════ bit[3]: 0→0 ✓

If sampled during transition:
  Binary: Could read 0000,0001,0010,0011,0100,0101,0110,0111 ⚠ DANGEROUS
  Gray:   Can only read 0010 or 0110 ✓ SAFE (old or new value)


FIFO Pointer Application:
──────────────────────────────────────────────────────────────────

Write Domain                   |  Read Domain
                              |
wr_ptr (binary) ─►[Bin→Gray]──┼──►[Sync]──►[Gray→Bin]──► wr_ptr_sync
                              |   (2-FF)
                             CDC
                          Boundary

Empty/Full Calculation:
  empty = (rd_ptr_gray == wr_ptr_gray_sync)
  full  = (wr_ptr_gray_next == {~rd_ptr_gray_sync[MSB:MSB-1],
                                 rd_ptr_gray_sync[MSB-2:0]})

Gray code ensures pointer comparisons are glitch-free!
```

**When to Use Gray Code:**
```
✓ USE Gray Code for:
  • Counter/pointer synchronization
  • FIFO read/write pointers
  • Sequential address crossing
  • Any incrementing/decrementing value

✗ DON'T USE Gray Code for:
  • Random data values
  • Non-sequential changes
  • Multi-bit buses with arbitrary data
  • Values that can change by >1 at a time

For arbitrary multi-bit data, use:
  • Handshaking protocols
  • MUX recirculation
  • Asynchronous FIFO
```

### MUX Recirculation Synchronizer

For multi-bit data buses:

```systemverilog
module mux_recirc_sync #(
    parameter WIDTH = 8
)(
    input  clk_src,
    input  clk_dst,
    input  rst_n,
    input  [WIDTH-1:0] data_in,
    input  valid_in,
    output logic [WIDTH-1:0] data_out,
    output logic valid_out
);
    // Source domain: Hold data stable
    logic [WIDTH-1:0] data_hold;
    logic req_toggle;

    always_ff @(posedge clk_src or negedge rst_n) begin
        if (!rst_n) begin
            data_hold <= '0;
            req_toggle <= 1'b0;
        end else if (valid_in) begin
            data_hold <= data_in;
            req_toggle <= ~req_toggle;
        end
    end

    // Synchronize request toggle
    logic [2:0] req_sync;

    always_ff @(posedge clk_dst or negedge rst_n) begin
        if (!rst_n)
            req_sync <= 3'b0;
        else
            req_sync <= {req_sync[1:0], req_toggle};
    end

    // Destination domain: Sample when stable
    logic req_sync_prev;

    always_ff @(posedge clk_dst or negedge rst_n) begin
        if (!rst_n) begin
            data_out <= '0;
            valid_out <= 1'b0;
            req_sync_prev <= 1'b0;
        end else begin
            req_sync_prev <= req_sync[2];
            valid_out <= req_sync[2] ^ req_sync_prev;
            if (req_sync[2] ^ req_sync_prev)
                data_out <= data_hold;
        end
    end

endmodule
```

---

## FIFO-Based CDC

### Asynchronous FIFO

Essential for high-throughput CDC with different clock frequencies:

```systemverilog
module async_fifo #(
    parameter DATA_WIDTH = 8,
    parameter ADDR_WIDTH = 4
)(
    // Write interface
    input  wr_clk,
    input  wr_rst_n,
    input  wr_en,
    input  [DATA_WIDTH-1:0] wr_data,
    output logic wr_full,

    // Read interface
    input  rd_clk,
    input  rd_rst_n,
    input  rd_en,
    output logic [DATA_WIDTH-1:0] rd_data,
    output logic rd_empty
);
    localparam DEPTH = 2**ADDR_WIDTH;

    // Memory array
    logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];

    // Write and read pointers (Gray coded)
    logic [ADDR_WIDTH:0] wr_ptr, wr_ptr_gray, wr_ptr_gray_sync1, wr_ptr_gray_sync2;
    logic [ADDR_WIDTH:0] rd_ptr, rd_ptr_gray, rd_ptr_gray_sync1, rd_ptr_gray_sync2;

    // Write pointer logic
    logic [ADDR_WIDTH:0] wr_ptr_next, wr_ptr_gray_next;

    always_comb begin
        wr_ptr_next = wr_ptr + (wr_en & ~wr_full);
        wr_ptr_gray_next = wr_ptr_next ^ (wr_ptr_next >> 1);
    end

    always_ff @(posedge wr_clk or negedge wr_rst_n) begin
        if (!wr_rst_n) begin
            wr_ptr <= '0;
            wr_ptr_gray <= '0;
        end else begin
            wr_ptr <= wr_ptr_next;
            wr_ptr_gray <= wr_ptr_gray_next;
        end
    end

    // Read pointer logic
    logic [ADDR_WIDTH:0] rd_ptr_next, rd_ptr_gray_next;

    always_comb begin
        rd_ptr_next = rd_ptr + (rd_en & ~rd_empty);
        rd_ptr_gray_next = rd_ptr_next ^ (rd_ptr_next >> 1);
    end

    always_ff @(posedge rd_clk or negedge rd_rst_n) begin
        if (!rd_rst_n) begin
            rd_ptr <= '0;
            rd_ptr_gray <= '0;
        end else begin
            rd_ptr <= rd_ptr_next;
            rd_ptr_gray <= rd_ptr_gray_next;
        end
    end

    // Synchronize read pointer to write clock domain
    always_ff @(posedge wr_clk or negedge wr_rst_n) begin
        if (!wr_rst_n) begin
            rd_ptr_gray_sync1 <= '0;
            rd_ptr_gray_sync2 <= '0;
        end else begin
            rd_ptr_gray_sync1 <= rd_ptr_gray;
            rd_ptr_gray_sync2 <= rd_ptr_gray_sync1;
        end
    end

    // Synchronize write pointer to read clock domain
    always_ff @(posedge rd_clk or negedge rd_rst_n) begin
        if (!rd_rst_n) begin
            wr_ptr_gray_sync1 <= '0;
            wr_ptr_gray_sync2 <= '0;
        end else begin
            wr_ptr_gray_sync1 <= wr_ptr_gray;
            wr_ptr_gray_sync2 <= wr_ptr_gray_sync1;
        end
    end

    // Full condition: write pointer catches read pointer
    assign wr_full = (wr_ptr_gray_next == {~rd_ptr_gray_sync2[ADDR_WIDTH:ADDR_WIDTH-1],
                                            rd_ptr_gray_sync2[ADDR_WIDTH-2:0]});

    // Empty condition: read pointer catches write pointer
    assign rd_empty = (rd_ptr_gray == wr_ptr_gray_sync2);

    // Write to memory
    always_ff @(posedge wr_clk) begin
        if (wr_en && !wr_full)
            mem[wr_ptr[ADDR_WIDTH-1:0]] <= wr_data;
    end

    // Read from memory
    always_ff @(posedge rd_clk or negedge rd_rst_n) begin
        if (!rd_rst_n)
            rd_data <= '0;
        else if (rd_en && !rd_empty)
            rd_data <= mem[rd_ptr[ADDR_WIDTH-1:0]];
    end

endmodule
```

---

## Handshaking Protocols

### 2-Phase (Toggle) Handshake

```systemverilog
module two_phase_handshake #(
    parameter WIDTH = 8
)(
    // Source clock domain
    input  clk_src,
    input  rst_src_n,
    input  [WIDTH-1:0] data_in,
    input  valid_in,
    output logic ready_out,

    // Destination clock domain
    input  clk_dst,
    input  rst_dst_n,
    output logic [WIDTH-1:0] data_out,
    output logic valid_out
);
    // Source domain
    logic [WIDTH-1:0] data_hold;
    logic req_toggle;
    logic [2:0] ack_sync;
    logic ack_sync_prev;

    always_ff @(posedge clk_src or negedge rst_src_n) begin
        if (!rst_src_n) begin
            data_hold <= '0;
            req_toggle <= 1'b0;
            ack_sync_prev <= 1'b0;
        end else begin
            ack_sync_prev <= ack_sync[2];

            if (valid_in && ready_out) begin
                data_hold <= data_in;
                req_toggle <= ~req_toggle;
            end
        end
    end

    assign ready_out = (req_toggle == ack_sync[2]);

    // Synchronize request to destination
    logic [2:0] req_sync;

    always_ff @(posedge clk_dst or negedge rst_dst_n) begin
        if (!rst_dst_n)
            req_sync <= 3'b0;
        else
            req_sync <= {req_sync[1:0], req_toggle};
    end

    // Destination domain
    logic req_sync_prev;
    logic ack_toggle;

    always_ff @(posedge clk_dst or negedge rst_dst_n) begin
        if (!rst_dst_n) begin
            data_out <= '0;
            valid_out <= 1'b0;
            req_sync_prev <= 1'b0;
            ack_toggle <= 1'b0;
        end else begin
            req_sync_prev <= req_sync[2];
            valid_out <= req_sync[2] ^ req_sync_prev;

            if (req_sync[2] ^ req_sync_prev) begin
                data_out <= data_hold;
                ack_toggle <= ~ack_toggle;
            end
        end
    end

    // Synchronize acknowledge back to source
    always_ff @(posedge clk_src or negedge rst_src_n) begin
        if (!rst_src_n)
            ack_sync <= 3'b0;
        else
            ack_sync <= {ack_sync[1:0], ack_toggle};
    end

endmodule
```

**Detailed Waveform - 2-Phase Handshake:**
```
Two-Phase Protocol Phases:
  Phase 1: REQ toggle → ACK toggle
  Phase 2: Data transfer complete

Source Domain (clk_src = 100 MHz)
──────────────────────────────────────────────────────────────────────

clk_src      ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐
             └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘

valid_in     ────┐               ┌───────────────┐
                 └───────────────┘               └───────────────────

data_in      ────< D1 >───────────< D2 >────────────────────────────

data_hold    ────────< D1 >───────────────< D2 >────────────────────
                    ↑ Captured             ↑ Captured

req_toggle   ────────┐                           ┌───────────────────
                     └───────────────────────────┘
                     ↑ Phase 1: REQ toggles

ready_out    ────┐           ┌───────────┐           ┌───────────────
                 └───────────┘           └───────────┘
                 ↑ Busy      ↑ Ready     ↑ Busy      ↑ Ready

ack_sync[2]  ──────────────────────┐                           ┌─────
(synced ACK)                       └───────────────────────────┘
                                   ↑ ACK arrives (3-4 cycles later)


Destination Domain (clk_dst = 80 MHz)
──────────────────────────────────────────────────────────────────────

clk_dst      ┐   ┌   ┐   ┌   ┐   ┌   ┐   ┌   ┐   ┌   ┐   ┌   ┐   ┌
             └───┘   └───┘   └───┘   └───┘   └───┘   └───┘   └───┘

req_sync[2]  ────────────┐                                   ┌───────
(synced REQ)             └───────────────────────────────────┘
                         ↑ REQ arrives (2-3 cycles latency)

valid_out    ────────────┐ ┌─────────────────────────────┐ ┌────────
                         └─┘                             └─┘
                         ↑ Pulse on REQ toggle           ↑ Pulse on toggle

data_out     ────────────< D1 >─────────────────────────< D2 >──────
                         ↑ Sampled                       ↑ Sampled

ack_toggle   ────────────────┐                                   ┌───
                             └───────────────────────────────────┘
                             ↑ Phase 2: ACK toggles back


Timing Diagram - Complete Transaction:
──────────────────────────────────────────────────────────────────────

Event Sequence:
T0:  Source: valid_in asserted, data_in = D1
T1:  Source: data captured in data_hold, req_toggle flips
T2:  Source: ready_out de-asserted (busy)
T3-T5: CDC: req_toggle synchronizes to destination (2-3 cycles)
T5:  Dest: req_sync[2] detects toggle, valid_out pulses
T6:  Dest: data_out = data_hold (D1), ack_toggle flips
T7-T9: CDC: ack_toggle synchronizes back to source (2-3 cycles)
T9:  Source: ack_sync[2] matches req_toggle, ready_out asserted
T10: Source: Ready for next transaction

Total Latency: 6-8 clock cycles (destination clock)
Throughput: Limited by round-trip handshake time


Advantages of 2-Phase:
  ✓ Only one synchronization per direction per transaction
  ✓ Faster than 4-phase (no return-to-zero)
  ✓ Good for moderate data rates
  ✓ Toggle tracks transfer count

Disadvantages:
  ✓ More complex edge detection logic
  ✓ Requires XOR for edge detection
  ✓ Must ensure toggles don't cancel
```

### 4-Phase (REQ/ACK) Handshake

**Protocol Description:**
```
Four-Phase Protocol States:
  Phase 1: REQ asserted → Wait for ACK asserted
  Phase 2: REQ de-asserted → Wait for ACK de-asserted
  Phase 3: Return to idle
  Phase 4: Ready for next transfer

Also called "Return-to-Zero" protocol
```

```systemverilog
module four_phase_handshake #(
    parameter WIDTH = 8
)(
    // Source domain
    input  clk_src,
    input  rst_src_n,
    input  [WIDTH-1:0] data_in,
    input  valid_in,
    output logic ready_out,

    // Destination domain
    input  clk_dst,
    input  rst_dst_n,
    output logic [WIDTH-1:0] data_out,
    output logic valid_out
);
    // Source domain
    logic [WIDTH-1:0] data_hold;
    logic req;
    logic [2:0] ack_sync;

    typedef enum logic [1:0] {
        IDLE,
        WAIT_ACK,
        WAIT_ACK_LOW
    } src_state_t;

    src_state_t src_state;

    always_ff @(posedge clk_src or negedge rst_src_n) begin
        if (!rst_src_n) begin
            src_state <= IDLE;
            data_hold <= '0;
            req <= 1'b0;
            ready_out <= 1'b1;
        end else begin
            case (src_state)
                IDLE: begin
                    ready_out <= 1'b1;
                    if (valid_in) begin
                        data_hold <= data_in;
                        req <= 1'b1;
                        ready_out <= 1'b0;
                        src_state <= WAIT_ACK;
                    end
                end

                WAIT_ACK: begin
                    if (ack_sync[2]) begin
                        req <= 1'b0;
                        src_state <= WAIT_ACK_LOW;
                    end
                end

                WAIT_ACK_LOW: begin
                    if (!ack_sync[2]) begin
                        src_state <= IDLE;
                    end
                end
            endcase
        end
    end

    // Synchronize request to destination
    logic [2:0] req_sync;

    always_ff @(posedge clk_dst or negedge rst_dst_n) begin
        if (!rst_dst_n)
            req_sync <= 3'b0;
        else
            req_sync <= {req_sync[1:0], req};
    end

    // Destination domain
    logic ack;

    typedef enum logic [1:0] {
        DST_IDLE,
        DST_ACK,
        DST_WAIT_REQ_LOW
    } dst_state_t;

    dst_state_t dst_state;

    always_ff @(posedge clk_dst or negedge rst_dst_n) begin
        if (!rst_dst_n) begin
            dst_state <= DST_IDLE;
            data_out <= '0;
            valid_out <= 1'b0;
            ack <= 1'b0;
        end else begin
            valid_out <= 1'b0;

            case (dst_state)
                DST_IDLE: begin
                    if (req_sync[2]) begin
                        data_out <= data_hold;
                        valid_out <= 1'b1;
                        ack <= 1'b1;
                        dst_state <= DST_ACK;
                    end
                end

                DST_ACK: begin
                    dst_state <= DST_WAIT_REQ_LOW;
                end

                DST_WAIT_REQ_LOW: begin
                    if (!req_sync[2]) begin
                        ack <= 1'b0;
                        dst_state <= DST_IDLE;
                    end
                end
            endcase
        end
    end

    // Synchronize acknowledge back to source
    always_ff @(posedge clk_src or negedge rst_src_n) begin
        if (!rst_src_n)
            ack_sync <= 3'b0;
        else
            ack_sync <= {ack_sync[1:0], ack};
    end

endmodule
```

**Detailed Waveform - 4-Phase Handshake:**
```
Four-Phase Protocol State Machine:
  Source: IDLE → WAIT_ACK → WAIT_ACK_LOW → IDLE
  Dest:   IDLE → ACK → WAIT_REQ_LOW → IDLE

Source Domain (clk_src = 100 MHz)
──────────────────────────────────────────────────────────────────────────────

clk_src      ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐ ┐
             └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘

valid_in     ────┐                               ┌───
                 └───────────────────────────────┘

data_in      ────< D1 >─────────────────────────────< D2 >─────────────────

data_hold    ────────< D1 >───────────────────────────────< D2 >───────────
                    ↑ Latched                             ↑ Latched

req          ────────┐                           ┌───────────┐
                     └───────────────────────────┘           └───────────────
                     │←─ Phase 1: Asserted ─────→│←─ Phase 2: De-asserted ─→│

ready_out    ────┐       ┌───────────────────────────────────┐
                 └───────┘                                   └───────────────
                 IDLE  WAIT_ACK      WAIT_ACK_LOW            IDLE

ack_sync[2]  ──────────────────┐                   ┌───────────────────────
(synced ACK)                   └───────────────────┘
                               ↑ Phase 1: ACK high ↑ Phase 2: ACK low
                               (2-3 cycle delay)    (2-3 cycle delay)


Destination Domain (clk_dst = 80 MHz)
──────────────────────────────────────────────────────────────────────────────

clk_dst      ┐   ┌   ┐   ┌   ┐   ┐   ┌   ┐   ┌   ┐   ┌   ┐   ┌   ┐   ┌
             └───┘   └───┘   └───┘   └───┘   └───┘   └───┘   └───┘   └───┘

req_sync[2]  ────────────┐                                   ┌───────────────
(synced REQ)             └───────────────────────────────────┘
                         ↑ REQ synchronized                   ↑ REQ cleared

valid_out    ────────────┐ ┌─────────────────────────────────────────────────
                         └─┘
                         ↑ Pulse when data valid

data_out     ────────────< D1 >─────────────────────────────< D2 >─────────
                         ↑ Data captured                     ↑ New data

ack          ────────────────┐                   ┌───────────────┐
                             └───────────────────┘               └───────────
                             │←─ ACK asserted ──→│←─ ACK cleared ─→│

dst_state    ──IDLE──────────ACK─WAIT_REQ_LOW────IDLE────────ACK──WAIT───


Complete Transaction Timeline:
──────────────────────────────────────────────────────────────────────────────

T0:  Source IDLE: valid_in=1, latch data, assert REQ, go to WAIT_ACK
T1-3:  CDC: REQ synchronizing to destination (2-3 cycles)
T3:  Dest IDLE: req_sync[2]=1, output data, assert ACK, go to DST_ACK
T4:  Dest DST_ACK: go to WAIT_REQ_LOW
T5-7:  CDC: ACK synchronizing back to source (2-3 cycles)
T7:  Source WAIT_ACK: ack_sync[2]=1, de-assert REQ, go to WAIT_ACK_LOW
T8-10: CDC: REQ falling edge synchronizing (2-3 cycles)
T10: Dest WAIT_REQ_LOW: req_sync[2]=0, de-assert ACK, go to IDLE
T11-13: CDC: ACK falling edge synchronizing (2-3 cycles)
T13: Source WAIT_ACK_LOW: ack_sync[2]=0, go to IDLE, ready for next

Total Latency: ~13-16 clock cycles (destination clock)
Throughput: Lower than 2-phase due to return-to-zero


State Transitions Diagram:
──────────────────────────────────────────────────────────────────────────────

Source FSM:

       ┌─────────────────────┐
       │       IDLE          │ ready_out = 1
       │  (ready for data)   │
       └──────────┬──────────┘
                  │ valid_in=1
                  ↓ req=1
       ┌──────────────────────┐
       │      WAIT_ACK        │ ready_out = 0
       │  (waiting for ACK)   │
       └──────────┬───────────┘
                  │ ack_sync[2]=1
                  ↓ req=0
       ┌──────────────────────┐
       │   WAIT_ACK_LOW       │ ready_out = 0
       │ (waiting ACK clear)  │
       └──────────┬───────────┘
                  │ ack_sync[2]=0
                  ↓
       ┌──────────────────────┐
       │       IDLE           │ ready_out = 1
       └──────────────────────┘


Destination FSM:

       ┌─────────────────────┐
       │     DST_IDLE        │
       │  (waiting for REQ)  │
       └──────────┬──────────┘
                  │ req_sync[2]=1
                  ↓ ack=1, valid_out=1
       ┌──────────────────────┐
       │      DST_ACK         │
       │   (ACK asserted)     │
       └──────────┬───────────┘
                  │ (1 cycle)
                  ↓
       ┌──────────────────────┐
       │  DST_WAIT_REQ_LOW    │
       │ (waiting REQ clear)  │
       └──────────┬───────────┘
                  │ req_sync[2]=0
                  ↓ ack=0
       ┌──────────────────────┐
       │     DST_IDLE         │
       └──────────────────────┘


Comparison: 2-Phase vs 4-Phase
──────────────────────────────────────────────────────────────────────────────

Characteristic         │  2-Phase (Toggle)  │  4-Phase (REQ/ACK)
───────────────────────┼────────────────────┼─────────────────────
Signal transitions     │  2 per transfer    │  4 per transfer
Latency               │  6-8 cycles        │  13-16 cycles
Throughput            │  Higher            │  Lower
Protocol complexity    │  Medium            │  Simple
State machine         │  Edge detection    │  Level detection
Metastability risk    │  Lower             │  Lower
Power consumption     │  Lower             │  Higher (more toggles)
Common usage          │  Moderate speed    │  Slow, reliable

Advantages of 4-Phase:
  ✓ Simple level-based detection (no edge logic)
  ✓ Very robust and reliable
  ✓ Clear handshake states
  ✓ Easy to debug (levels visible)
  ✓ Industry standard for reliable CDC

Disadvantages:
  ✗ Slower (4 transitions vs 2)
  ✗ More power (more signal transitions)
  ✗ Lower throughput
  ✗ More CDC cycles per transaction
```

---

## Advanced CDC Techniques

### Convergence Synchronizer

For slow-to-fast clock domain crossing:

```systemverilog
module convergence_sync (
    input  clk_slow,
    input  clk_fast,
    input  rst_n,
    input  data_in,
    output logic data_out
);
    logic data_slow;
    logic [2:0] sync_ff;

    // Register in slow domain
    always_ff @(posedge clk_slow or negedge rst_n) begin
        if (!rst_n)
            data_slow <= 1'b0;
        else
            data_slow <= data_in;
    end

    // Sample multiple times in fast domain
    always_ff @(posedge clk_fast or negedge rst_n) begin
        if (!rst_n)
            sync_ff <= 3'b0;
        else
            sync_ff <= {sync_ff[1:0], data_slow};
    end

    // Majority voting
    always_ff @(posedge clk_fast or negedge rst_n) begin
        if (!rst_n)
            data_out <= 1'b0;
        else
            data_out <= (sync_ff[2] & sync_ff[1]) |
                       (sync_ff[1] & sync_ff[0]) |
                       (sync_ff[2] & sync_ff[0]);
    end

endmodule
```

### Bus Synchronizer with Valid/Ready

```systemverilog
module bus_sync_valid_ready #(
    parameter WIDTH = 32
)(
    input  clk_src,
    input  rst_src_n,
    input  [WIDTH-1:0] data_in,
    input  valid_in,
    output logic ready_out,

    input  clk_dst,
    input  rst_dst_n,
    output logic [WIDTH-1:0] data_out,
    output logic valid_out,
    input  ready_in
);
    // Source domain: Store data
    logic [WIDTH-1:0] data_store;
    logic req_toggle, req_pending;
    logic [2:0] ack_sync;
    logic ack_sync_d;

    always_ff @(posedge clk_src or negedge rst_src_n) begin
        if (!rst_src_n) begin
            data_store <= '0;
            req_toggle <= 1'b0;
            req_pending <= 1'b0;
            ack_sync_d <= 1'b0;
        end else begin
            ack_sync_d <= ack_sync[2];

            // Detect acknowledge
            if (ack_sync[2] ^ ack_sync_d)
                req_pending <= 1'b0;

            // Accept new data
            if (valid_in && !req_pending) begin
                data_store <= data_in;
                req_toggle <= ~req_toggle;
                req_pending <= 1'b1;
            end
        end
    end

    assign ready_out = !req_pending;

    // Synchronize to destination
    logic [2:0] req_sync;

    always_ff @(posedge clk_dst or negedge rst_dst_n) begin
        if (!rst_dst_n)
            req_sync <= 3'b0;
        else
            req_sync <= {req_sync[1:0], req_toggle};
    end

    // Destination domain
    logic req_sync_d, ack_toggle;

    always_ff @(posedge clk_dst or negedge rst_dst_n) begin
        if (!rst_dst_n) begin
            data_out <= '0;
            valid_out <= 1'b0;
            req_sync_d <= 1'b0;
            ack_toggle <= 1'b0;
        end else begin
            req_sync_d <= req_sync[2];

            // New data arrival
            if ((req_sync[2] ^ req_sync_d) && !valid_out) begin
                data_out <= data_store;
                valid_out <= 1'b1;
            end

            // Data accepted
            if (valid_out && ready_in) begin
                valid_out <= 1'b0;
                ack_toggle <= ~ack_toggle;
            end
        end
    end

    // Synchronize acknowledge back
    always_ff @(posedge clk_src or negedge rst_src_n) begin
        if (!rst_src_n)
            ack_sync <= 3'b0;
        else
            ack_sync <= {ack_sync[1:0], ack_toggle};
    end

endmodule
```

---

## CDC Verification

### Static CDC Verification

Tools like Synopsys SpyGlass, Cadence Conformal, Siemens Questa CDC:

```tcl
# Example SpyGlass CDC setup
set_option top my_design
set_option enableSV09 yes

# Define clock domains
create_clock -name clk_a -period 10 [get_ports clk_a]
create_clock -name clk_b -period 15 [get_ports clk_b]

# Mark asynchronous clocks
set_clock_groups -asynchronous -group clk_a -group clk_b

# Run CDC analysis
run_spyglass -goal cdc/cdc_setup
```

### Formal Verification

```systemverilog
// SVA assertions for CDC
module cdc_assertions (
    input clk_src,
    input clk_dst,
    input rst_n,
    input data_async,
    input data_sync
);
    // Check synchronizer depth
    property sync_depth;
        @(posedge clk_dst) disable iff (!rst_n)
        $past(data_async, 2) == data_sync;
    endproperty

    // Check metastability attributes
    property no_fanout_first_stage;
        // First stage should not fan out
    endproperty

    assert property (sync_depth);

endmodule
```

### Simulation-Based Verification

```systemverilog
// Testbench with random clock ratios
module cdc_tb;
    logic clk_src, clk_dst, rst_n;
    logic [7:0] data_in, data_out;
    logic valid_in, valid_out;

    // Random clock generation
    initial begin
        clk_src = 0;
        forever #(10 + $urandom_range(0, 5)) clk_src = ~clk_src;
    end

    initial begin
        clk_dst = 0;
        forever #(15 + $urandom_range(0, 5)) clk_dst = ~clk_dst;
    end

    // DUT instantiation
    async_fifo #(.DATA_WIDTH(8), .ADDR_WIDTH(4)) dut (.*);

    // Scoreboard
    logic [7:0] write_queue[$];
    logic [7:0] read_queue[$];

    always @(posedge clk_src) begin
        if (valid_in && !dut.wr_full) begin
            write_queue.push_back(data_in);
        end
    end

    always @(posedge clk_dst) begin
        if (valid_out) begin
            read_queue.push_back(data_out);
        end
    end

    // Check data integrity
    final begin
        assert (write_queue == read_queue) else
            $error("Data mismatch!");
    end

endmodule
```

---

## Best Practices

### Design Guidelines

1. **Minimize CDC Crossings**
   - Group signals into same clock domain
   - Use FIFOs for bulk transfers
   - Consolidate control signals

2. **Use Proven Synchronizers**
   - Use standard 2-FF synchronizer for single bits
   - Use Gray code for counters
   - Use handshaking for multi-bit data

3. **Proper Reset Strategies**
   ```systemverilog
   // Good: Asynchronous assert, synchronous de-assert
   logic rst_sync1, rst_sync2;

   always_ff @(posedge clk or negedge rst_n_async) begin
       if (!rst_n_async) begin
           rst_sync1 <= 1'b0;
           rst_sync2 <= 1'b0;
       end else begin
           rst_sync1 <= 1'b1;
           rst_sync2 <= rst_sync1;
       end
   end

   assign rst_n_sync = rst_sync2;
   ```

4. **Prevent Logic Optimization**
   ```systemverilog
   (* ASYNC_REG = "TRUE" *)  // Xilinx
   (* preserve *)             // Generic
   (* dont_touch = "true" *)  // Synopsys
   logic sync_ff1, sync_ff2;
   ```

5. **Timing Constraints**
   ```tcl
   # SDC constraints
   set_false_path -from [get_clocks clk_a] -to [get_clocks clk_b]
   set_max_delay -from [get_clocks clk_a] -to [get_clocks clk_b] 5.0
   ```

### Coding Guidelines

1. **Never use combinational logic between domains**
2. **Always register signals before CDC**
3. **Document all CDC crossings**
4. **Use consistent naming conventions** (e.g., `signal_clka`, `signal_clkb`)
5. **Avoid using async signals in complex logic**

---

## Common Pitfalls

### 1. Missing Synchronization

```systemverilog
// WRONG
always_ff @(posedge clk_b)
    data_b <= data_a;  // Direct crossing!

// CORRECT
always_ff @(posedge clk_b) begin
    data_sync1 <= data_a;
    data_b <= data_sync1;
end
```

### 2. Synchronizer on Multiple Bits

```systemverilog
// WRONG - Different bits may arrive at different times
logic [7:0] data_sync1, data_sync2;
always_ff @(posedge clk_b) begin
    data_sync1 <= data_a[7:0];
    data_sync2 <= data_sync1;
end

// CORRECT - Use Gray code or handshake
```

### 3. Logic Between Synchronizer Stages

```systemverilog
// WRONG
always_ff @(posedge clk_b)
    sync1 <= data_a;

assign intermediate = sync1 & enable;  // Logic on metastable signal!

always_ff @(posedge clk_b)
    sync2 <= intermediate;

// CORRECT
always_ff @(posedge clk_b) begin
    sync1 <= data_a;
    sync2 <= sync1;
end

assign output_signal = sync2 & enable;
```

### 4. Insufficient Pulse Width

```systemverilog
// WRONG - Pulse too short for slow clock
always_ff @(posedge clk_fast)
    pulse <= trigger;  // 1 cycle pulse

// CORRECT - Extend pulse or use toggle
always_ff @(posedge clk_fast)
    if (trigger)
        toggle <= ~toggle;
```

### 5. Reset Synchronization

```systemverilog
// WRONG - Async reset used directly
always_ff @(posedge clk or posedge rst_async)
    if (rst_async) q <= 0;

// BETTER - Synchronize reset de-assertion
always_ff @(posedge clk or posedge rst_async) begin
    if (rst_async) begin
        rst_sync1 <= 0;
        rst_sync2 <= 0;
    end else begin
        rst_sync1 <= 1;
        rst_sync2 <= rst_sync1;
    end
end
```

---

## Industry Standards

### IEEE Standards

- **IEEE 1500**: Test wrapper for embedded cores
- **IEEE 1149.1**: JTAG boundary scan
- **IEEE 1687**: Internal JTAG (IJTAG)

### Design Automation Standards

- **CPF (Common Power Format)**: Power intent specification
- **UPF (Unified Power Format)**: IEEE 1801 for power management
- **SDC (Synopsys Design Constraints)**: Timing constraints

### CDC Check Standards

```systemverilog
// Standard CDC checks to pass:
// 1. No combinational logic in sync path
// 2. Minimum 2 flops for synchronization
// 3. Synchronizer cells marked with attributes
// 4. No reconvergence of synchronized paths
// 5. Proper false path constraints
// 6. Gray coding for multi-bit counters
// 7. Control/data correlation checked
```

---

## Summary Checklist

- [ ] Identified all clock domain crossings
- [ ] Used appropriate synchronizer for each crossing type
- [ ] Added synthesis attributes to prevent optimization
- [ ] Documented all CDC paths
- [ ] Applied proper timing constraints
- [ ] Ran static CDC verification
- [ ] Verified with dynamic simulation
- [ ] Checked MTBF calculations
- [ ] Reviewed reset synchronization
- [ ] Validated data integrity through verification

---

## References and Further Reading

1. **Cliff Cummings Papers**:
   - "Clock Domain Crossing (CDC) Design & Verification Techniques Using SystemVerilog"
   - "Synthesis and Scripting Techniques for Designing Multi-Asynchronous Clock Designs"

2. **Books**:
   - "Digital Design and Computer Architecture" - Harris & Harris
   - "ASIC Design in the Silicon Sandbox" - Tuckerman & Karri

3. **Industry Papers**:
   - Synopsys: "Best Practices for CDC Verification"
   - Cadence: "Clock Domain Crossing Methodology"

4. **Standards**:
   - IEEE 1801 (UPF)
   - IEEE 1149.1 (JTAG)

---

**Document Version**: 1.0
**Last Updated**: November 2024
**Author**: Digital Design Documentation Project
