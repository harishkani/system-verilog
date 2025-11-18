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

#### Key Points:
- First flip-flop may go metastable
- Second flip-flop provides time for resolution
- MTBF improves exponentially with more stages
- 2-3 stages are typical

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

### 4-Phase (REQ/ACK) Handshake

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
