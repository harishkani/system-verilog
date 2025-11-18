# Clock Gating - Complete Guide

## Table of Contents
1. [Introduction](#introduction)
2. [Fundamental Concepts](#fundamental-concepts)
3. [Types of Clock Gating](#types-of-clock-gating)
4. [Clock Gating Cell Design](#clock-gating-cell-design)
5. [RTL Clock Gating](#rtl-clock-gating)
6. [Auto Clock Gating](#auto-clock-gating)
7. [Clock Gating Implementation](#clock-gating-implementation)
8. [Verification and Testing](#verification-and-testing)
9. [Power Analysis](#power-analysis)
10. [Best Practices](#best-practices)
11. [Advanced Techniques](#advanced-techniques)
12. [Common Issues and Solutions](#common-issues-and-solutions)
13. [Industry Standards](#industry-standards)

---

## Introduction

### What is Clock Gating?

Clock gating is a power-saving technique used in digital designs to reduce dynamic power consumption by disabling the clock signal to portions of the circuit when they are not in use.

### Why Clock Gating?

**Dynamic Power Equation**:
```
P_dynamic = α × C × V² × f

Where:
- α = switching activity factor
- C = capacitance
- V = supply voltage
- f = clock frequency
```

Clock gating reduces power by:
- Reducing switching activity (α)
- Stopping unnecessary clock transitions
- Minimizing power in idle functional units

### Power Savings

- Can reduce dynamic power by **20-70%**
- Most effective in designs with:
  - Conditional data processing
  - Pipeline stages with enable signals
  - State machines with idle states
  - Memory arrays

---

## Fundamental Concepts

### Clock Tree Power Consumption

```
Clock tree power = 30-50% of total chip power

Components:
1. Clock distribution network (buffers)
2. Sequential elements (flip-flops, latches)
3. Clock gating cells
```

### When to Gate Clocks

1. **Register with Enable**
   ```systemverilog
   // Without clock gating
   always_ff @(posedge clk)
       if (enable)
           data <= new_data;
   ```

2. **Conditional Updates**
   - State machines in idle states
   - Pipeline stages waiting for data
   - Unused functional units

3. **Power Modes**
   - Low power states
   - Sleep modes
   - Standby conditions

### Clock Gating vs. Other Techniques

| Technique | Power Reduction | Area Overhead | Complexity |
|-----------|----------------|---------------|------------|
| Clock Gating | 20-70% | Low (2-5%) | Medium |
| Power Gating | 80-95% | Medium (5-15%) | High |
| Multi-VDD | 30-50% | Medium | High |
| DVFS | 40-60% | High | Very High |

---

## Types of Clock Gating

### 1. Latch-Based Clock Gating

Most common and safest form:

```systemverilog
module latch_clock_gate (
    input  clk,
    input  enable,
    input  test_enable,
    output gated_clk
);
    logic enable_latched;

    // Level-sensitive latch
    always_latch begin
        if (!clk)
            enable_latched = enable | test_enable;
    end

    // AND gate
    assign gated_clk = clk & enable_latched;

endmodule
```

**Advantages**:
- Glitch-free operation
- No timing issues with enable signal
- Industry standard approach

**Waveform**:
```
clk          : ┐   ┌   ┐   ┌   ┐   ┌   ┐   ┌
               └───┘   └───┘   └───┘   └───┘
enable       : ────┐       ┌───────────────
                   └───────┘
enable_latched:────┐           ┌───────────
                   └───────────┘
gated_clk    : ┐   ┌   ┐   ┌           ┌
               └───┘   └───┘           └───┘
```

### 2. AND-Based Clock Gating

Simple but risky:

```systemverilog
module and_clock_gate (
    input  clk,
    input  enable,
    output gated_clk
);
    assign gated_clk = clk & enable;
endmodule
```

**Problems**:
- ⚠️ Glitches if enable changes during high clock
- ⚠️ Timing issues
- ⚠️ NOT recommended for use

### 3. Latch-Free Clock Gating

For specific low-power applications:

```systemverilog
module latch_free_clock_gate (
    input  clk,
    input  enable,
    output gated_clk
);
    logic enable_sync;

    // Synchronize enable to falling edge
    always_ff @(negedge clk)
        enable_sync <= enable;

    assign gated_clk = clk & enable_sync;

endmodule
```

### 4. Integrated Clock Gating Cell (ICG)

Standard cell provided by foundries:

```systemverilog
// Typical ICG interface
module ICG (
    input  CP,    // Clock input
    input  E,     // Enable
    input  TE,    // Test enable
    output Q      // Gated clock
);
    // Internal implementation by foundry
    // Usually includes:
    // - Latch
    // - AND/OR gates
    // - Clock tree aware design
endmodule
```

**Features**:
- Optimized for clock tree
- Low skew
- DFT features built-in
- Power/timing characterized

---

## Clock Gating Cell Design

### Standard ICG Cell

```systemverilog
module standard_icg (
    input  wire clk,
    input  wire enable,
    input  wire scan_enable,  // For DFT
    output wire clk_out
);
    logic enable_reg;

    // Latch on negative edge to avoid glitches
    always_latch begin
        if (clk == 1'b0)
            enable_reg = enable | scan_enable;
    end

    // Gate the clock
    assign clk_out = clk & enable_reg;

endmodule
```

### Negative-Edge Triggered ICG

```systemverilog
module negedge_icg (
    input  wire clk,
    input  wire enable,
    input  wire scan_enable,
    output wire clk_out
);
    logic enable_reg;

    // Latch on positive edge (for negative-edge FFs)
    always_latch begin
        if (clk == 1'b1)
            enable_reg = enable | scan_enable;
    end

    // NAND for negative edge
    assign clk_out = ~(clk | ~enable_reg);

endmodule
```

### Observation-Based Clock Gating

```systemverilog
module obs_clock_gate (
    input  clk,
    input  enable,
    input  data_in,
    input  scan_enable,
    output clk_out,
    output logic data_out
);
    logic enable_latched;
    logic enable_final;

    // Observability: check if data will actually change
    assign enable_final = enable & (data_in != data_out);

    always_latch begin
        if (!clk)
            enable_latched = enable_final | scan_enable;
    end

    assign clk_out = clk & enable_latched;

    always_ff @(posedge clk_out)
        data_out <= data_in;

endmodule
```

---

## RTL Clock Gating

### Manual Clock Gating

#### Simple Register with Enable

```systemverilog
module register_with_cg #(
    parameter WIDTH = 32
)(
    input  clk,
    input  rst_n,
    input  enable,
    input  [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);
    logic clk_gated;

    // Clock gating cell
    standard_icg u_icg (
        .clk(clk),
        .enable(enable),
        .scan_enable(1'b0),
        .clk_out(clk_gated)
    );

    // Gated register
    always_ff @(posedge clk_gated or negedge rst_n) begin
        if (!rst_n)
            data_out <= '0;
        else
            data_out <= data_in;
    end

endmodule
```

#### State Machine Clock Gating

```systemverilog
module fsm_with_cg (
    input  clk,
    input  rst_n,
    input  start,
    input  done,
    output logic busy
);
    typedef enum logic [1:0] {
        IDLE,
        ACTIVE,
        WAIT,
        DONE
    } state_t;

    state_t state, next_state;
    logic state_enable;

    // Enable only when state changes
    assign state_enable = start | done | (state != IDLE);

    // Clock gating
    logic clk_gated;
    standard_icg u_icg (
        .clk(clk),
        .enable(state_enable),
        .scan_enable(1'b0),
        .clk_out(clk_gated)
    );

    // State register with gated clock
    always_ff @(posedge clk_gated or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next_state;
    end

    // Next state logic
    always_comb begin
        next_state = state;
        busy = 1'b0;

        case (state)
            IDLE: begin
                if (start)
                    next_state = ACTIVE;
            end

            ACTIVE: begin
                busy = 1'b1;
                if (done)
                    next_state = WAIT;
            end

            WAIT: begin
                next_state = DONE;
            end

            DONE: begin
                next_state = IDLE;
            end
        endcase
    end

endmodule
```

#### Pipeline Stage Clock Gating

```systemverilog
module pipeline_stage_cg #(
    parameter WIDTH = 32
)(
    input  clk,
    input  rst_n,
    input  valid_in,
    input  [WIDTH-1:0] data_in,
    output logic valid_out,
    output logic [WIDTH-1:0] data_out
);
    logic clk_gated;

    // Gate clock when no valid data
    standard_icg u_icg (
        .clk(clk),
        .enable(valid_in),
        .scan_enable(1'b0),
        .clk_out(clk_gated)
    );

    always_ff @(posedge clk_gated or negedge rst_n) begin
        if (!rst_n) begin
            valid_out <= 1'b0;
            data_out <= '0;
        end else begin
            valid_out <= valid_in;
            data_out <= data_in;
        end
    end

endmodule
```

### Hierarchical Clock Gating

```systemverilog
module hierarchical_cg (
    input  clk,
    input  rst_n,
    input  module_enable,
    input  block_enable,
    input  reg_enable
);
    // Module level gating
    logic clk_module;
    standard_icg u_module_cg (
        .clk(clk),
        .enable(module_enable),
        .scan_enable(1'b0),
        .clk_out(clk_module)
    );

    // Block level gating
    logic clk_block;
    standard_icg u_block_cg (
        .clk(clk_module),
        .enable(block_enable),
        .scan_enable(1'b0),
        .clk_out(clk_block)
    );

    // Register level gating
    logic clk_reg;
    standard_icg u_reg_cg (
        .clk(clk_block),
        .enable(reg_enable),
        .scan_enable(1'b0),
        .clk_out(clk_reg)
    );

    // Use clk_reg for final registers
    logic [31:0] data_reg;
    always_ff @(posedge clk_reg or negedge rst_n) begin
        if (!rst_n)
            data_reg <= '0;
        else
            data_reg <= /* ... */;
    end

endmodule
```

---

## Auto Clock Gating

### Synthesis-Based Auto Clock Gating

Modern synthesis tools can automatically insert clock gating cells.

#### Design Code (Before Auto CG)

```systemverilog
module auto_cg_example (
    input  clk,
    input  rst_n,
    input  enable,
    input  [31:0] data_in,
    output logic [31:0] data_out
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            data_out <= '0;
        else if (enable)
            data_out <= data_in;
    end

endmodule
```

#### Synthesis Script (DC Example)

```tcl
# Design Compiler clock gating script

# Read design
read_verilog auto_cg_example.sv

# Set clock gating options
set_clock_gating_style \
    -sequential_cell latch \
    -minimum_bitwidth 3 \
    -control_point before \
    -control_signal scan_enable

# Enable automatic clock gating
set compile_clock_gating_through_hierarchy true

# Compile with clock gating
compile_ultra -gate_clock

# Reports
report_clock_gating -multi_stage
report_power -hierarchy
```

### Auto Clock Gating Controls

```tcl
# Minimum registers to gate
set_clock_gating_style -minimum_bitwidth 4

# Don't gate specific modules
set_clock_gating_style -no_sharing [get_designs critical_module]

# Set observation depth
set_clock_gating_style -observation_logic

# Control point insertion
set_clock_gating_style -control_point before
# Options: before, after, none
```

### Controlling Auto CG with Attributes

```systemverilog
module selective_cg (
    input  clk,
    input  rst_n,
    input  en1, en2,
    input  [31:0] data1, data2,
    output logic [31:0] out1, out2
);
    // Enable auto clock gating for this register
    (* clock_gating = "yes" *)
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            out1 <= '0;
        else if (en1)
            out1 <= data1;
    end

    // Disable auto clock gating for this register
    (* clock_gating = "no" *)
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            out2 <= '0;
        else if (en2)
            out2 <= data2;
    end

endmodule
```

---

## Clock Gating Implementation

### Granularity Levels

#### 1. Fine-Grained (Register Level)
```systemverilog
// Each register has its own clock gate
// Pros: Maximum power savings
// Cons: Higher area overhead
```

#### 2. Medium-Grained (Module Level)
```systemverilog
// Functional blocks share clock gates
// Pros: Balanced power/area
// Cons: Less granular control
```

#### 3. Coarse-Grained (Subsystem Level)
```systemverilog
// Major subsystems gated together
// Pros: Minimal area overhead
// Cons: Less power savings
```

### Multi-Stage Clock Gating

```systemverilog
module multi_stage_cg (
    input  clk,
    input  rst_n,
    input  global_enable,
    input  local_enable,
    input  [31:0] data_in,
    output logic [31:0] data_out
);
    // First stage: Global gating
    logic clk_global;
    standard_icg u_global_cg (
        .clk(clk),
        .enable(global_enable),
        .scan_enable(1'b0),
        .clk_out(clk_global)
    );

    // Second stage: Local gating
    logic clk_local;
    standard_icg u_local_cg (
        .clk(clk_global),
        .enable(local_enable),
        .scan_enable(1'b0),
        .clk_out(clk_local)
    );

    always_ff @(posedge clk_local or negedge rst_n) begin
        if (!rst_n)
            data_out <= '0;
        else
            data_out <= data_in;
    end

endmodule
```

### Clock Gating with Power Domains

```systemverilog
module power_domain_cg (
    input  clk,
    input  rst_n,
    input  pd_enable,      // Power domain enable
    input  cg_enable,      // Clock gate enable
    input  [31:0] data_in,
    output logic [31:0] data_out
);
    logic clk_gated;
    logic combined_enable;

    // Combine power domain and clock gate enables
    assign combined_enable = pd_enable & cg_enable;

    standard_icg u_icg (
        .clk(clk),
        .enable(combined_enable),
        .scan_enable(1'b0),
        .clk_out(clk_gated)
    );

    // Isolation cells would be added here for power domain
    always_ff @(posedge clk_gated or negedge rst_n) begin
        if (!rst_n)
            data_out <= '0;
        else
            data_out <= data_in;
    end

endmodule
```

---

## Verification and Testing

### Functional Verification

```systemverilog
module clock_gating_tb;
    logic clk, rst_n;
    logic enable;
    logic [31:0] data_in, data_out;
    int power_cycles;

    // DUT
    register_with_cg dut (.*);

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Monitor clock gating activity
    always @(posedge clk) begin
        if (dut.clk_gated === 1'bx || dut.clk_gated === 1'bz)
            $error("Gated clock in unknown state!");
    end

    // Count active cycles
    always @(posedge clk) begin
        if (enable)
            power_cycles++;
    end

    // Test scenarios
    initial begin
        rst_n = 0;
        enable = 0;
        data_in = 0;
        power_cycles = 0;

        #20 rst_n = 1;

        // Test 1: Verify clock gates when disabled
        #20 enable = 0;
        repeat (10) @(posedge clk);
        assert (power_cycles == 0) else
            $error("Clock not gated when disabled!");

        // Test 2: Verify clock active when enabled
        enable = 1;
        data_in = 32'hDEADBEEF;
        @(posedge clk);
        @(posedge clk);
        assert (data_out == 32'hDEADBEEF) else
            $error("Data transfer failed!");

        // Test 3: Verify no glitches
        fork
            begin
                repeat (100) begin
                    @(posedge clk);
                    enable = $random;
                end
            end
            begin
                always @(dut.clk_gated) begin
                    if ($time > 0) begin
                        #0.1; // Small delay
                        if (enable == 0 && dut.clk_gated == 1)
                            $error("Glitch detected!");
                    end
                end
            end
        join

        $finish;
    end

    // Assertions
    property no_glitch;
        @(posedge clk)
        $fell(enable) |-> ##1 !dut.clk_gated throughout ##[1:$] $rose(enable);
    endproperty

    assert property (no_glitch) else
        $error("Clock glitch when enable falls!");

endmodule
```

### DFT Considerations

```systemverilog
module cg_with_dft (
    input  clk,
    input  rst_n,
    input  enable,
    input  scan_mode,      // DFT control
    input  scan_enable,    // Scan shift enable
    input  [31:0] data_in,
    output logic [31:0] data_out
);
    logic clk_gated;
    logic cg_enable;

    // Bypass clock gating in scan mode
    assign cg_enable = enable | scan_mode;

    standard_icg u_icg (
        .clk(clk),
        .enable(cg_enable),
        .scan_enable(scan_enable),
        .clk_out(clk_gated)
    );

    always_ff @(posedge clk_gated or negedge rst_n) begin
        if (!rst_n)
            data_out <= '0;
        else
            data_out <= data_in;
    end

endmodule
```

### Coverage for Clock Gating

```systemverilog
covergroup cg_coverage @(posedge clk);
    // Cover enable signal transitions
    enable_transitions: coverpoint enable {
        bins low_to_high = (0 => 1);
        bins high_to_low = (1 => 0);
        bins stay_low = (0 => 0);
        bins stay_high = (1 => 1);
    }

    // Cover clock gating efficiency
    gating_efficiency: coverpoint enable {
        bins mostly_off = {[0:20]};
        bins balanced = {[21:80]};
        bins mostly_on = {[81:100]};
    }

    // Cross coverage
    enable_data: cross enable, data_in {
        ignore_bins no_data_when_disabled = binsof(enable) intersect {0};
    }
endgroup
```

---

## Power Analysis

### Power Calculation

```systemverilog
// Power savings estimation
// Without clock gating:
P_total = P_clock_tree + P_registers

// With clock gating:
P_total_cg = P_clock_tree × α + P_registers × α + P_icg

Where α = activity factor (0 to 1)

// Savings:
Savings = (1 - α) × (P_clock_tree + P_registers) - P_icg
```

### Power Reports

```tcl
# Primetime PX power analysis

# Read design
read_verilog design.v
link_design

# Read switching activity
read_saif -input design.saif

# Power analysis with clock gating
report_power -hierarchy -verbose

# Compare scenarios
report_power -scenario {cg_enabled cg_disabled}

# Clock gating specific report
report_clock_gating_savings

# Output
# Clock Gating Summary:
# Total registers: 10000
# Gated registers: 8500 (85%)
# ICG cells: 250
# Power savings: 45%
```

### Activity Analysis

```systemverilog
module activity_monitor (
    input clk,
    input enable,
    input clk_gated
);
    int total_cycles;
    int active_cycles;
    int gated_cycles;
    real efficiency;

    always @(posedge clk) begin
        total_cycles++;
        if (enable)
            active_cycles++;
        if (!clk_gated)
            gated_cycles++;
    end

    final begin
        efficiency = 100.0 * gated_cycles / total_cycles;
        $display("Clock Gating Efficiency: %.2f%%", efficiency);
        $display("Active: %0d, Gated: %0d, Total: %0d",
                 active_cycles, gated_cycles, total_cycles);
    end

endmodule
```

---

## Best Practices

### Design Guidelines

1. **Use Standard ICG Cells**
   ```systemverilog
   // Good: Use library ICG
   ICG u_icg (.CP(clk), .E(enable), .Q(clk_out));

   // Bad: Manual implementation
   assign clk_out = clk & enable;  // Glitch risk!
   ```

2. **Minimum Bitwidth Threshold**
   ```systemverilog
   // Gate only if ≥ 4 registers share enable
   // Rationale: ICG overhead vs. savings
   ```

3. **Enable Signal Timing**
   ```systemverilog
   // Ensure enable is stable before rising clock edge
   // Add timing constraints:
   set_data_check -from [get_pins */enable] \
                  -to [get_pins */clk] \
                  -setup 0.5
   ```

4. **Avoid Gating Critical Paths**
   ```systemverilog
   // Don't gate high-frequency control logic
   // Clock gating adds delay: ~100-200ps
   ```

5. **Reset Handling**
   ```systemverilog
   // Reset should be independent of gated clock
   always_ff @(posedge clk_gated or negedge rst_n) begin
       if (!rst_n)
           data <= '0;  // Async reset, no clock needed
       else
           data <= new_data;
   end
   ```

### Coding Guidelines

1. **Use `if` for Enable Logic**
   ```systemverilog
   // Good: Tools recognize this pattern
   always_ff @(posedge clk)
       if (enable)
           data <= new_data;

   // Less optimal for auto-CG
   always_ff @(posedge clk)
       data <= enable ? new_data : data;
   ```

2. **Consistent Enable Signals**
   ```systemverilog
   // Good: Group registers with same enable
   always_ff @(posedge clk) begin
       if (module_enable) begin
           reg1 <= data1;
           reg2 <= data2;
           reg3 <= data3;
       end
   end

   // Less efficient: Separate enables
   always_ff @(posedge clk)
       if (en1) reg1 <= data1;
   always_ff @(posedge clk)
       if (en2) reg2 <= data2;
   ```

3. **Document Clock Gating Intent**
   ```systemverilog
   // Specify gating strategy in comments
   // CG_STRATEGY: Auto-insert ICG for enable_valid signal
   // MIN_WIDTH: 8 registers
   ```

---

## Advanced Techniques

### Data-Driven Clock Gating

```systemverilog
module data_driven_cg (
    input  clk,
    input  rst_n,
    input  enable,
    input  [31:0] data_in,
    output logic [31:0] data_out
);
    logic clk_gated;
    logic data_enable;

    // Only clock when data will change
    assign data_enable = enable && (data_in != data_out);

    standard_icg u_icg (
        .clk(clk),
        .enable(data_enable),
        .scan_enable(1'b0),
        .clk_out(clk_gated)
    );

    always_ff @(posedge clk_gated or negedge rst_n) begin
        if (!rst_n)
            data_out <= '0;
        else
            data_out <= data_in;
    end

endmodule
```

### Speculative Clock Gating

```systemverilog
module speculative_cg (
    input  clk,
    input  rst_n,
    input  enable,
    input  predict_enable,  // Look-ahead signal
    input  [31:0] data_in,
    output logic [31:0] data_out
);
    logic clk_gated;

    // Use prediction for early gating decision
    standard_icg u_icg (
        .clk(clk),
        .enable(predict_enable),
        .scan_enable(1'b0),
        .clk_out(clk_gated)
    );

    always_ff @(posedge clk_gated or negedge rst_n) begin
        if (!rst_n)
            data_out <= '0;
        else if (enable)  // Actual enable
            data_out <= data_in;
    end

endmodule
```

### Adaptive Clock Gating

```systemverilog
module adaptive_cg (
    input  clk,
    input  rst_n,
    input  enable,
    input  [31:0] data_in,
    output logic [31:0] data_out
);
    logic clk_gated;
    logic adaptive_enable;
    logic [7:0] activity_counter;

    // Track activity
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            activity_counter <= '0;
        else if (enable)
            activity_counter <= (activity_counter < 255) ?
                               activity_counter + 1 : 255;
        else if (activity_counter > 0)
            activity_counter <= activity_counter - 1;
    end

    // Adapt gating based on recent activity
    assign adaptive_enable = enable || (activity_counter > 200);

    standard_icg u_icg (
        .clk(clk),
        .enable(adaptive_enable),
        .scan_enable(1'b0),
        .clk_out(clk_gated)
    );

    always_ff @(posedge clk_gated or negedge rst_n) begin
        if (!rst_n)
            data_out <= '0;
        else if (enable)
            data_out <= data_in;
    end

endmodule
```

---

## Common Issues and Solutions

### Issue 1: Clock Glitches

**Problem**:
```systemverilog
// Glitches when enable changes during clock high
assign clk_gated = clk & enable;  // WRONG!
```

**Solution**:
```systemverilog
// Use latch-based ICG
standard_icg u_icg (.clk(clk), .enable(enable), .clk_out(clk_gated));
```

### Issue 2: Increased Clock Skew

**Problem**:
```
Clock gating adds buffers → increased skew
```

**Solution**:
```tcl
# Balanced clock tree synthesis
set_clock_tree_options -target_skew 0.1
set_clock_gating_check -hold 0.0
```

### Issue 3: DFT Coverage

**Problem**:
```systemverilog
// Scan chains broken by clock gating
```

**Solution**:
```systemverilog
// Include scan_enable in ICG
standard_icg u_icg (
    .clk(clk),
    .enable(enable | scan_mode),
    .scan_enable(scan_enable),
    .clk_out(clk_gated)
);
```

### Issue 4: Enable Timing Violations

**Problem**:
```
Enable signal arrives too late
```

**Solution**:
```tcl
# Add timing constraints
set_multicycle_path 2 -setup -from [get_pins */enable]
set_data_check -setup 0.5 -from enable -to clk
```

### Issue 5: Over-Gating

**Problem**:
```systemverilog
// Too many small ICGs → area overhead > savings
```

**Solution**:
```tcl
# Set minimum bitwidth
set_clock_gating_style -minimum_bitwidth 8
```

### Issue 6: Reset Recovery

**Problem**:
```systemverilog
// Gated clock affects reset release
```

**Solution**:
```systemverilog
// Use async reset, independent of clock
always_ff @(posedge clk_gated or negedge rst_n) begin
    if (!rst_n)  // Async, doesn't need clock
        data <= '0;
    else
        data <= new_data;
end
```

---

## Industry Standards

### Liberty Format Clock Gating

```liberty
cell (ICG) {
    area : 5.0;
    clock_gating_integrated_cell : latch_posedge;

    pin (CP) {
        direction : input;
        clock : true;
    }

    pin (E) {
        direction : input;
    }

    pin (Q) {
        direction : output;
        function : "CP & IQ";
        timing () {
            related_pin : "CP";
            timing_type : rising_edge;
        }
    }

    internal_power () {
        when : "!E";
        power(scalar) {
            values("0.001");
        }
    }
}
```

### UPF Clock Gating

```upf
# Unified Power Format
create_power_domain PD_CORE
create_power_domain PD_PERIPH

# Clock gating style for domain
set_domain_supply_net PD_CORE -primary_power_net VDD

# Clock gating cells
set_clock_gating_check -setup 0.0 [get_ports clk]

# Power state table with clock gating
add_power_state -domain PD_CORE \
    -state ACTIVE {-logic_expr {enable == 1}} \
    -state GATED {-logic_expr {enable == 0}}
```

### SDC Constraints

```sdc
# Clock gating constraints

# Define clock
create_clock -period 10 [get_ports clk]

# Clock gating check
set_clock_gating_check -setup 0.2 -hold 0.0 [get_ports clk]

# False paths for async enables
set_false_path -through [get_pins */ICG/E]

# Multicycle for enable
set_multicycle_path 2 -setup -through [get_pins */enable]
```

---

## Clock Gating Checklist

- [ ] Identified all enable-based registers
- [ ] Selected appropriate ICG cells from library
- [ ] Set minimum bitwidth threshold
- [ ] Added scan_enable for DFT
- [ ] Verified no clock glitches
- [ ] Added timing constraints for enables
- [ ] Ran power analysis (with/without CG)
- [ ] Verified clock tree skew
- [ ] Tested scan chain coverage
- [ ] Documented gating strategy
- [ ] Reviewed area vs. power trade-offs

---

## Summary

### Key Takeaways

1. **Clock gating reduces dynamic power by 20-70%**
2. **Always use latch-based ICG cells**
3. **Balance granularity vs. overhead**
4. **Include DFT considerations**
5. **Verify with both static and dynamic analysis**

### When to Use Clock Gating

✅ **Use for:**
- Registers with enable signals
- Conditional processing blocks
- State machines with idle states
- Pipeline stages with valid signals
- Low-power modes

❌ **Avoid for:**
- Always-active control logic
- < 3-4 registers per gate
- Critical timing paths
- Already low-activity circuits

---

## References

1. **Books**:
   - "Low Power Methodology Manual" - Synopsys
   - "Static Timing Analysis for Nanometer Designs" - Rakesh Chadha

2. **Papers**:
   - "Automated Clock Gating for Low Power" - IEEE
   - "Clock Gating and Its Application to Low Power Design" - ACM

3. **Tools Documentation**:
   - Synopsys Design Compiler User Guide
   - Cadence Genus Synthesis Solution
   - Siemens Questa Power Aware Simulation

4. **Standards**:
   - IEEE 1801 (UPF)
   - Liberty LEF/DEF

---

**Document Version**: 1.0
**Last Updated**: November 2024
**Author**: Digital Design Documentation Project
