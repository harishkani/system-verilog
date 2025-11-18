# Power Gating - Complete Guide

## Table of Contents
1. [Introduction](#introduction)
2. [Fundamental Concepts](#fundamental-concepts)
3. [Power Gating Architecture](#power-gating-architecture)
4. [Power Switch Design](#power-switch-design)
5. [Isolation Cells](#isolation-cells)
6. [Retention Strategies](#retention-strategies)
7. [Power State Management](#power-state-management)
8. [RTL Implementation](#rtl-implementation)
9. [UPF Power Intent](#upf-power-intent)
10. [Verification and Testing](#verification-and-testing)
11. [Physical Implementation](#physical-implementation)
12. [Advanced Techniques](#advanced-techniques)
13. [Best Practices](#best-practices)
14. [Common Issues and Solutions](#common-issues-and-solutions)

---

## Introduction

### What is Power Gating?

Power gating is an advanced low-power technique that completely shuts off power supply to inactive circuit blocks, eliminating both dynamic and leakage power in those blocks.

### Why Power Gating?

**Leakage Power Crisis**:
```
Modern CMOS (≤7nm):
- Leakage power = 40-50% of total power
- Subthreshold leakage dominates
- Gate leakage significant

Power Gating Solution:
- Reduces leakage by 80-95%
- Eliminates both dynamic and leakage power
- Essential for battery-powered devices
```

### Power Gating vs. Other Techniques

| Technique | Dynamic Power | Leakage Power | Wake-up Time | Complexity |
|-----------|---------------|---------------|--------------|------------|
| Clock Gating | ↓ 20-70% | No change | ~0 ns | Low |
| Power Gating | ↓ 100% | ↓ 80-95% | µs-ms | High |
| DVFS | ↓ 40-60% | ↓ 10-30% | ms | Very High |
| Multi-Vt | No change | ↓ 30-50% | ~0 ns | Medium |

### Applications

- Mobile SoCs (Application processors)
- IoT devices
- Wearable electronics
- Data center processors
- Automotive systems

---

## Fundamental Concepts

### Leakage Power Components

```
Total Leakage = Subthreshold + Gate + Junction

1. Subthreshold Leakage:
   I_sub = I_0 × e^((Vgs - Vth)/(n × Vt)) × (1 - e^(-Vds/Vt))

2. Gate Leakage:
   I_gate = A × J_g (tunneling current)

3. Junction Leakage:
   I_junction = A × J_j (reverse bias)
```

### Power Gating Effectiveness

```
Power Savings = P_dynamic + P_leakage - P_overhead

Where P_overhead includes:
- Power switch resistance losses
- Isolation cell power
- Retention register power
- Control logic power
```

### Key Terminology

- **Power Domain (PD)**: Region with independent power control
- **Power Switch**: Transistor controlling power supply
- **Virtual VDD/VSS**: Gated supply rails
- **Isolation Cell**: Prevents X propagation
- **Retention Register**: Maintains state during power-off
- **Always-On Domain**: Never powered down

---

## Power Gating Architecture

### Basic Power Gating Structure

```
                Always-On Domain
                ┌─────────────────────┐
                │  Power Controller   │
                │  ┌───────────────┐  │
                │  │ State Machine │  │
                │  └───────┬───────┘  │
                │          │          │
                └──────────┼──────────┘
                           │ power_en
                           ▼
         VDD ─────┬────[Power Switch]─── VDDG (Virtual VDD)
                  │                          │
                  │                    ┌─────┴─────┐
                  │                    │  Gated    │
                  │                    │  Domain   │
                  │                    │           │
         VSS ──────────────────────────┴───────────┘
```

### Power Domain Hierarchy

```systemverilog
// Multi-domain system example
/*
    TOP (Always-On)
    ├── CPU_CORE (Gated)
    │   ├── ALU (Gated)
    │   ├── FPU (Gated)
    │   └── L1_CACHE (Retention)
    ├── GPU (Gated)
    │   ├── SHADER_0 (Gated)
    │   └── SHADER_1 (Gated)
    └── PERIPHERALS (Always-On)
        ├── UART (Always-On)
        └── TIMER (Always-On)
*/
```

### Header vs. Footer Switches

```systemverilog
// Header Switch (PMOS): Controls VDD
/*
    VDD ───┬─── [PMOS Switch] ─── VDDG
           │         │
           │      Enable_n
           │
*/

// Footer Switch (NMOS): Controls VSS
/*
           ┌─── VSSG ─── [NMOS Switch] ─── VSS
           │                   │
          Load              Enable
*/
```

**Comparison**:
| Type | Pros | Cons |
|------|------|------|
| Header | Better noise immunity | Larger area (PMOS) |
| Footer | Smaller area (NMOS) | Ground bounce risk |
| Both | Best performance | 2x area overhead |

---

## Power Switch Design

### Single Power Switch

```systemverilog
module power_switch (
    input  power_en,      // Enable signal
    input  vdd,           // Real VDD
    output vddg           // Virtual VDD (gated)
);
    // Header switch (PMOS)
    pmos_sw #(.WIDTH(10)) sw (
        .g(~power_en),
        .s(vdd),
        .d(vddg)
    );

endmodule
```

### Distributed Power Switch Network

```systemverilog
module distributed_power_switches #(
    parameter NUM_SWITCHES = 16,
    parameter SWITCH_WIDTH = 50  // µm
)(
    input  power_en,
    input  vdd,
    output vddg
);
    // Multiple switches to reduce IR drop
    genvar i;
    generate
        for (i = 0; i < NUM_SWITCHES; i++) begin : sw_array
            pmos_sw #(.WIDTH(SWITCH_WIDTH)) sw (
                .g(~power_en),
                .s(vdd),
                .d(vddg)
            );
        end
    endgenerate

endmodule
```

### Power Switch Sizing

```
Key Equations:

1. IR Drop:
   V_drop = I_load × R_switch

2. Switch Resistance:
   R_switch = ρ × L / (W × t)

3. Sizing Rule:
   W_switch ≥ I_peak / (K × (VDD - Vth))

   Typical: W_switch = 100-500 µm per mA

4. Rush Current:
   I_rush = C_load × dV/dt
```

### Staged Power-Up

```systemverilog
module staged_power_switch (
    input  clk,
    input  rst_n,
    input  power_on_req,
    input  vdd,
    output logic vddg,
    output logic power_ready
);
    localparam NUM_STAGES = 4;
    logic [NUM_STAGES-1:0] stage_en;
    logic [3:0] stage_counter;

    // State machine
    typedef enum logic [1:0] {
        OFF,
        RAMPING,
        ON
    } state_t;

    state_t state;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= OFF;
            stage_counter <= 0;
            stage_en <= '0;
            power_ready <= 0;
        end else begin
            case (state)
                OFF: begin
                    power_ready <= 0;
                    if (power_on_req) begin
                        state <= RAMPING;
                        stage_counter <= 0;
                    end
                end

                RAMPING: begin
                    if (stage_counter < NUM_STAGES) begin
                        stage_en[stage_counter] <= 1'b1;
                        stage_counter <= stage_counter + 1;
                    end else begin
                        state <= ON;
                        power_ready <= 1'b1;
                    end
                end

                ON: begin
                    if (!power_on_req) begin
                        state <= OFF;
                        stage_en <= '0;
                    end
                end
            endcase
        end
    end

    // Distributed switches with staged enable
    genvar i;
    generate
        for (i = 0; i < NUM_STAGES; i++) begin : sw_stage
            pmos_sw sw (
                .g(~stage_en[i]),
                .s(vdd),
                .d(vddg)
            );
        end
    endgenerate

endmodule
```

---

## Isolation Cells

### Why Isolation?

When a power domain is off:
- Outputs float to unknown (X) values
- X propagates to always-on domains
- Causes increased power consumption
- May trigger false logic

### Isolation Cell Types

#### 1. AND-Based Isolation

```systemverilog
module iso_and (
    input  iso_en,      // Active high to isolate
    input  data_in,     // From gated domain
    output logic data_out  // To always-on domain
);
    // Clamps to 0 when isolated
    assign data_out = data_in & ~iso_en;

endmodule
```

#### 2. OR-Based Isolation

```systemverilog
module iso_or (
    input  iso_en,
    input  data_in,
    output logic data_out
);
    // Clamps to 1 when isolated
    assign data_out = data_in | iso_en;

endmodule
```

#### 3. Latch-Based Isolation

```systemverilog
module iso_latch (
    input  iso_en,
    input  data_in,
    output logic data_out
);
    logic data_latched;

    always_latch begin
        if (!iso_en)
            data_latched = data_in;
    end

    assign data_out = data_latched;

endmodule
```

#### 4. Configurable Isolation

```systemverilog
module iso_cell #(
    parameter CLAMP_VALUE = 1'b0
)(
    input  iso_en,
    input  data_in,
    output logic data_out
);
    assign data_out = iso_en ? CLAMP_VALUE : data_in;

endmodule
```

### Multi-Bit Isolation

```systemverilog
module iso_bus #(
    parameter WIDTH = 32,
    parameter CLAMP_VALUE = 32'h0
)(
    input  iso_en,
    input  [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);
    assign data_out = iso_en ? CLAMP_VALUE : data_in;

endmodule
```

### Bidirectional Isolation

```systemverilog
module iso_bidir #(
    parameter WIDTH = 8
)(
    input  iso_en_ab,   // Isolate A→B
    input  iso_en_ba,   // Isolate B→A
    input  [WIDTH-1:0] data_a,
    input  [WIDTH-1:0] data_b,
    output logic [WIDTH-1:0] data_to_a,
    output logic [WIDTH-1:0] data_to_b
);
    assign data_to_b = iso_en_ab ? '0 : data_a;
    assign data_to_a = iso_en_ba ? '0 : data_b;

endmodule
```

### Isolation Timing

```systemverilog
// Critical timing sequence:
// 1. Assert isolation BEFORE powering down
// 2. De-assert isolation AFTER power is stable

module iso_with_timing (
    input  clk,
    input  power_down_req,
    input  power_stable,
    output logic iso_en,
    output logic power_switch_en
);
    typedef enum logic [1:0] {
        ACTIVE,
        ISOLATING,
        POWERED_DOWN,
        POWERING_UP
    } state_t;

    state_t state;
    logic [3:0] delay_counter;

    always_ff @(posedge clk) begin
        case (state)
            ACTIVE: begin
                iso_en <= 1'b0;
                power_switch_en <= 1'b1;
                if (power_down_req) begin
                    state <= ISOLATING;
                    delay_counter <= 0;
                end
            end

            ISOLATING: begin
                iso_en <= 1'b1;  // Isolate first
                if (delay_counter < 4) begin
                    delay_counter <= delay_counter + 1;
                end else begin
                    power_switch_en <= 1'b0;  // Then power down
                    state <= POWERED_DOWN;
                end
            end

            POWERED_DOWN: begin
                if (!power_down_req) begin
                    power_switch_en <= 1'b1;  // Power up first
                    state <= POWERING_UP;
                    delay_counter <= 0;
                end
            end

            POWERING_UP: begin
                if (power_stable && delay_counter < 8) begin
                    delay_counter <= delay_counter + 1;
                end else if (delay_counter >= 8) begin
                    iso_en <= 1'b0;  // Remove isolation last
                    state <= ACTIVE;
                end
            end
        endcase
    end

endmodule
```

---

## Retention Strategies

### Why Retention?

- Preserve critical state during power gating
- Avoid re-initialization overhead
- Maintain context for fast wake-up
- Store configuration data

### Retention Register Types

#### 1. Balloon Retention FF

```systemverilog
module retention_ff (
    input  clk,
    input  rst_n,
    input  save,        // Save to retention latch
    input  restore,     // Restore from retention latch
    input  vdd,         // Always-on supply
    input  vddg,        // Gated supply
    input  d,
    output logic q
);
    // Main flip-flop (on VDDG)
    logic q_main;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            q_main <= 1'b0;
        else if (!restore)
            q_main <= d;
    end

    // Retention latch (on VDD - always on)
    logic q_retention;

    always_latch begin
        if (save)
            q_retention = q_main;
    end

    // Output mux
    assign q = restore ? q_retention : q_main;

endmodule
```

#### 2. Shadow Latch Retention

```systemverilog
module shadow_retention_ff (
    input  clk,
    input  rst_n,
    input  sleep_mode,
    input  vdd,
    input  vddg,
    input  d,
    output logic q
);
    // Primary storage (VDDG)
    logic q_primary;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            q_primary <= 1'b0;
        else
            q_primary <= d;
    end

    // Shadow storage (VDD)
    logic q_shadow;

    always_latch begin
        if (clk && sleep_mode)
            q_shadow = q_primary;
    end

    // Restore on wake-up
    assign q = sleep_mode ? q_shadow : q_primary;

endmodule
```

### Retention Register Bank

```systemverilog
module retention_register_bank #(
    parameter WIDTH = 32,
    parameter DEPTH = 16
)(
    input  clk,
    input  rst_n,
    input  save_state,
    input  restore_state,
    input  [$clog2(DEPTH)-1:0] addr,
    input  wr_en,
    input  [WIDTH-1:0] wr_data,
    output logic [WIDTH-1:0] rd_data
);
    // Main storage (gated domain)
    logic [WIDTH-1:0] mem_main [DEPTH];

    // Retention storage (always-on domain)
    logic [WIDTH-1:0] mem_retention [DEPTH];

    // Write operation
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < DEPTH; i++)
                mem_main[i] <= '0;
        end else if (wr_en && !restore_state) begin
            mem_main[addr] <= wr_data;
        end
    end

    // Save to retention
    always_ff @(posedge clk) begin
        if (save_state) begin
            for (int i = 0; i < DEPTH; i++)
                mem_retention[i] <= mem_main[i];
        end
    end

    // Restore from retention
    always_ff @(posedge clk) begin
        if (restore_state) begin
            for (int i = 0; i < DEPTH; i++)
                mem_main[i] <= mem_retention[i];
        end
    end

    // Read operation
    assign rd_data = restore_state ? mem_retention[addr] : mem_main[addr];

endmodule
```

### Partial Retention

```systemverilog
module partial_retention #(
    parameter TOTAL_REGS = 32,
    parameter RETAIN_REGS = 8
)(
    input  clk,
    input  rst_n,
    input  save,
    input  restore,
    input  [TOTAL_REGS-1:0] data_in,
    output logic [TOTAL_REGS-1:0] data_out
);
    // Non-retained registers
    logic [TOTAL_REGS-RETAIN_REGS-1:0] regs_normal;

    // Retained registers
    logic [RETAIN_REGS-1:0] regs_retain_main;
    logic [RETAIN_REGS-1:0] regs_retain_shadow;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            regs_normal <= '0;
            regs_retain_main <= '0;
        end else begin
            regs_normal <= data_in[TOTAL_REGS-1:RETAIN_REGS];
            if (!restore)
                regs_retain_main <= data_in[RETAIN_REGS-1:0];
        end
    end

    // Retention logic
    always_ff @(posedge clk) begin
        if (save)
            regs_retain_shadow <= regs_retain_main;
        if (restore)
            regs_retain_main <= regs_retain_shadow;
    end

    assign data_out = {regs_normal, regs_retain_main};

endmodule
```

---

## Power State Management

### Power State Table (PST)

```systemverilog
// Define power states
typedef enum logic [2:0] {
    PS_ON,          // Fully operational
    PS_RETENTION,   // Retention mode
    PS_OFF,         // Completely off
    PS_STANDBY,     // Clock gated only
    PS_TRANSITION   // Power state change
} power_state_t;
```

### Power Controller

```systemverilog
module power_controller (
    input  clk,
    input  rst_n,

    // Request interface
    input  [2:0] target_state,
    input  state_change_req,
    output logic state_change_ack,

    // Domain controls
    output logic power_switch_en,
    output logic iso_en,
    output logic save_state,
    output logic restore_state,
    output logic clk_gate_en,

    // Status
    output power_state_t current_state,
    input  power_good
);
    power_state_t next_state;
    logic [7:0] timer;

    // State machine
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_state <= PS_OFF;
            state_change_ack <= 1'b0;
            timer <= 0;
        end else begin
            if (state_change_req && current_state != PS_TRANSITION) begin
                next_state <= power_state_t'(target_state);
                current_state <= PS_TRANSITION;
                timer <= 0;
                state_change_ack <= 1'b0;
            end else if (current_state == PS_TRANSITION) begin
                timer <= timer + 1;
                // Implement state transition logic
                case (next_state)
                    PS_ON: begin
                        if (power_state_on_sequence(timer)) begin
                            current_state <= PS_ON;
                            state_change_ack <= 1'b1;
                        end
                    end

                    PS_RETENTION: begin
                        if (power_state_retention_sequence(timer)) begin
                            current_state <= PS_RETENTION;
                            state_change_ack <= 1'b1;
                        end
                    end

                    PS_OFF: begin
                        if (power_state_off_sequence(timer)) begin
                            current_state <= PS_OFF;
                            state_change_ack <= 1'b1;
                        end
                    end
                endcase
            end
        end
    end

    // Control signal generation
    always_comb begin
        // Defaults
        power_switch_en = 1'b0;
        iso_en = 1'b1;
        save_state = 1'b0;
        restore_state = 1'b0;
        clk_gate_en = 1'b0;

        case (current_state)
            PS_ON: begin
                power_switch_en = 1'b1;
                iso_en = 1'b0;
                clk_gate_en = 1'b1;
            end

            PS_RETENTION: begin
                power_switch_en = 1'b0;
                iso_en = 1'b1;
                clk_gate_en = 1'b0;
            end

            PS_OFF: begin
                power_switch_en = 1'b0;
                iso_en = 1'b1;
                clk_gate_en = 1'b0;
            end

            PS_STANDBY: begin
                power_switch_en = 1'b1;
                iso_en = 1'b0;
                clk_gate_en = 1'b0;
            end
        endcase
    end

    // Transition sequence functions
    function automatic logic power_state_on_sequence(input logic [7:0] t);
        // Step 1: Enable power (t=0-10)
        // Step 2: Wait for power good (t=11-20)
        // Step 3: Restore state (t=21-25)
        // Step 4: De-assert isolation (t=26-30)
        // Step 5: Enable clock (t=31)
        return (t > 31);
    endfunction

    function automatic logic power_state_retention_sequence(input logic [7:0] t);
        // Step 1: Save state (t=0-5)
        // Step 2: Gate clock (t=6)
        // Step 3: Assert isolation (t=7-10)
        // Step 4: Disable power (t=11)
        return (t > 11);
    endfunction

    function automatic logic power_state_off_sequence(input logic [7:0] t);
        // Step 1: Gate clock (t=0)
        // Step 2: Assert isolation (t=1-5)
        // Step 3: Disable power (t=6)
        return (t > 6);
    endfunction

endmodule
```

### Multi-Domain Power Manager

```systemverilog
module multi_domain_power_manager #(
    parameter NUM_DOMAINS = 4
)(
    input  clk,
    input  rst_n,

    // Domain requests
    input  [NUM_DOMAINS-1:0] domain_power_req,
    output logic [NUM_DOMAINS-1:0] domain_power_ack,

    // Domain controls
    output logic [NUM_DOMAINS-1:0] power_switch_en,
    output logic [NUM_DOMAINS-1:0] iso_en,

    // Dependencies
    input  [NUM_DOMAINS-1:0][NUM_DOMAINS-1:0] dependencies
);
    power_state_t [NUM_DOMAINS-1:0] domain_states;
    logic [NUM_DOMAINS-1:0] domain_ready;

    genvar i;
    generate
        for (i = 0; i < NUM_DOMAINS; i++) begin : domain_ctrl
            // Check dependencies
            always_comb begin
                domain_ready[i] = 1'b1;
                for (int j = 0; j < NUM_DOMAINS; j++) begin
                    if (dependencies[i][j] && domain_states[j] != PS_ON)
                        domain_ready[i] = 1'b0;
                end
            end

            // Domain power controller
            power_controller u_pwr_ctrl (
                .clk(clk),
                .rst_n(rst_n),
                .target_state(domain_power_req[i] && domain_ready[i] ? PS_ON : PS_OFF),
                .state_change_req(domain_power_req[i]),
                .state_change_ack(domain_power_ack[i]),
                .power_switch_en(power_switch_en[i]),
                .iso_en(iso_en[i]),
                .current_state(domain_states[i]),
                .power_good(1'b1)
            );
        end
    endgenerate

endmodule
```

---

## RTL Implementation

### Complete Power-Gated Module

```systemverilog
module power_gated_module #(
    parameter DATA_WIDTH = 32
)(
    // Always-on domain
    input  clk_always_on,
    input  rst_n,
    input  power_on_req,
    output logic power_ready,

    // Interface signals
    input  [DATA_WIDTH-1:0] data_in,
    input  valid_in,
    output logic [DATA_WIDTH-1:0] data_out,
    output logic valid_out
);
    // Power control signals
    logic power_switch_en;
    logic iso_en;
    logic save_state;
    logic restore_state;
    logic power_good;

    // Virtual power rails
    wire vddg;  // Gated VDD

    // Isolated signals
    logic [DATA_WIDTH-1:0] data_in_iso;
    logic valid_in_iso;

    // Power controller
    power_controller u_pwr_ctrl (
        .clk(clk_always_on),
        .rst_n(rst_n),
        .target_state(power_on_req ? PS_ON : PS_OFF),
        .state_change_req(power_on_req),
        .state_change_ack(power_ready),
        .power_switch_en(power_switch_en),
        .iso_en(iso_en),
        .save_state(save_state),
        .restore_state(restore_state),
        .power_good(power_good)
    );

    // Power switches
    distributed_power_switches #(
        .NUM_SWITCHES(8)
    ) u_pwr_sw (
        .power_en(power_switch_en),
        .vdd(1'b1),  // Would be actual VDD
        .vddg(vddg)
    );

    // Isolation cells
    iso_bus #(.WIDTH(DATA_WIDTH)) u_iso_data (
        .iso_en(iso_en),
        .data_in(data_in),
        .data_out(data_in_iso)
    );

    iso_cell u_iso_valid (
        .iso_en(iso_en),
        .data_in(valid_in),
        .data_out(valid_in_iso)
    );

    // Gated domain logic (uses VDDG)
    logic [DATA_WIDTH-1:0] internal_reg;
    logic internal_valid;

    always_ff @(posedge clk_always_on or negedge rst_n) begin
        if (!rst_n) begin
            internal_reg <= '0;
            internal_valid <= 1'b0;
        end else if (power_switch_en && !restore_state) begin
            if (valid_in_iso) begin
                internal_reg <= data_in_iso;
                internal_valid <= 1'b1;
            end
        end
    end

    // Retention for critical state
    retention_ff #(.WIDTH(DATA_WIDTH)) u_retention (
        .clk(clk_always_on),
        .rst_n(rst_n),
        .save(save_state),
        .restore(restore_state),
        .d(internal_reg),
        .q(data_out)
    );

    assign valid_out = internal_valid && power_switch_en;

endmodule
```

### Memory with Power Gating

```systemverilog
module power_gated_memory #(
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 10,
    parameter RETENTION_DEPTH = 64  // Retain first 64 words
)(
    input  clk,
    input  rst_n,
    input  power_mode,  // 0=ON, 1=RETENTION

    input  wr_en,
    input  rd_en,
    input  [ADDR_WIDTH-1:0] addr,
    input  [DATA_WIDTH-1:0] wr_data,
    output logic [DATA_WIDTH-1:0] rd_data,
    output logic ready
);
    localparam DEPTH = 2**ADDR_WIDTH;

    // Main memory (gated domain)
    logic [DATA_WIDTH-1:0] mem [DEPTH];

    // Retention memory (always-on, smaller)
    logic [DATA_WIDTH-1:0] retention_mem [RETENTION_DEPTH];

    // Power control
    logic power_switch_en;
    logic save_state;
    logic restore_state;

    assign power_switch_en = !power_mode;
    assign ready = power_switch_en;

    // Save to retention before power down
    always_ff @(posedge clk) begin
        if (power_mode && !save_state) begin
            save_state <= 1'b1;
            for (int i = 0; i < RETENTION_DEPTH; i++)
                retention_mem[i] <= mem[i];
        end else if (!power_mode) begin
            save_state <= 1'b0;
        end
    end

    // Restore on power up
    always_ff @(posedge clk) begin
        if (!power_mode && save_state) begin
            restore_state <= 1'b1;
            for (int i = 0; i < RETENTION_DEPTH; i++)
                mem[i] <= retention_mem[i];
        end else begin
            restore_state <= 1'b0;
        end
    end

    // Memory operations
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_data <= '0;
        end else if (power_switch_en) begin
            if (wr_en)
                mem[addr] <= wr_data;
            if (rd_en)
                rd_data <= mem[addr];
        end
    end

endmodule
```

---

## UPF Power Intent

### Basic UPF Example

```upf
# Create power domains
create_power_domain PD_TOP -include_scope

create_power_domain PD_CPU \
    -elements {cpu_core} \
    -scope cpu_core

create_power_domain PD_GPU \
    -elements {gpu_core} \
    -scope gpu_core

# Create supply nets
create_supply_net VDD -domain PD_TOP
create_supply_net VSS -domain PD_TOP
create_supply_net VDDG_CPU -domain PD_CPU
create_supply_net VDDG_GPU -domain PD_GPU

# Create supply ports
create_supply_port VDD -domain PD_TOP
create_supply_port VSS -domain PD_TOP

# Connect supplies
connect_supply_net VDD -ports VDD
connect_supply_net VSS -ports VSS

# Set domain supply network
set_domain_supply_net PD_TOP \
    -primary_power_net VDD \
    -primary_ground_net VSS

set_domain_supply_net PD_CPU \
    -primary_power_net VDDG_CPU \
    -primary_ground_net VSS

set_domain_supply_net PD_GPU \
    -primary_power_net VDDG_GPU \
    -primary_ground_net VSS

# Create power switches
create_power_switch SW_CPU \
    -domain PD_CPU \
    -output_supply_port {vout VDDG_CPU} \
    -input_supply_port {vin VDD} \
    -control_port {sw_en cpu_power_en} \
    -on_state {on_state vin {sw_en}} \
    -off_state {off_state {!sw_en}}

create_power_switch SW_GPU \
    -domain PD_GPU \
    -output_supply_port {vout VDDG_GPU} \
    -input_supply_port {vin VDD} \
    -control_port {sw_en gpu_power_en} \
    -on_state {on_state vin {sw_en}} \
    -off_state {off_state {!sw_en}}

# Isolation strategy
set_isolation ISO_CPU \
    -domain PD_CPU \
    -isolation_power_net VDD \
    -isolation_ground_net VSS \
    -clamp_value 0 \
    -applies_to outputs \
    -isolation_signal cpu_iso_en \
    -isolation_sense high \
    -location parent

set_isolation ISO_GPU \
    -domain PD_GPU \
    -isolation_power_net VDD \
    -isolation_ground_net VSS \
    -clamp_value 0 \
    -applies_to outputs \
    -isolation_signal gpu_iso_en \
    -isolation_sense high \
    -location parent

# Retention strategy
set_retention RET_CPU \
    -domain PD_CPU \
    -retention_power_net VDD \
    -retention_ground_net VSS \
    -save_signal {cpu_save high} \
    -restore_signal {cpu_restore high}

# Power state table
add_power_state PD_TOP \
    -state ON \
    -state OFF

add_power_state PD_CPU \
    -state ON {-logic_expr {VDD == FULL_ON && VDDG_CPU == FULL_ON}} \
    -state RET {-logic_expr {VDD == FULL_ON && VDDG_CPU == OFF}} \
    -state OFF {-logic_expr {VDDG_CPU == OFF}}

add_power_state PD_GPU \
    -state ON {-logic_expr {VDD == FULL_ON && VDDG_GPU == FULL_ON}} \
    -state OFF {-logic_expr {VDDG_GPU == OFF}}

# Level shifters (if multi-VDD)
set_level_shifter LS_CPU_TO_TOP \
    -domain PD_CPU \
    -applies_to outputs \
    -location parent \
    -threshold 0.5

# Map to library cells
map_power_switch SW_CPU \
    -lib_cells {HEADER_CELL}

map_isolation_cell ISO_CPU \
    -lib_cells {ISO_AND_CELL ISO_OR_CELL}

map_retention_cell RET_CPU \
    -lib_cells {RET_FF_CELL}
```

### Advanced UPF with PST

```upf
# Power State Table with transitions
add_pst_state CPU_ACTIVE \
    -pst PD_CPU \
    -state {ON}

add_pst_state CPU_SLEEP \
    -pst PD_CPU \
    -state {RET}

add_pst_state CPU_OFF \
    -pst PD_CPU \
    -state {OFF}

# Define legal transitions
add_pst_transition -pst PD_CPU \
    -from CPU_ACTIVE -to CPU_SLEEP \
    -latency 100ns \
    -energy {10uW * 100ns}

add_pst_transition -pst PD_CPU \
    -from CPU_SLEEP -to CPU_ACTIVE \
    -latency 1us \
    -energy {100uW * 1us}

add_pst_transition -pst PD_CPU \
    -from CPU_ACTIVE -to CPU_OFF \
    -latency 50ns \
    -energy {5uW * 50ns}

add_pst_transition -pst PD_CPU \
    -from CPU_OFF -to CPU_ACTIVE \
    -latency 10us \
    -energy {500uW * 10us}
```

---

## Verification and Testing

### Power-Aware Simulation

```systemverilog
module power_gating_tb;
    logic clk, rst_n;
    logic power_req;
    logic [31:0] data_in, data_out;
    logic valid_in, valid_out;

    // DUT
    power_gated_module dut (.*);

    // Clock
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Power monitoring
    real power_active, power_gated;
    int active_cycles, gated_cycles;

    always @(posedge clk) begin
        if (dut.power_switch_en)
            active_cycles++;
        else
            gated_cycles++;
    end

    // Test sequence
    initial begin
        $dumpfile("power_gating.vcd");
        $dumpvars(0, power_gating_tb);

        rst_n = 0;
        power_req = 0;
        data_in = 0;
        valid_in = 0;
        active_cycles = 0;
        gated_cycles = 0;

        #20 rst_n = 1;

        // Test 1: Power up
        $display("Test 1: Power up sequence");
        power_req = 1;
        wait(dut.power_ready);
        $display("  Power ready at time %t", $time);

        // Test 2: Normal operation
        $display("Test 2: Normal operation");
        repeat (10) begin
            @(posedge clk);
            data_in = $random;
            valid_in = 1;
        end

        // Test 3: Power down
        $display("Test 3: Power down sequence");
        @(posedge clk);
        power_req = 0;
        valid_in = 0;
        wait(!dut.power_switch_en);
        $display("  Power off at time %t", $time);

        // Test 4: Verify isolation
        $display("Test 4: Check isolation");
        if (dut.iso_en)
            $display("  Isolation active: PASS");
        else
            $error("  Isolation not active: FAIL");

        // Test 5: Power cycle with retention
        $display("Test 5: Power cycle");
        #100;
        power_req = 1;
        wait(dut.power_ready);
        $display("  Powered back on at time %t", $time);

        #1000;

        // Report
        $display("\n=== Power Gating Report ===");
        $display("Active cycles: %0d", active_cycles);
        $display("Gated cycles: %0d", gated_cycles);
        $display("Gating efficiency: %.2f%%",
                 100.0 * gated_cycles / (active_cycles + gated_cycles));

        $finish;
    end

    // Assertions
    property iso_before_powerdown;
        @(posedge clk)
        $fell(dut.power_switch_en) |-> dut.iso_en;
    endproperty

    property iso_after_powerup;
        @(posedge clk)
        $rose(dut.power_switch_en) |=> ##[1:10] !dut.iso_en;
    endproperty

    assert property (iso_before_powerdown) else
        $error("Isolation not asserted before power down!");

    assert property (iso_after_powerup) else
        $error("Isolation not de-asserted after power up!");

    // Coverage
    covergroup pg_coverage @(posedge clk);
        power_state: coverpoint dut.u_pwr_ctrl.current_state {
            bins states[] = {PS_ON, PS_RETENTION, PS_OFF};
            bins transitions = (PS_ON => PS_RETENTION),
                               (PS_RETENTION => PS_ON),
                               (PS_ON => PS_OFF),
                               (PS_OFF => PS_ON);
        }
    endgroup

    pg_coverage cg = new();

endmodule
```

### UPF Verification with Questa

```tcl
# Questa Power Aware Simulation
vlog -sv +define+POWER_AWARE design.sv
vlog -upf power_intent.upf

vsim -voptargs="+acc" -upf power_intent.upf top_tb

# Enable power-aware checks
add wave -r /*
add wave -position insertpoint sim:/top_tb/dut/VDDG_CPU
add wave -position insertpoint sim:/top_tb/dut/cpu_iso_en

# Run simulation
run -all

# Report power domain states
report_power_domain_state
```

---

## Physical Implementation

### Floor Planning for Power Domains

```tcl
# ICC2/Innovus floor planning

# Create power domains
create_power_domain PD_CPU \
    -boundary cpu_boundary

# Place power switches
create_pg_ring -domain PD_CPU \
    -nets {VDD VSS}

# Power switch placement
place_power_switch \
    -switches {SW_CPU*} \
    -pattern stripe \
    -spacing 50

# Retention cell placement
set_attribute [get_cells -hier *retention*] \
    physical_status fixed
```

### Power Grid Design

```tcl
# Power mesh for gated domain
create_pg_mesh PG_MESH_CPU \
    -domain PD_CPU \
    -layers {M4 M5} \
    -width 2.0 \
    -spacing 10.0

# Connect power switches
connect_pg_net -net VDDG_CPU \
    -from_pins {SW_CPU*/vout}
```

### IR Drop Analysis

```tcl
# Static IR drop
analyze_power_rail \
    -domain PD_CPU \
    -mode peak

# Report
report_power_rail_ir_drop \
    -threshold 50mV

# Dynamic IR drop
analyze_power_rail \
    -dynamic \
    -switching_activity design.saif
```

---

## Advanced Techniques

### Adaptive Voltage Scaling (AVS) with Power Gating

```systemverilog
module avs_power_gating (
    input  clk,
    input  rst_n,
    input  [1:0] performance_req,  // 00=off, 01=low, 10=med, 11=high
    output logic [1:0] voltage_sel,
    output logic power_en
);
    typedef enum logic [2:0] {
        MODE_OFF,
        MODE_RETENTION,
        MODE_LOW_POWER,
        MODE_NOMINAL,
        MODE_TURBO
    } mode_t;

    mode_t current_mode;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_mode <= MODE_OFF;
            voltage_sel <= 2'b00;
            power_en <= 1'b0;
        end else begin
            case (performance_req)
                2'b00: begin
                    current_mode <= MODE_OFF;
                    voltage_sel <= 2'b00;  // 0V
                    power_en <= 1'b0;
                end

                2'b01: begin
                    current_mode <= MODE_LOW_POWER;
                    voltage_sel <= 2'b01;  // 0.6V
                    power_en <= 1'b1;
                end

                2'b10: begin
                    current_mode <= MODE_NOMINAL;
                    voltage_sel <= 2'b10;  // 0.9V
                    power_en <= 1'b1;
                end

                2'b11: begin
                    current_mode <= MODE_TURBO;
                    voltage_sel <= 2'b11;  // 1.2V
                    power_en <= 1'b1;
                end
            endcase
        end
    end

endmodule
```

### Fine-Grained Power Gating

```systemverilog
module fine_grained_pg #(
    parameter NUM_BLOCKS = 8
)(
    input  clk,
    input  rst_n,
    input  [NUM_BLOCKS-1:0] block_active,
    output logic [NUM_BLOCKS-1:0] block_power_en
);
    // Activity monitor
    logic [NUM_BLOCKS-1:0][7:0] idle_counter;

    genvar i;
    generate
        for (i = 0; i < NUM_BLOCKS; i++) begin : block_pg
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    idle_counter[i] <= 0;
                    block_power_en[i] <= 1'b1;
                end else begin
                    if (block_active[i]) begin
                        idle_counter[i] <= 0;
                        block_power_en[i] <= 1'b1;
                    end else begin
                        if (idle_counter[i] < 255)
                            idle_counter[i] <= idle_counter[i] + 1;

                        // Power gate after 100 idle cycles
                        if (idle_counter[i] > 100)
                            block_power_en[i] <= 1'b0;
                    end
                end
            end
        end
    endgenerate

endmodule
```

---

## Best Practices

### Design Guidelines

1. **Granularity Selection**
   - Too fine: Overhead > savings
   - Too coarse: Miss opportunities
   - Sweet spot: 10-100K gates per domain

2. **Domain Boundaries**
   - Align with functional blocks
   - Minimize cross-domain signals
   - Consider thermal hotspots

3. **Retention Planning**
   - Identify critical state early
   - Use partial retention
   - Estimate retention overhead (5-15%)

4. **Power Switch Sizing**
   ```
   Rule of thumb:
   - W_switch = 100-500µm per mA load
   - Multiple distributed switches
   - Staged power-up for large domains
   ```

5. **Timing Closure**
   - Add timing margin for IR drop
   - Consider retention path delays
   - Account for level shifter delays

### Verification Checklist

- [ ] UPF correctly describes intent
- [ ] All cross-domain paths isolated
- [ ] Retention covers critical state
- [ ] Power-up sequence verified
- [ ] Power-down sequence verified
- [ ] X-propagation checked
- [ ] Power state transitions legal
- [ ] DFT coverage maintained
- [ ] IR drop within spec
- [ ] EM analysis passed

---

## Common Issues and Solutions

### Issue 1: X-Propagation

**Problem**: Unknown values from powered-down domain
**Solution**: Proper isolation cell placement and timing

```systemverilog
// Ensure isolation before power-down
always @(posedge clk) begin
    iso_en <= 1'b1;      // Step 1
    #delay;
    power_en <= 1'b0;    // Step 2
end
```

### Issue 2: Retention Failure

**Problem**: State lost during power transition
**Solution**: Verify save/restore timing

```systemverilog
// Adequate time for save operation
parameter SAVE_CYCLES = 10;
// Check retention cell power supply
```

### Issue 3: Excessive IR Drop

**Problem**: Voltage drop too large during power-up
**Solution**: Staged power-up, more switches

```tcl
# Add more power switches
set_power_switch_size -factor 1.5
# Use staged power-up
```

### Issue 4: Long Wake-up Latency

**Problem**: Too slow to power up
**Solution**:
- Reduce retention depth
- Optimize power controller FSM
- Use faster power switches

---

## Summary

### Power Gating Benefits

- 80-95% leakage reduction
- Complete power elimination when off
- Essential for mobile/IoT

### Implementation Cost

- Area: +5-15%
- Design complexity: High
- Verification effort: 2-3x

### When to Use Power Gating

✅ **Use for:**
- Long idle periods (> 1ms)
- Battery-powered devices
- Thermal management
- Infrequently used blocks

❌ **Avoid for:**
- Always-active circuits
- Fast wake-up requirements (< 1µs)
- Small blocks (< 10K gates)

---

## References

1. **Standards**:
   - IEEE 1801 (UPF)
   - CPF (Common Power Format)

2. **Books**:
   - "Low Power Methodology Manual" - Synopsys
   - "Power Gating for Mobile Devices" - Springer

3. **Tools**:
   - Synopsys Design Compiler
   - Cadence Genus/Innovus
   - Siemens Questa Power Aware

4. **Papers**:
   - "Power Gating for Leakage Control" - IEEE
   - "Fine-Grained Power Gating" - ACM/IEEE

---

**Document Version**: 1.0
**Last Updated**: November 2024
**Author**: Digital Design Documentation Project
