# Low-Power Design - Advanced Guide
### From Fundamentals to Industry Best Practices

---

## Table of Contents
1. [Introduction to Low-Power Design](#1-introduction-to-low-power-design)
2. [Power Fundamentals](#2-power-fundamentals)
3. [Static Power Reduction Techniques](#3-static-power-reduction-techniques)
4. [Dynamic Power Reduction Techniques](#4-dynamic-power-reduction-techniques)
5. [Clock Gating](#5-clock-gating)
6. [Power Gating](#6-power-gating)
7. [Multi-Voltage Design (MVDD)](#7-multi-voltage-design-mvdd)
8. [Dynamic Voltage and Frequency Scaling (DVFS)](#8-dynamic-voltage-and-frequency-scaling-dvfs)
9. [Memory Power Optimization](#9-memory-power-optimization)
10. [Low-Power Coding Techniques](#10-low-power-coding-techniques)
11. [Power-Aware Verification](#11-power-aware-verification)
12. [Unified Power Format (UPF)](#12-unified-power-format-upf)
13. [Industry Examples](#13-industry-examples)
14. [Power Analysis and Estimation](#14-power-analysis-and-estimation)
15. [Summary and Best Practices](#15-summary-and-best-practices)

---

## 1. Introduction to Low-Power Design

### Why Low-Power Design?

**Critical Drivers:**
- **Battery Life**: Mobile devices, IoT sensors, wearables
- **Thermal Management**: Cooling costs, reliability (every 10°C increase halves component life)
- **Energy Costs**: Data centers consume 1-2% of global electricity
- **Environmental Impact**: Reducing carbon footprint
- **Performance**: Less power = less heat = higher performance possible

**Market Impact:**
```
Smartphone Example:
- Active power: 2W (browsing, gaming)
- Standby power: 0.01W (screen off, cellular on)
- 99% of time in standby → standby power dominates battery life!
```

### Power Design Hierarchy

```
System Level
    ↓ Architecture choices, workload optimization

Algorithm Level
    ↓ Algorithm selection, data reuse

RTL Level
    ↓ Clock gating, operand isolation, FSM optimization

Gate Level
    ↓ Cell selection, gate sizing, multi-Vt cells

Physical Level
    ↓ Floorplanning, placement, routing, power grid
```

---

## 2. Power Fundamentals

### 2.1 Total Power Equation

```
P_total = P_dynamic + P_static + P_short_circuit

Where:
P_dynamic       = Switching power (dominant in active mode)
P_static        = Leakage power (dominant in standby)
P_short_circuit = Short-circuit current (typically 5-10% of dynamic)
```

### 2.2 Dynamic Power

**Formula:**
```
P_dynamic = α × C × V² × f

Where:
α = Activity factor (0 to 1, percentage of nodes switching)
C = Load capacitance (wire + gate capacitance)
V = Supply voltage
f = Clock frequency
```

**Example Calculation:**
```
Design Parameters:
- Activity factor (α) = 0.2 (20% of gates switch per cycle)
- Total capacitance (C) = 10pF
- Supply voltage (V) = 1.0V
- Frequency (f) = 100MHz

P_dynamic = 0.2 × 10×10⁻¹² × (1.0)² × 100×10⁶
          = 0.2 × 10 × 10⁻¹² × 1 × 100 × 10⁶
          = 200 μW

Impact of halving voltage:
P_dynamic @ 0.5V = 0.2 × 10×10⁻¹² × (0.5)² × 100×10⁶
                 = 50 μW (4× reduction!)
```

**Key Insight**: Power scales with V² → Voltage reduction is most effective!

### 2.3 Static Power (Leakage)

**Formula:**
```
P_static = I_leakage × V_dd

Where:
I_leakage = Subthreshold + Gate + Junction leakage currents
```

**Leakage Components:**

1. **Subthreshold Leakage** (Dominant in modern technologies)
   ```
   I_sub ∝ e^(V_gs - V_th) / (n × V_T)

   Where:
   V_gs = Gate-source voltage
   V_th = Threshold voltage
   V_T  = Thermal voltage (26mV at 25°C)
   n    = Subthreshold slope factor
   ```

2. **Gate Leakage** (increases exponentially with thinner oxides)
   ```
   I_gate ∝ e^(-T_ox)

   Where:
   T_ox = Gate oxide thickness
   ```

3. **Junction Leakage** (reverse-biased PN junctions)

**Temperature Dependence:**
```
I_leakage doubles every ~10-12°C temperature increase!

Example:
- Leakage @ 25°C = 10mA
- Leakage @ 85°C = ~100mA (10× increase!)
```

### 2.4 Power vs Performance Trade-off

```
         High Performance
              ↑
              │     ┌────┐
              │     │ HP │ (High-performance processors)
              │     └────┘
              │
              │   ┌────┐
Power         │   │ GP │    (General purpose)
              │   └────┘
              │
              │ ┌────┐
              │ │ LP │      (Low-power IoT)
              │ └────┘
              └─────────────────→
                   Low Power
```

---

## 3. Static Power Reduction Techniques

### 3.1 Multi-Threshold Voltage (Multi-Vt) Cells

Use different threshold voltage cells strategically:

**Cell Types:**
```
┌─────────────┬──────────┬──────────┬─────────┐
│ Cell Type   │ V_th     │ Speed    │ Leakage │
├─────────────┼──────────┼──────────┼─────────┤
│ High-Vt     │ High     │ Slow     │ Very Low│
│ Standard-Vt │ Medium   │ Medium   │ Medium  │
│ Low-Vt      │ Low      │ Fast     │ High    │
│ Ultra-Low-Vt│ Very Low │ Very Fast│ Very High│
└─────────────┴──────────┴──────────┴─────────┘
```

**Strategy:**
```verilog
Critical Path (timing-sensitive):
  Use Low-Vt cells
  ┌─────┐    ┌─────┐    ┌─────┐
  │LVT  │───>│LVT  │───>│LVT  │  Fast, high leakage
  └─────┘    └─────┘    └─────┘

Non-Critical Paths:
  Use High-Vt cells
  ┌─────┐    ┌─────┐    ┌─────┐
  │HVT  │───>│HVT  │───>│HVT  │  Slow, low leakage
  └─────┘    └─────┘    └─────┘
```

**Results:**
- Typically 30-50% leakage reduction
- No performance impact (critical paths use LVT)
- Widely used in modern designs

### 3.2 Power Gating (MTCMOS)

Completely shut off power to unused blocks:

```verilog
module power_gated_block (
  input  wire       clk,
  input  wire       rst_n,
  input  wire       sleep_mode,  // Power control
  input  wire [7:0] data_in,
  output reg  [7:0] data_out
);

  // Virtual supply rails
  wire vdd_virtual;

  // Power switch (header switch)
  // In real design, this is a high-Vt PMOS
  assign vdd_virtual = sleep_mode ? 1'b0 : 1'b1;

  // State retention register (powered from always-on rail)
  reg [7:0] retention_reg;

  // Save state before power-down
  always @(posedge clk) begin
    if (sleep_mode)
      retention_reg <= data_out;
  end

  // Normal operation (powered by virtual rail)
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      data_out <= 8'h00;
    else if (!sleep_mode)
      data_out <= data_in + 1;
    else
      data_out <= retention_reg;  // Restore state
  end

endmodule
```

**Power Switch Implementation:**
```
VDD (Always-on)
    │
    │  ┌──────────────┐
    └─>│ Power Switch │ (High-Vt PMOS, low leakage when off)
       │   (PMOS)     │
       └──────┬───────┘
              │
         VDD_virtual (Gated rail)
              │
         ┌────┴─────┐
         │ Logic    │
         │ Block    │
         └────┬─────┘
              │
            VSS/GND
```

**Design Considerations:**
- **Rush Current**: Large inrush when turning on
- **Retention**: State preservation during power-down
- **Isolation**: Prevent floating outputs
- **Wake-up Time**: Typically 100s of cycles

**Example: ARM Cortex-M Processor**
```
Active Mode:    All blocks powered
                Power = 100%

Sleep Mode:     CPU powered off, peripherals on
                Power = 20%

Deep Sleep:     Everything off except RTC, wake-up logic
                Power = 1%

Shutdown:       Everything off
                Power = 0.1%
```

### 3.3 Body Biasing

Dynamically adjust threshold voltage via body terminal:

```
Forward Body Bias (FBB):
  V_body > V_source → Lower V_th → Faster, more leakage
  Use for: High-performance mode

Reverse Body Bias (RBB):
  V_body < V_source → Higher V_th → Slower, less leakage
  Use for: Low-power mode

        VDD
         │
    ┌────┴────┐
    │  PMOS   │
    │ (Body)  │
    └────┬────┘
         │
  ───────┴─────── Body Bias Voltage
```

**Adaptive Body Biasing:**
```verilog
// Pseudo-code for ABB controller
module adaptive_body_bias (
  input  wire temperature,
  input  wire performance_mode,
  output reg  body_bias_voltage
);

  always @(*) begin
    if (performance_mode && temperature < 50)
      body_bias_voltage = FBB_VOLTAGE;  // Fast mode
    else if (!performance_mode || temperature > 80)
      body_bias_voltage = RBB_VOLTAGE;  // Low leakage
    else
      body_bias_voltage = ZERO_BIAS;    // Normal
  end

endmodule
```

---

## 4. Dynamic Power Reduction Techniques

### 4.1 Voltage Scaling

**Most Effective Technique** (P ∝ V²):

```
Example:
V = 1.2V → 0.9V (25% reduction)
Power reduction = (0.9/1.2)² = 56% (44% power savings!)

But: Speed reduces by ~25-30%
```

**Voltage Islands:**
```
┌─────────────────────────────────┐
│ Chip                            │
│  ┌──────────┐   ┌──────────┐   │
│  │  Block A │   │  Block B │   │
│  │  V=1.2V  │   │  V=0.9V  │   │
│  │  High    │   │  Lower   │   │
│  │  Speed   │   │  Power   │   │
│  └────┬─────┘   └─────┬────┘   │
│       │               │         │
│       └───> Level ────┘         │
│           Shifter               │
└─────────────────────────────────┘
```

**Level Shifter Required:**
```verilog
module level_shifter_low_to_high (
  input  wire in_low,   // Low voltage domain (0.9V)
  output wire out_high  // High voltage domain (1.2V)
);
  // Actual implementation uses specialized cells
  // This is simplified representation

  assign out_high = in_low;  // Special cell handles voltage translation

endmodule
```

### 4.2 Frequency Scaling

Reduce clock frequency when high performance not needed:

```verilog
module dynamic_frequency_control (
  input  wire        clk_source,     // High-frequency source
  input  wire [1:0]  workload,       // 00=idle, 01=low, 10=med, 11=high
  output reg         clk_out
);

  reg [3:0] divider;

  always @(*) begin
    case (workload)
      2'b00: divider = 4'd15;  // Divide by 16 (idle)
      2'b01: divider = 4'd7;   // Divide by 8  (low)
      2'b10: divider = 4'd3;   // Divide by 4  (medium)
      2'b11: divider = 4'd0;   // Divide by 1  (high performance)
    endcase
  end

  reg [3:0] counter;

  always @(posedge clk_source) begin
    if (counter >= divider) begin
      counter <= 0;
      clk_out <= ~clk_out;
    end else begin
      counter <= counter + 1;
    end
  end

endmodule
```

### 4.3 Operand Isolation

Prevent unnecessary transitions in unused blocks:

```verilog
module alu_with_isolation (
  input  wire        clk,
  input  wire        enable,
  input  wire [31:0] operand_a,
  input  wire [31:0] operand_b,
  input  wire [2:0]  operation,
  output reg  [31:0] result
);

  // Isolated operands - prevent switching when disabled
  wire [31:0] alu_a = enable ? operand_a : 32'h00000000;
  wire [31:0] alu_b = enable ? operand_b : 32'h00000000;

  always @(posedge clk) begin
    if (enable) begin
      case (operation)
        3'b000: result <= alu_a + alu_b;
        3'b001: result <= alu_a - alu_b;
        3'b010: result <= alu_a & alu_b;
        3'b011: result <= alu_a | alu_b;
        3'b100: result <= alu_a ^ alu_b;
        default: result <= 32'h00000000;
      endcase
    end
  end

endmodule
```

**Power Savings:**
```
Without Isolation:
  Operands switch even when disabled → Wasted power in ALU

With Isolation:
  Operands held at 0 when disabled → 40-60% power reduction
```

### 4.4 Logic Minimization

Reduce switching activity by optimizing logic:

```verilog
// Inefficient - Extra transitions
module inefficient_logic (
  input  wire a, b, c,
  output wire y
);
  wire temp1 = a & b;
  wire temp2 = a & c;
  wire temp3 = temp1 | temp2;  // Extra nodes switching
  assign y = temp3;
endmodule

// Efficient - Minimized logic
module efficient_logic (
  input  wire a, b, c,
  output wire y
);
  assign y = a & (b | c);  // Fewer gates, less switching
endmodule
```

**Boolean Minimization:**
```
Original: Y = A·B + A·C + A·B·C
Minimized: Y = A·(B + C)

Gates: 3 ANDs + 1 OR → 1 AND + 1 OR
Power savings: ~40%
```

---

## 5. Clock Gating

**Most Common Low-Power Technique** - Disable clock to idle registers.

See [Clock_Gating.md](Clock_Gating.md) for detailed coverage.

### 5.1 Integrated Clock Gating (ICG)

```verilog
module integrated_clock_gate (
  input  wire clk,
  input  wire enable,
  input  wire test_enable,  // For DFT
  output wire gated_clk
);

  reg enable_latched;

  // Latch on negative edge to avoid glitches
  always @(*) begin
    if (!clk)
      enable_latched = enable | test_enable;
  end

  // Gate the clock
  assign gated_clk = clk & enable_latched;

endmodule
```

**Glitch-Free Timing:**
```
clk:      ──┐  ┌──┐  ┌──┐  ┌──┐  ┌──
            └──┘  └──┘  └──┘  └──┘

enable:   ─────┐              ┌──────
               └──────────────┘

enable_   ─────┐                    ┌──
latched:       └────────────────────┘
               (Latches when clk=0)

gated_    ──┐  ┌──┐  ┌──┐     ┌──┐
clk:        └──┘  └──┘  └──┘  └──┘
            (No glitches!)
```

### 5.2 Automatic Clock Gating Example

```verilog
module register_file_with_cg (
  input  wire        clk,
  input  wire        rst_n,
  input  wire [3:0]  wr_en,    // Write enable per register
  input  wire [31:0] wr_data,
  output reg  [31:0] reg0, reg1, reg2, reg3
);

  // Generate gated clocks for each register
  wire gclk0, gclk1, gclk2, gclk3;

  integrated_clock_gate cg0 (.clk(clk), .enable(wr_en[0]), .gated_clk(gclk0));
  integrated_clock_gate cg1 (.clk(clk), .enable(wr_en[1]), .gated_clk(gclk1));
  integrated_clock_gate cg2 (.clk(clk), .enable(wr_en[2]), .gated_clk(gclk2));
  integrated_clock_gate cg3 (.clk(clk), .enable(wr_en[3]), .gated_clk(gclk3));

  // Each register uses its gated clock
  always @(posedge gclk0 or negedge rst_n) begin
    if (!rst_n) reg0 <= 32'h0;
    else        reg0 <= wr_data;
  end

  always @(posedge gclk1 or negedge rst_n) begin
    if (!rst_n) reg1 <= 32'h0;
    else        reg1 <= wr_data;
  end

  always @(posedge gclk2 or negedge rst_n) begin
    if (!rst_n) reg2 <= 32'h0;
    else        reg2 <= wr_data;
  end

  always @(posedge gclk3 or negedge rst_n) begin
    if (!rst_n) reg3 <= 32'h0;
    else        reg3 <= wr_data;
  end

endmodule
```

**Power Savings:** 20-60% dynamic power reduction typical

---

## 6. Power Gating

See [Power_Gating.md](Power_Gating.md) for comprehensive coverage.

### 6.1 State Retention

Critical for maintaining state during power-down:

```verilog
module retention_register (
  input  wire       clk,
  input  wire       rst_n,
  input  wire       save,      // Save state before power-down
  input  wire       restore,   // Restore after power-up
  input  wire [7:0] data_in,
  output reg  [7:0] data_out
);

  // Retention flop (balloon latch) - powered from always-on domain
  reg [7:0] retention_data;

  // Save to retention storage
  always @(posedge clk) begin
    if (save)
      retention_data <= data_out;
  end

  // Normal operation
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      data_out <= 8'h00;
    else if (restore)
      data_out <= retention_data;  // Restore from retention
    else
      data_out <= data_in;
  end

endmodule
```

### 6.2 Isolation Cells

Prevent unknown values from propagating:

```verilog
module isolation_cell (
  input  wire data_in,
  input  wire iso_enable,  // 1 = isolate
  input  wire iso_value,   // Value to drive when isolated (0 or 1)
  output wire data_out
);

  assign data_out = iso_enable ? iso_value : data_in;

endmodule
```

**Placement:**
```
  Powered Domain          Unpowered Domain
┌─────────────────┐    ┌─────────────────┐
│                 │    │                 │
│   Logic Block   │───>│  Isolation  │───>  Always-On
│   (Can be off)  │    │    Cell     │      Domain
│                 │    │ (Always on) │
└─────────────────┘    └─────────────────┘
```

---

## 7. Multi-Voltage Design (MVDD)

### 7.1 Voltage Domain Architecture

```verilog
// Top-level with multiple voltage domains
module multi_voltage_soc (
  input  wire        clk,
  input  wire        rst_n,

  // Interface between domains
  input  wire [7:0]  data_from_1v2,
  output wire [7:0]  data_to_0v9
);

  // 1.2V domain - High performance CPU
  wire [31:0] cpu_data;
  high_performance_cpu #(.VOLTAGE(1.2)) cpu (
    .clk(clk),
    .data_out(cpu_data)
  );

  // Level shifter 1.2V → 0.9V
  wire [31:0] cpu_data_shifted;
  level_shifter_1v2_to_0v9 ls1 (
    .in(cpu_data),
    .out(cpu_data_shifted)
  );

  // 0.9V domain - Low power peripherals
  low_power_peripheral #(.VOLTAGE(0.9)) peripheral (
    .clk(clk),
    .data_in(cpu_data_shifted)
  );

endmodule
```

### 7.2 Level Shifter Types

**Low-to-High Level Shifter:**
```
 VDDL (0.9V)          VDDH (1.2V)
     │                    │
     │                ┌───┴───┐
  ┌──┴──┐             │ PMOS  │
  │ Input│             │ Cross-│
  │Logic │────────────>│coupled│────> Output (1.2V)
  └─────┘             │ Latch │
                      └───────┘
                          │
                         VSS
```

**High-to-Low Level Shifter:**
```
Simpler - can use resistive divider or pass-gate
```

---

## 8. Dynamic Voltage and Frequency Scaling (DVFS)

### 8.1 DVFS Controller

```verilog
module dvfs_controller (
  input  wire        clk,
  input  wire        rst_n,
  input  wire [7:0]  cpu_utilization,  // 0-100%
  input  wire [7:0]  temperature,      // Celsius
  output reg  [1:0]  voltage_select,   // Voltage level
  output reg  [1:0]  frequency_select  // Frequency level
);

  // Operating Points (OPP)
  localparam OPP0 = 2'b00;  // 0.8V, 400MHz  (Low power)
  localparam OPP1 = 2'b01;  // 0.9V, 800MHz  (Normal)
  localparam OPP2 = 2'b10;  // 1.0V, 1.2GHz  (High)
  localparam OPP3 = 2'b11;  // 1.1V, 1.6GHz  (Turbo)

  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      voltage_select <= OPP1;
      frequency_select <= OPP1;
    end else begin
      // Thermal throttling
      if (temperature > 85) begin
        voltage_select <= OPP0;
        frequency_select <= OPP0;
      end
      // Performance scaling based on utilization
      else if (cpu_utilization > 90) begin
        voltage_select <= OPP3;    // Turbo mode
        frequency_select <= OPP3;
      end
      else if (cpu_utilization > 60) begin
        voltage_select <= OPP2;    // High performance
        frequency_select <= OPP2;
      end
      else if (cpu_utilization > 30) begin
        voltage_select <= OPP1;    // Normal
        frequency_select <= OPP1;
      end
      else begin
        voltage_select <= OPP0;    // Low power
        frequency_select <= OPP0;
      end
    end
  end

endmodule
```

**Operating Point Table:**
```
┌─────┬─────────┬───────────┬──────────┬────────────┐
│ OPP │ Voltage │ Frequency │ Power    │ Use Case   │
├─────┼─────────┼───────────┼──────────┼────────────┤
│ 0   │ 0.8V    │ 400 MHz   │ 100 mW   │ Idle/Light │
│ 1   │ 0.9V    │ 800 MHz   │ 250 mW   │ Normal     │
│ 2   │ 1.0V    │ 1.2 GHz   │ 500 mW   │ Heavy      │
│ 3   │ 1.1V    │ 1.6 GHz   │ 900 mW   │ Turbo      │
└─────┴─────────┴───────────┴──────────┴────────────┘
```

### 8.2 Voltage Regulator Interface

```verilog
module voltage_regulator_controller (
  input  wire       clk,
  input  wire       rst_n,
  input  wire [1:0] voltage_select,
  output reg        vdd_ready,

  // I2C/SPI to external regulator
  output reg        reg_sda,
  input  wire       reg_scl
);

  // Voltage transition state machine
  typedef enum reg [2:0] {
    IDLE,
    REQUEST_CHANGE,
    WAIT_STABLE,
    READY
  } state_t;

  state_t state;
  reg [15:0] stability_timer;

  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state <= IDLE;
      vdd_ready <= 1'b0;
    end else begin
      case (state)
        IDLE: begin
          if (voltage_select != current_voltage) begin
            state <= REQUEST_CHANGE;
            vdd_ready <= 1'b0;
          end
        end

        REQUEST_CHANGE: begin
          // Send command to regulator via I2C/SPI
          // ... I2C transaction ...
          state <= WAIT_STABLE;
          stability_timer <= 16'd1000;  // Wait cycles
        end

        WAIT_STABLE: begin
          if (stability_timer == 0) begin
            state <= READY;
          end else begin
            stability_timer <= stability_timer - 1;
          end
        end

        READY: begin
          vdd_ready <= 1'b1;
          state <= IDLE;
        end
      endcase
    end
  end

endmodule
```

---

## 9. Memory Power Optimization

### 9.1 Memory Partitioning

```verilog
module partitioned_memory (
  input  wire        clk,
  input  wire [3:0]  bank_enable,  // Enable per bank
  input  wire [11:0] address,      // 12-bit address
  input  wire        wr_en,
  input  wire [31:0] wr_data,
  output wire [31:0] rd_data
);

  // 4KB memory split into 4x 1KB banks
  wire [1:0]  bank_sel = address[11:10];
  wire [9:0]  bank_addr = address[9:0];

  wire [31:0] bank_out[0:3];

  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : mem_banks
      memory_bank_1kb bank (
        .clk(clk),
        .enable(bank_enable[i] && (bank_sel == i)),  // Only active bank powered
        .addr(bank_addr),
        .wr_en(wr_en),
        .wr_data(wr_data),
        .rd_data(bank_out[i])
      );
    end
  endgenerate

  // Output mux
  assign rd_data = bank_out[bank_sel];

endmodule
```

**Power Savings:**
- Only 1 of 4 banks active at a time
- 75% of memory in low-power state
- Typical savings: 60-70%

### 9.2 Memory Drowsy Mode

```verilog
module drowsy_memory (
  input  wire        clk,
  input  wire        drowsy_mode,  // Reduce voltage when inactive
  input  wire [9:0]  addr,
  input  wire        wr_en,
  input  wire [31:0] wr_data,
  output reg  [31:0] rd_data
);

  // Memory array with voltage control
  (* ram_style = "block" *) reg [31:0] mem [0:1023];

  // Simulated voltage control (in real design, controls bitcell supply)
  wire vdd_mem = drowsy_mode ? 1'b0 : 1'b1;  // Simplified

  always @(posedge clk) begin
    if (!drowsy_mode) begin
      if (wr_en)
        mem[addr] <= wr_data;
      rd_data <= mem[addr];
    end
  end

endmodule
```

**Drowsy Mode Benefits:**
- Data retained (unlike power gating)
- 50-70% leakage reduction
- Fast wake-up (1-2 cycles)

---

## 10. Low-Power Coding Techniques

### 10.1 One-Hot vs Binary Encoding

**Binary Encoding** (Lower area):
```verilog
// 8 states in 3 bits
typedef enum reg [2:0] {
  IDLE   = 3'b000,
  STATE1 = 3'b001,
  STATE2 = 3'b010,
  STATE3 = 3'b011,
  STATE4 = 3'b100
} state_binary_t;

// Pros: Fewer flip-flops
// Cons: More complex decode logic, higher switching
```

**One-Hot Encoding** (Lower power):
```verilog
// 8 states in 8 bits (one bit per state)
typedef enum reg [7:0] {
  IDLE   = 8'b00000001,
  STATE1 = 8'b00000010,
  STATE2 = 8'b00000100,
  STATE3 = 8'b00001000,
  STATE4 = 8'b00010000
} state_onehot_t;

// Pros: Simpler decode, lower switching activity
// Cons: More flip-flops
```

**Power Comparison:**
```
8-state FSM:
Binary:   3 FFs, complex logic    → 100% power
One-hot:  8 FFs, simple logic     → 70% power (30% savings)
Gray:     3 FFs, medium logic     → 85% power
```

### 10.2 Gray Code Counters

```verilog
module gray_counter #(parameter WIDTH = 4) (
  input  wire             clk,
  input  wire             rst_n,
  output reg [WIDTH-1:0]  count_gray
);

  reg [WIDTH-1:0] count_binary;

  // Binary counter
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      count_binary <= 0;
    else
      count_binary <= count_binary + 1;
  end

  // Convert to Gray code (only 1 bit changes per increment)
  always @(*) begin
    count_gray = count_binary ^ (count_binary >> 1);
  end

endmodule
```

**Switching Activity:**
```
Binary Count:  0000→0001→0010→0011→0100→0101→0110→0111
Transitions:      1    2    1    3    1    2    1  (11 total)

Gray Count:    0000→0001→0011→0010→0110→0111→0101→0100
Transitions:      1    1    1    1    1    1    1  (7 total)

Power savings: ~36%
```

### 10.3 Resource Sharing

```verilog
// Without sharing - High power
module no_sharing (
  input  wire [15:0] a, b, c, d,
  input  wire        sel,
  output wire [15:0] result
);

  wire [15:0] mult1 = a * b;  // Multiplier 1
  wire [15:0] mult2 = c * d;  // Multiplier 2

  assign result = sel ? mult1 : mult2;

  // Problem: Both multipliers active even though only one used!

endmodule

// With sharing - Low power
module with_sharing (
  input  wire [15:0] a, b, c, d,
  input  wire        sel,
  output wire [15:0] result
);

  wire [15:0] op1 = sel ? a : c;
  wire [15:0] op2 = sel ? b : d;
  wire [15:0] mult = op1 * op2;  // Single shared multiplier

  assign result = mult;

  // Power savings: 50% (one multiplier instead of two)

endmodule
```

### 10.4 Glitch Reduction

```verilog
// Glitchy design
module glitchy (
  input  wire [7:0] a, b,
  output wire [7:0] sum
);

  // Combinational path - can have glitches
  assign sum = a + b;

endmodule

// Glitch-free with pipelining
module glitch_free (
  input  wire       clk,
  input  wire [7:0] a, b,
  output reg  [7:0] sum
);

  // Register output - glitches filtered by flop
  always @(posedge clk) begin
    sum <= a + b;
  end

endmodule
```

**Glitch Waveform:**
```
Combinational:
a:      ────┐           ┌────
            └───────────┘

b:      ──────┐     ┌────────
              └─────┘

sum:    ────┐ ┌─┐ ┌─┐     ┌──
            └─┘ └─┘ └─────┘
            (Glitches waste power!)

Registered:
sum:    ────┐               ┌──
            └───────────────┘
            (Clean transition)
```

---

## 11. Power-Aware Verification

### 11.1 Power Intent Verification

```systemverilog
// Testbench with power checking
module tb_power_aware;

  reg       clk;
  reg       rst_n;
  reg [1:0] power_mode;  // 00=active, 01=sleep, 10=deep_sleep
  wire      power_error;

  design_under_test dut (
    .clk(clk),
    .rst_n(rst_n),
    .power_mode(power_mode)
  );

  // Power state checker
  power_checker checker (
    .clk(clk),
    .power_mode(power_mode),
    .error(power_error)
  );

  // Assertions for power states
  property p_no_activity_in_sleep;
    @(posedge clk) (power_mode == 2'b01) |-> (dut.internal_activity == 0);
  endproperty

  assert property (p_no_activity_in_sleep)
    else $error("Activity detected during sleep mode!");

  // Check isolation
  property p_isolation_active;
    @(posedge clk) (power_mode == 2'b10) |-> (dut.iso_enable == 1);
  endproperty

  assert property (p_isolation_active)
    else $error("Isolation not active in deep sleep!");

endmodule
```

### 11.2 Power Estimation in Simulation

```systemverilog
module power_monitor;

  integer toggle_count;
  real    switching_power;

  // Monitor signal toggles
  always @(dut.clk or dut.data_bus) begin
    toggle_count = toggle_count + 1;
  end

  // Calculate estimated power
  initial begin
    #10000;  // Sample period
    switching_power = toggle_count * CAPACITANCE * VDD * VDD * FREQ;
    $display("Estimated Dynamic Power: %f mW", switching_power * 1000);
  end

endmodule
```

---

## 12. Unified Power Format (UPF)

Industry-standard for specifying power intent.

### 12.1 Basic UPF Structure

```tcl
# Create power domains
create_power_domain PD_TOP -include_scope
create_power_domain PD_CPU -elements {cpu_inst}
create_power_domain PD_PERIPH -elements {periph_inst}

# Create supply nets
create_supply_net VDD_1V2 -domain PD_CPU
create_supply_net VDD_0V9 -domain PD_PERIPH
create_supply_net VSS -domain PD_TOP

# Create supply ports
create_supply_port VDD_1V2
create_supply_port VDD_0V9
create_supply_port VSS

# Connect supplies
connect_supply_net VDD_1V2 -ports {VDD_1V2}
connect_supply_net VDD_0V9 -ports {VDD_0V9}
connect_supply_net VSS -ports {VSS}

# Set supply sets
create_supply_set SS_CPU \
  -function {power VDD_1V2} \
  -function {ground VSS}

create_supply_set SS_PERIPH \
  -function {power VDD_0V9} \
  -function {ground VSS}

# Associate with domains
associate_supply_set SS_CPU -handle PD_CPU
associate_supply_set SS_PERIPH -handle PD_PERIPH

# Power states
add_power_state PD_CPU \
  -state {ACTIVE -supply_expr {power == FULL_ON}} \
  -state {SLEEP  -supply_expr {power == OFF}}

# Level shifters
set_level_shifter LS_CPU_TO_PERIPH \
  -domain PD_CPU \
  -source {VDD_1V2} \
  -sink {VDD_0V9} \
  -location automatic

# Isolation strategy
set_isolation ISO_CPU \
  -domain PD_CPU \
  -isolation_power_net VDD_0V9 \
  -isolation_ground_net VSS \
  -clamp_value 0 \
  -applies_to outputs

# Retention strategy
set_retention RET_CPU \
  -domain PD_CPU \
  -retention_power_net VDD_1V2 \
  -retention_ground_net VSS \
  -save_signal {save_state high} \
  -restore_signal {restore_state high}

# Power switches
set_switch_cell SWITCH_CPU \
  -domain PD_CPU \
  -lib_cells {HEADER_SWITCH}
```

### 12.2 Power States Definition

```tcl
# Define operating modes
create_pst CPU_PST -supplies {VDD_CPU VDD_PERIPH}

add_pst_state ACTIVE \
  -pst CPU_PST \
  -state {VDD_CPU 1.2 VDD_PERIPH 0.9}

add_pst_state STANDBY \
  -pst CPU_PST \
  -state {VDD_CPU 0.8 VDD_PERIPH 0.9}

add_pst_state SLEEP \
  -pst CPU_PST \
  -state {VDD_CPU OFF VDD_PERIPH 0.9}

add_pst_state DEEP_SLEEP \
  -pst CPU_PST \
  -state {VDD_CPU OFF VDD_PERIPH OFF}
```

---

## 13. Industry Examples

### 13.1 Smartphone Application Processor

**Power Domains:**
```
┌─────────────────────────────────────────┐
│ Application Processor                   │
│                                         │
│  ┌────────────┐    ┌─────────────┐    │
│  │ CPU Cores  │    │ GPU         │    │
│  │ 1.2V       │    │ 1.0V        │    │
│  │ DVFS       │    │ Power Gated │    │
│  └────────────┘    └─────────────┘    │
│                                         │
│  ┌────────────┐    ┌─────────────┐    │
│  │ Memory     │    │ Peripherals │    │
│  │ 1.8V       │    │ 0.9V        │    │
│  │ Retention  │    │ Always-On   │    │
│  └────────────┘    └─────────────┘    │
└─────────────────────────────────────────┘
```

**Power States:**
```
Active:     All domains on         → 2000 mW
Screen Off: CPU/GPU sleep          → 100 mW
Standby:    Only modem, RTC active → 10 mW
Airplane:   All radios off         → 1 mW
```

### 13.2 IoT Sensor Node

```verilog
module iot_sensor_node (
  input  wire       clk_32khz,     // Low-power clock
  input  wire       sensor_trigger,
  output reg        radio_tx
);

  // State machine
  typedef enum reg [1:0] {
    DEEP_SLEEP,    // 10 μW
    SENSE,         // 100 μW
    PROCESS,       // 500 μW
    TRANSMIT       // 50 mW
  } power_state_t;

  power_state_t state;
  reg [15:0] sensor_data;

  always @(posedge clk_32khz) begin
    case (state)
      DEEP_SLEEP: begin
        // Everything off except wake-up timer
        if (sensor_trigger)
          state <= SENSE;
      end

      SENSE: begin
        // Power on sensor, ADC
        sensor_data <= read_sensor();
        state <= PROCESS;
      end

      PROCESS: begin
        // Wake up CPU, process data
        if (data_ready())
          state <= TRANSMIT;
      end

      TRANSMIT: begin
        // Power on radio, transmit
        radio_tx <= 1'b1;
        // After transmission
        state <= DEEP_SLEEP;
      end
    endcase
  end

endmodule
```

**Duty Cycle:**
```
24 hours:
- Deep Sleep: 23h 59m 50s (99.99%)
- Active:     10s          (0.01%)

Average Power = 10μW × 0.9999 + 50mW × 0.0001 = 15 μW
Battery Life (CR2032, 220mAh @ 3V):
  220mAh / 5μA = 44,000 hours = 5 years!
```

### 13.3 Data Center Server CPU

**Power Management Features:**
- **Turbo Boost**: Temporarily increase frequency when thermal headroom available
- **Core Parking**: Turn off unused cores
- **Memory Throttling**: Reduce DRAM refresh rate when idle
- **Package C-States**: Progressive power-down levels

```
C0 (Active):       All cores active              → 150W
C1 (Halt):         Cores halted, caches on       → 80W
C3 (Sleep):        Caches flushed, L2 off       → 30W
C6 (Deep Sleep):   Cores powered off            → 5W
Package C6:        Entire package off           → 1W
```

---

## 14. Power Analysis and Estimation

### 14.1 Power Calculation Methods

**1. Activity-Based (Early RTL):**
```
P = Σ (toggle_rate × capacitance × V² × f)
```

**2. Statistical (Post-Synthesis):**
```
- Use gate-level netlist
- Apply statistical activity
- More accurate than RTL
```

**3. Vector-Based (Post-Layout):**
```
- Actual testbench vectors
- Includes extracted parasitics
- Most accurate
```

### 14.2 Power Analysis Flow

```
RTL Design
    ↓
    ├─→ [RTL Power Estimation]
    │     - Quick feedback
    │     - ±50% accuracy
    ↓
Synthesis
    ↓
    ├─→ [Gate-Level Power Analysis]
    │     - Netlist-based
    │     - ±20% accuracy
    ↓
Place & Route
    ↓
    └─→ [Signoff Power Analysis]
          - Includes parasitics
          - ±5% accuracy
```

### 14.3 Power Profiling

```systemverilog
module power_profiler;

  // Track power per module
  real cpu_power;
  real memory_power;
  real peripheral_power;

  initial begin
    forever begin
      #1000;  // Sample every 1000ns

      cpu_power = measure_power(dut.cpu);
      memory_power = measure_power(dut.memory);
      peripheral_power = measure_power(dut.periph);

      $display("Power Profile @ %t", $time);
      $display("  CPU:        %f mW", cpu_power);
      $display("  Memory:     %f mW", memory_power);
      $display("  Peripheral: %f mW", peripheral_power);
      $display("  Total:      %f mW", cpu_power + memory_power + peripheral_power);
    end
  end

endmodule
```

---

## 15. Summary and Best Practices

### 15.1 Power Reduction Hierarchy

```
Impact vs Effort:

HIGH IMPACT, LOW EFFORT:
✓ Clock gating (20-60% dynamic power reduction)
✓ Operand isolation
✓ Multi-Vt cell selection

MEDIUM IMPACT, MEDIUM EFFORT:
✓ Voltage scaling
✓ Frequency scaling
✓ Memory partitioning

HIGH IMPACT, HIGH EFFORT:
✓ Power gating (90% static power in gated blocks)
✓ DVFS
✓ Multi-voltage domains
```

### 15.2 Design Checklist

**Architecture Level:**
- [ ] Identify power-critical blocks
- [ ] Define power states (active, sleep, off)
- [ ] Plan voltage domains
- [ ] Define operating points (DVFS)

**RTL Level:**
- [ ] Use clock gating liberally
- [ ] Add operand isolation
- [ ] Optimize FSM encoding
- [ ] Minimize unnecessary transitions
- [ ] Use resource sharing

**Verification:**
- [ ] Create UPF file
- [ ] Verify power state transitions
- [ ] Check isolation/retention
- [ ] Validate level shifters
- [ ] Measure power in simulation

**Implementation:**
- [ ] Use multi-Vt cells
- [ ] Insert power switches
- [ ] Add retention registers
- [ ] Place isolation cells
- [ ] Optimize power grid

### 15.3 Common Mistakes

**❌ DON'T:**
1. Add clock gating at end of project (integrate early)
2. Forget temperature effects on leakage
3. Ignore power state transitions (can be expensive)
4. Over-design (not everything needs lowest power)
5. Skip power verification (leads to tape-out failures)

**✓ DO:**
1. Start power planning in architecture phase
2. Use UPF from RTL onwards
3. Measure power regularly
4. Balance power/performance/area
5. Learn from silicon measurements

### 15.4 Industry Tools

**RTL Power Estimation:**
- Synopsys: Power Compiler
- Cadence: Joules RTL Power Solution

**Gate-Level Power Analysis:**
- Synopsys: PrimeTime PX
- Cadence: Voltus

**Power-Aware Verification:**
- Synopsys: VC LP (Low Power)
- Cadence: Xcelium with LP option

**UPF Editing:**
- Typically integrated in synthesis/P&R tools

### 15.5 Key Takeaways

1. **Power scales with V²** → Voltage reduction most effective
2. **Clock gating is essential** → 20-60% power savings with minimal effort
3. **Leakage increases exponentially with temperature** → Thermal management critical
4. **Power gating saves static power** → But adds complexity (retention, isolation)
5. **DVFS provides best power/performance** → But requires careful implementation
6. **UPF is mandatory** → Industry standard for power intent
7. **Measure early and often** → Power bugs are expensive to fix late

---

## Conclusion

Low-power design is no longer optional—it's a fundamental requirement in modern digital design. From mobile devices to data centers, power efficiency directly impacts product success.

**Progressive Learning Path:**
1. **Beginner**: Clock gating, basic power concepts
2. **Intermediate**: Power gating, multi-Vt, UPF basics
3. **Advanced**: DVFS, multi-voltage, advanced verification

**Next Steps:**
- Practice with real designs
- Study existing low-power IPs
- Learn UPF syntax hands-on
- Measure and optimize iteratively

The techniques in this guide are used in every modern chip, from smartphones to servers. Master them to become an indispensable hardware engineer!

---

*For related topics, see:*
- [Clock_Gating.md](Clock_Gating.md) - Detailed clock gating techniques
- [Power_Gating.md](Power_Gating.md) - Comprehensive power gating guide
- [ASIC_Design_Flow_Guide.md](ASIC_Design_Flow_Guide.md) - Complete design flow

---
