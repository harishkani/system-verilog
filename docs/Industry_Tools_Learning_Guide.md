# Industry EDA Tools Learning Guide (4-6 Weeks)

## Table of Contents

1. [Introduction](#introduction)
2. [Prerequisites](#prerequisites)
3. [Tool Overview](#tool-overview)
4. [Week 1-2: VCS (Verilog Compiler Simulator)](#week-1-2-vcs-verilog-compiler-simulator)
5. [Week 2-3: Verdi Debug Platform](#week-2-3-verdi-debug-platform)
6. [Week 3-4: Questa Advanced Simulator](#week-3-4-questa-advanced-simulator)
7. [Week 5-6: Formal Verification Tools](#week-5-6-formal-verification-tools)
8. [Integrated Workflow](#integrated-workflow)
9. [Best Practices](#best-practices)
10. [Additional Resources](#additional-resources)

---

## Introduction

This guide provides a comprehensive 4-6 week curriculum for learning industry-standard EDA (Electronic Design Automation) tools used in semiconductor verification and design. These tools are essential for professional ASIC/FPGA design and verification engineers.

### Learning Objectives

By the end of this guide, you will be able to:
- Set up and run simulations using VCS and Questa
- Debug complex designs using Verdi's advanced features
- Perform formal verification using industry-standard tools
- Integrate multiple tools in a professional verification flow
- Apply best practices for efficient debugging and verification

### Time Commitment

- **Minimum**: 4 weeks (20-25 hours/week)
- **Recommended**: 6 weeks (15-20 hours/week)
- **Practice Time**: Additional 10-15 hours for hands-on projects

---

## Prerequisites

### Required Knowledge
- Strong understanding of SystemVerilog/Verilog
- Familiarity with digital design concepts
- Basic Linux/Unix command-line skills
- Understanding of testbench concepts

### System Requirements
- Linux environment (RHEL, CentOS, or Ubuntu)
- Minimum 16GB RAM (32GB recommended)
- 50GB free disk space
- Valid tool licenses

### Software Access
- Synopsys VCS (version 2020.03 or later)
- Synopsys Verdi (version 2020.03 or later)
- Mentor Questa/ModelSim (version 2020.1 or later)
- Formal tools (JasperGold, VC Formal, or Questa Formal)

---

## Tool Overview

### VCS (Verilog Compiler Simulator) - Synopsys
**Primary Use**: High-performance simulation of RTL and gate-level designs

**Key Features**:
- 3-step compile-elaborate-simulate flow
- Multi-core simulation support
- Code coverage and functional coverage
- Native SystemVerilog and UVM support
- DVE (Discovery Visualization Environment) GUI

**Industry Adoption**: ~40% market share in ASIC verification

---

### Verdi - Synopsys
**Primary Use**: Advanced debug and analysis platform

**Key Features**:
- Unified debug environment
- Advanced waveform viewing (nWave)
- Source code and schematic browsing
- Transaction-level debug
- Automated debug methodologies
- Power-aware debugging

**Industry Adoption**: Industry-leading debug platform

---

### Questa - Siemens (Mentor Graphics)
**Primary Use**: Advanced verification simulation and debug

**Key Features**:
- Integrated simulator and debugger
- Advanced code and functional coverage
- SystemVerilog Assertions (SVA) support
- Formal verification integration
- Mixed-language simulation (VHDL/Verilog/SystemVerilog)
- Advanced debugging with Visualizer

**Industry Adoption**: ~35% market share in ASIC verification

---

### Formal Verification Tools
**Primary Use**: Mathematical proof of design correctness

**Common Tools**:
- **JasperGold** (Cadence)
- **VC Formal** (Synopsys)
- **Questa Formal** (Siemens)

**Key Features**:
- Property verification
- Equivalence checking
- Connectivity checking
- X-propagation analysis

---

## Week 1-2: VCS (Verilog Compiler Simulator)

### Week 1: VCS Fundamentals

#### Day 1-2: Installation and Setup

**Learning Goals**:
- Understand VCS directory structure
- Set up environment variables
- Verify installation

**Key Environment Variables**:
```bash
# Add to ~/.bashrc or ~/.cshrc
export VCS_HOME=/path/to/vcs/installation
export PATH=$VCS_HOME/bin:$PATH
export LD_LIBRARY_PATH=$VCS_HOME/lib:$LD_LIBRARY_PATH

# License setup
export SNPSLMD_LICENSE_FILE=port@license_server
# or
export LM_LICENSE_FILE=port@license_server
```

**Verification**:
```bash
# Check VCS version
vcs -ID

# Check license
vcs -check_license
```

---

#### Day 3-4: Basic Compilation and Simulation

**The VCS 3-Step Flow**:

1. **Compile** (`vlogan`): Analyze SystemVerilog files
2. **Elaborate** (`vcs`): Build simulation model
3. **Simulate** (`simv`): Run simulation

**Example 1: Simple Counter**

`counter.sv`:
```systemverilog
module counter #(
    parameter WIDTH = 8
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             en,
    output logic [WIDTH-1:0] count
);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= '0;
        else if (en)
            count <= count + 1'b1;
    end

endmodule
```

`counter_tb.sv`:
```systemverilog
module counter_tb;
    logic       clk;
    logic       rst_n;
    logic       en;
    logic [7:0] count;

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // DUT instantiation
    counter #(.WIDTH(8)) dut (
        .clk(clk),
        .rst_n(rst_n),
        .en(en),
        .count(count)
    );

    // Test sequence
    initial begin
        rst_n = 0;
        en = 0;
        #20 rst_n = 1;
        #10 en = 1;
        #100;
        en = 0;
        #50;
        $finish;
    end

    // Waveform dumping
    initial begin
        $fsdbDumpfile("counter.fsdb");
        $fsdbDumpvars(0, counter_tb);
    end

endmodule
```

**Compilation and Simulation**:
```bash
# Method 1: Single command
vcs -sverilog counter.sv counter_tb.sv -debug_access+all
./simv

# Method 2: Separate compilation (recommended for large designs)
vlogan -sverilog counter.sv counter_tb.sv
vcs counter_tb -debug_access+all
./simv
```

**Important VCS Options**:
```bash
# Debug options
-debug_access+all        # Full debug capability
-debug_access+r          # Read-only access (faster)
-kdb                     # Generate KDB for Verdi

# Coverage options
-cm line+cond+fsm+tgl+branch  # Enable code coverage
-cm_dir coverage_db           # Coverage database location

# Performance options
-j8                      # Parallel compilation (8 cores)
-ntb_opts uvm            # UVM support

# Waveform dumping
-ucli -do dump.tcl       # Execute TCL script for dumping
```

---

#### Day 5-7: Advanced VCS Features

**Example 2: UVM Testbench Compilation**

`uvm_test.sv`:
```systemverilog
`include "uvm_macros.svh"
import uvm_pkg::*;

class my_test extends uvm_test;
    `uvm_component_utils(my_test)

    function new(string name = "my_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info(get_type_name(), "Build phase", UVM_LOW)
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Running test", UVM_LOW)
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial begin
        run_test("my_test");
    end
endmodule
```

**UVM Compilation**:
```bash
vcs -sverilog \
    -ntb_opts uvm-1.2 \
    +incdir+$VCS_HOME/etc/uvm-1.2/src \
    -debug_access+all \
    -kdb \
    uvm_test.sv

./simv +UVM_TESTNAME=my_test +UVM_VERBOSITY=UVM_LOW
```

---

**Code Coverage Flow**:

`run_coverage.sh`:
```bash
#!/bin/bash

# Compile with coverage
vcs -sverilog counter.sv counter_tb.sv \
    -cm line+cond+fsm+tgl+branch \
    -cm_dir coverage.vdb \
    -debug_access+all

# Run simulation
./simv -cm line+cond+fsm+tgl+branch

# Generate coverage report
urg -dir coverage.vdb -report coverage_report
```

**Viewing Coverage Reports**:
```bash
# HTML report
firefox coverage_report/index.html

# GUI coverage viewer
verdi -cov -covdir coverage.vdb
```

---

**Makefile for VCS Projects**:

`Makefile`:
```makefile
# Makefile for VCS simulation

# Tool paths
VCS = vcs
SIMV = ./simv
URG = urg

# Source files
RTL_FILES = counter.sv
TB_FILES = counter_tb.sv

# Compilation options
VCS_OPTS = -sverilog -debug_access+all -kdb
COV_OPTS = -cm line+cond+fsm+tgl+branch -cm_dir coverage.vdb

# Targets
.PHONY: all compile sim clean cov

all: compile

compile:
	$(VCS) $(VCS_OPTS) $(RTL_FILES) $(TB_FILES)

sim: compile
	$(SIMV)

cov_compile:
	$(VCS) $(VCS_OPTS) $(COV_OPTS) $(RTL_FILES) $(TB_FILES)

cov_sim: cov_compile
	$(SIMV) $(COV_OPTS)

cov_report: cov_sim
	$(URG) -dir coverage.vdb -report coverage_report

clean:
	rm -rf simv* csrc *.log *.vpd DVEfiles coverage.vdb coverage_report
	rm -rf *.fsdb verdiLog novas* *.conf
```

---

### Week 2: Advanced VCS Techniques

#### Multi-File Projects and Fileists

**Using Filelists** (`filelist.f`):
```bash
# RTL files
./rtl/alu.sv
./rtl/register_file.sv
./rtl/control_unit.sv
./rtl/cpu_top.sv

# Include directories
+incdir+./rtl/include
+incdir+./tb/include

# Testbench files
./tb/cpu_tb.sv

# Defines
+define+SIMULATION
+define+DEBUG_MODE

# Library files
-v $VCS_HOME/lib/stdcells.v
```

**Compilation with Filelist**:
```bash
vcs -f filelist.f -debug_access+all -kdb
```

---

#### Direct Programming Interface (DPI)

**C Function in SystemVerilog**:

`dpi_example.c`:
```c
#include <stdio.h>
#include "svdpi.h"

// Export C function to SystemVerilog
void c_display(const char* msg) {
    printf("C Function: %s\n", msg);
}

int c_add(int a, int b) {
    return a + b;
}
```

`dpi_test.sv`:
```systemverilog
module dpi_test;
    // Import C functions
    import "DPI-C" function void c_display(string msg);
    import "DPI-C" function int c_add(int a, int b);

    initial begin
        int result;

        c_display("Hello from SystemVerilog!");

        result = c_add(10, 20);
        $display("10 + 20 = %0d", result);

        $finish;
    end
endmodule
```

**Compilation with DPI**:
```bash
# Compile C code
gcc -c -fPIC dpi_example.c -I$VCS_HOME/include

# Compile SystemVerilog with DPI
vcs -sverilog dpi_test.sv dpi_example.o -debug_access+all

./simv
```

---

#### Regression Testing

`run_regression.sh`:
```bash
#!/bin/bash

# Regression test script
TEST_LIST="test1 test2 test3 test4"
PASS_COUNT=0
FAIL_COUNT=0

for test in $TEST_LIST; do
    echo "Running $test..."
    ./simv +test=$test > ${test}.log 2>&1

    if grep -q "TEST PASSED" ${test}.log; then
        echo "  PASSED"
        ((PASS_COUNT++))
    else
        echo "  FAILED"
        ((FAIL_COUNT++))
    fi
done

echo "========================"
echo "Regression Summary:"
echo "PASSED: $PASS_COUNT"
echo "FAILED: $FAIL_COUNT"
echo "========================"
```

---

#### Practical Exercise 1: FIFO Design with VCS

**Assignment**: Design and verify a synchronous FIFO using VCS

**Requirements**:
1. Parameterized depth and width
2. Full and empty flags
3. Read and write pointers
4. Comprehensive testbench
5. Achieve 100% code coverage
6. Generate FSDB for Verdi debug

**Submission Checklist**:
- [ ] RTL code (`fifo.sv`)
- [ ] Testbench (`fifo_tb.sv`)
- [ ] Makefile
- [ ] Coverage report showing 100% coverage
- [ ] README with compilation instructions

---

## Week 2-3: Verdi Debug Platform

### Week 2 (Part 2): Verdi Basics

#### Day 1-2: Verdi Environment Setup

**License Configuration**:
```bash
# Verdi uses same license as VCS
export VERDI_HOME=/path/to/verdi
export PATH=$VERDI_HOME/bin:$PATH
export NOVAS_HOME=$VERDI_HOME
```

**Generating Debug Database**:

VCS generates FSDB (Fast Signal Database) for Verdi:

```bash
# Compile with Verdi support
vcs -sverilog -kdb -debug_access+all design.sv testbench.sv

# Alternative: Use FSDB dumping in testbench
# (shown in earlier examples)
```

**Launching Verdi**:
```bash
# Method 1: Standalone with FSDB
verdi -ssf design.fsdb &

# Method 2: With source code and FSDB
verdi -sv design.sv -ssf design.fsdb &

# Method 3: With VCS KDB database
verdi -dbdir ./simv.daidir -ssf design.fsdb &
```

---

#### Day 3-4: Verdi GUI Overview

**Main Windows in Verdi**:

1. **nSchema**: Schematic view
2. **nWave**: Waveform viewer
3. **nTrace**: Source code browser
4. **nMemory**: Memory viewer
5. **Source Browser**: Hierarchy and code

**Example Design for Verdi Learning** (`alu.sv`):
```systemverilog
module alu #(
    parameter WIDTH = 32
) (
    input  logic [WIDTH-1:0]  a,
    input  logic [WIDTH-1:0]  b,
    input  logic [3:0]        opcode,
    output logic [WIDTH-1:0]  result,
    output logic              zero,
    output logic              overflow
);

    always_comb begin
        overflow = 1'b0;
        case (opcode)
            4'b0000: result = a + b;                    // ADD
            4'b0001: result = a - b;                    // SUB
            4'b0010: result = a & b;                    // AND
            4'b0011: result = a | b;                    // OR
            4'b0100: result = a ^ b;                    // XOR
            4'b0101: result = ~a;                       // NOT
            4'b0110: result = a << b[4:0];              // SLL
            4'b0111: result = a >> b[4:0];              // SRL
            4'b1000: result = $signed(a) >>> b[4:0];    // SRA
            default: result = '0;
        endcase

        zero = (result == '0);
    end

endmodule
```

`alu_tb.sv`:
```systemverilog
module alu_tb;
    parameter WIDTH = 32;

    logic [WIDTH-1:0] a, b;
    logic [3:0]       opcode;
    logic [WIDTH-1:0] result;
    logic             zero, overflow;

    alu #(.WIDTH(WIDTH)) dut (.*);

    initial begin
        // Dump for Verdi
        $fsdbDumpfile("alu.fsdb");
        $fsdbDumpvars(0, alu_tb);

        // Test ADD
        a = 32'h00000010; b = 32'h00000020; opcode = 4'b0000;
        #10;

        // Test SUB
        a = 32'h00000030; b = 32'h00000010; opcode = 4'b0001;
        #10;

        // Test AND
        a = 32'hFFFF0000; b = 32'h0000FFFF; opcode = 4'b0010;
        #10;

        // Test OR
        a = 32'hF0F0F0F0; b = 32'h0F0F0F0F; opcode = 4'b0011;
        #10;

        $finish;
    end
endmodule
```

**Compile and View**:
```bash
vcs -sverilog -kdb -debug_access+all alu.sv alu_tb.sv
./simv
verdi -sv alu.sv -ssf alu.fsdb &
```

---

#### Day 5-7: Waveform Analysis with nWave

**Opening Signals in nWave**:

1. **Manual Selection**:
   - Browse hierarchy in Source Browser
   - Select signals
   - Right-click → "Add to nWave"

2. **Automatic**:
   - Use `$fsdbDumpvars()` in testbench
   - Verdi automatically loads signals

**nWave Essential Operations**:

```tcl
# Verdi TCL commands for automation

# Add signals
wvAddSignal -win $_nWave2 /alu_tb/dut/a
wvAddSignal -win $_nWave2 /alu_tb/dut/b
wvAddSignal -win $_nWave2 /alu_tb/dut/result

# Set radix
wvSetRadix -win $_nWave2 -format Hex

# Zoom operations
wvZoomAll -win $_nWave2
wvZoomIn -win $_nWave2
wvZoomOut -win $_nWave2

# Cursor operations
wvSetCursor -win $_nWave2 -time 100ns

# Create markers
wvMarker -win $_nWave2 -time 50ns -text "Event1"
```

**Save nWave Configuration**:
```bash
# In Verdi GUI: File → Save Session
# This creates a .rc file

# Load session later
verdi -ssf alu.fsdb -sswr alu_session.rc
```

---

**Value Change Dump (VCD) vs FSDB**:

```systemverilog
// VCD (standard, portable, large file size)
initial begin
    $dumpfile("design.vcd");
    $dumpvars(0, testbench);
end

// FSDB (Verdi-specific, compact, fast)
initial begin
    $fsdbDumpfile("design.fsdb");
    $fsdbDumpvars(0, testbench);
    // Optional: limit dump depth
    $fsdbDumpvars(2, testbench);  // 2 levels deep
end

// FSDB with time/signal filtering
initial begin
    $fsdbDumpfile("design.fsdb");
    $fsdbDumpvars(0, testbench);

    // Dump only between certain times
    #1000ns $fsdbDumpon;
    #5000ns $fsdbDumpoff;
end
```

---

### Week 3: Advanced Verdi Features

#### Transaction-Level Debug

**Example: AXI Transaction Debug**

`axi_monitor.sv`:
```systemverilog
module axi_monitor (
    input logic aclk,
    input logic aresetn,
    // AXI signals
    input logic        awvalid,
    input logic        awready,
    input logic [31:0] awaddr,
    // ... other AXI signals
);

    // FSDB transaction recording
    initial begin
        $fsdbDumpfile("axi.fsdb");
        $fsdbDumpvars(0, axi_monitor);
        $fsdbDumpMDA(0, axi_monitor);  // Multi-dimensional arrays
    end

    // Transaction tracking
    always @(posedge aclk) begin
        if (awvalid && awready) begin
            $fsdbDumpEventBegin("AXI_WRITE", "ADDR_PHASE");
            $display("AXI Write Address: 0x%h", awaddr);
            $fsdbDumpEventEnd("AXI_WRITE", "ADDR_PHASE");
        end
    end

endmodule
```

---

#### Active Annotation and Drivers/Loads

**Active Annotation**: Shows active signal path in schematic

**Steps**:
1. Open nSchema
2. Select a signal in nWave at specific time
3. Right-click → "Active Annotation"
4. nSchema highlights active path

**Finding Drivers and Loads**:
1. Select signal in nSchema
2. Right-click → "Trace Driver" (shows what drives this signal)
3. Right-click → "Trace Load" (shows what this signal drives)

---

#### Assertion Debug

`assertions_example.sv`:
```systemverilog
module fifo_with_assertions #(
    parameter DEPTH = 16,
    parameter WIDTH = 8
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             wr_en,
    input  logic             rd_en,
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out,
    output logic             full,
    output logic             empty
);

    // FIFO implementation
    logic [WIDTH-1:0] memory [DEPTH];
    logic [$clog2(DEPTH):0] count;
    logic [$clog2(DEPTH)-1:0] wr_ptr, rd_ptr;

    // ... FIFO logic ...

    // Assertions for Verdi
    property no_write_when_full;
        @(posedge clk) disable iff (!rst_n)
        full |-> !wr_en;
    endproperty

    property no_read_when_empty;
        @(posedge clk) disable iff (!rst_n)
        empty |-> !rd_en;
    endproperty

    property count_increment;
        @(posedge clk) disable iff (!rst_n)
        (wr_en && !rd_en && !full) |=> (count == $past(count) + 1);
    endproperty

    assert property (no_write_when_full)
        else $error("Write when full detected!");

    assert property (no_read_when_empty)
        else $error("Read when empty detected!");

    assert property (count_increment)
        else $error("Count increment failed!");

    // Cover properties
    cover property (@(posedge clk) full);
    cover property (@(posedge clk) empty);

endmodule
```

**View Assertions in Verdi**:
```bash
# Compile with assertions enabled
vcs -sverilog -kdb -debug_access+all -assert enable_diag fifo_with_assertions.sv

./simv

# Open in Verdi
verdi -sv fifo_with_assertions.sv -ssf fifo.fsdb &

# In Verdi:
# Tools → Assertion Browser
# View assertion failures, successes, and coverage
```

---

#### Practical Exercise 2: Debug Challenge

**Scenario**: You are given a buggy SPI master design. Use Verdi to:

1. Identify the bugs using waveform analysis
2. Use Active Annotation to trace signal paths
3. Find the root cause using nTrace
4. Document findings with markers and annotations

**Buggy SPI Master** (`spi_master_buggy.sv`):
```systemverilog
module spi_master_buggy (
    input  logic       clk,
    input  logic       rst_n,
    input  logic       start,
    input  logic [7:0] data_in,
    output logic       sclk,
    output logic       mosi,
    output logic       cs_n,
    output logic       done
);

    typedef enum logic [1:0] {
        IDLE,
        TRANSFER,
        FINISH
    } state_t;

    state_t state, next_state;
    logic [7:0] shift_reg;
    logic [2:0] bit_count;
    logic       sclk_en;

    // State register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next_state;
    end

    // Next state logic (BUG: Missing case)
    always_comb begin
        next_state = state;
        case (state)
            IDLE: begin
                if (start)
                    next_state = TRANSFER;
            end
            TRANSFER: begin
                if (bit_count == 3'b111)  // BUG: Should be checking done condition
                    next_state = IDLE;     // BUG: Should go to FINISH
            end
            // BUG: FINISH state not handled
        endcase
    end

    // SCLK generation (BUG: Always running)
    always_ff @(posedge clk) begin
        sclk <= ~sclk;  // BUG: Should only toggle when enabled
    end

    // Shift register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            shift_reg <= 8'h00;
            bit_count <= 3'b000;
        end else if (state == IDLE && start) begin
            shift_reg <= data_in;
            bit_count <= 3'b000;
        end else if (state == TRANSFER && sclk) begin  // BUG: Edge sensitivity
            shift_reg <= {shift_reg[6:0], 1'b0};
            bit_count <= bit_count + 1;
        end
    end

    // Output assignments
    assign mosi = shift_reg[7];
    assign cs_n = (state == IDLE);
    assign done = (state == FINISH);

endmodule
```

**Deliverable**: Bug report with Verdi screenshots showing:
- Waveforms highlighting the bugs
- Active annotation showing problematic paths
- Corrected RTL code

---

## Week 3-4: Questa Advanced Simulator

### Week 3 (Part 2): Questa Basics

#### Day 1-2: Questa Setup and First Simulation

**Environment Setup**:
```bash
export QUESTA_HOME=/path/to/questa
export PATH=$QUESTA_HOME/bin:$PATH
export LM_LICENSE_FILE=port@license_server
```

**Verify Installation**:
```bash
# Check version
vsim -version

# Check license
vmap -version
```

---

**Questa Compilation Flow**:

Unlike VCS's 3-step flow, Questa uses:
1. **vlog/vcom**: Compile Verilog/VHDL
2. **vsim**: Elaborate and simulate

**Example: Counter with Questa**:

```bash
# Create work library (one time)
vlib work

# Compile design
vlog counter.sv counter_tb.sv

# Simulate in command-line mode
vsim -c counter_tb -do "run -all; quit"

# Simulate in GUI mode
vsim counter_tb -do "add wave -r /*; run -all"
```

---

**Questa DO Files** (Script files):

`run.do`:
```tcl
# Compile
vlog counter.sv counter_tb.sv

# Load design
vsim -voptargs=+acc counter_tb

# Add waves
add wave -r /*
add wave -position insertpoint sim:/counter_tb/dut/*

# Configure wave window
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2

# Run simulation
run -all

# Zoom to fit
wave zoom full
```

**Run with DO file**:
```bash
vsim -do run.do
```

---

#### Day 3-5: Questa Advanced Features

**Code Coverage with Questa**:

`run_coverage.do`:
```tcl
# Compile with coverage
vlog +cover=bcesf counter.sv counter_tb.sv
# b: branch, c: condition, e: expression, s: statement, f: FSM

# Simulate with coverage
vsim -coverage counter_tb
run -all

# Generate coverage report
coverage save coverage.ucdb
coverage report -detail -file coverage_report.txt

quit
```

**View Coverage in GUI**:
```bash
vsim -viewcov coverage.ucdb
```

---

**Assertion-Based Verification in Questa**:

`fifo_with_sva.sv`:
```systemverilog
module fifo_with_sva #(
    parameter DEPTH = 8,
    parameter WIDTH = 16
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             push,
    input  logic             pop,
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out,
    output logic             full,
    output logic             empty
);

    // FIFO logic
    logic [WIDTH-1:0] mem [DEPTH];
    logic [$clog2(DEPTH)-1:0] wr_ptr, rd_ptr;
    logic [$clog2(DEPTH):0] count;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_ptr <= '0;
            rd_ptr <= '0;
            count  <= '0;
        end else begin
            case ({push && !full, pop && !empty})
                2'b10: begin  // Push only
                    mem[wr_ptr] <= data_in;
                    wr_ptr <= wr_ptr + 1;
                    count <= count + 1;
                end
                2'b01: begin  // Pop only
                    data_out <= mem[rd_ptr];
                    rd_ptr <= rd_ptr + 1;
                    count <= count - 1;
                end
                2'b11: begin  // Push and pop
                    mem[wr_ptr] <= data_in;
                    data_out <= mem[rd_ptr];
                    wr_ptr <= wr_ptr + 1;
                    rd_ptr <= rd_ptr + 1;
                end
            endcase
        end
    end

    assign full = (count == DEPTH);
    assign empty = (count == 0);

    // SVA Properties
    sequence push_op;
        push && !full;
    endsequence

    sequence pop_op;
        pop && !empty;
    endsequence

    // Assert: No overflow
    property no_overflow;
        @(posedge clk) disable iff (!rst_n)
        full |-> !push;
    endproperty

    // Assert: No underflow
    property no_underflow;
        @(posedge clk) disable iff (!rst_n)
        empty |-> !pop;
    endproperty

    // Assert: Count constraints
    property count_in_range;
        @(posedge clk) disable iff (!rst_n)
        count <= DEPTH;
    endproperty

    // Assert: Push increments count
    property push_increments;
        @(posedge clk) disable iff (!rst_n)
        push_op |=> (count == $past(count) + 1);
    endproperty

    // Formal assertions
    assert property (no_overflow)
        else $error("Overflow: Push when full");

    assert property (no_underflow)
        else $error("Underflow: Pop when empty");

    assert property (count_in_range)
        else $error("Count out of range");

    // Coverage properties
    cover property (@(posedge clk) full);
    cover property (@(posedge clk) empty);
    cover property (@(posedge clk) push && pop);

endmodule
```

**Questa Assertion Simulation**:
```bash
vlog +cover=s fifo_with_sva.sv fifo_tb.sv
vsim -coverage -assertdebug fifo_tb

# In Questa GUI: View → Assertions
```

---

### Week 4: Questa GUI and Debugging

#### Visualizer and Debugging Tools

**Questa Visualizer**: Advanced debugging environment

**Key Features**:
- Dataflow window
- Schematic view
- Class hierarchy
- Memory viewer

**Example: Using Visualizer for UVM**:

```tcl
# Compile UVM testbench
vlog -sv \
    +incdir+$UVM_HOME/src \
    $UVM_HOME/src/uvm_pkg.sv \
    uvm_test.sv

# Simulate with Visualizer
vsim -sv_seed random \
    -classdebug \
    -uvmcontrol=all \
    top

# Visualizer commands
dataflow class_hierarchy
dataflow uvm_topology
```

---

**Waveform Comparison**:

Questa can compare two waveforms (useful for regression):

```tcl
# Load first dataset
vsim -view results_v1.wlf
add wave /testbench/*

# Compare with second dataset
wlf -compare results_v2.wlf

# Differences highlighted in red
```

---

**Memory Debugging**:

```tcl
# View memory contents
vsim testbench
add wave /testbench/dut/memory_array

# Memory window
view -undock memory
mem load -infile memory_init.mem /testbench/dut/memory_array
```

---

#### Mixed-Language Simulation

Questa excels at mixed VHDL/Verilog/SystemVerilog:

`vhdl_component.vhd`:
```vhdl
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;

entity adder is
    Port (
        a : in  STD_LOGIC_VECTOR(7 downto 0);
        b : in  STD_LOGIC_VECTOR(7 downto 0);
        sum : out STD_LOGIC_VECTOR(7 downto 0)
    );
end adder;

architecture Behavioral of adder is
begin
    sum <= std_logic_vector(unsigned(a) + unsigned(b));
end Behavioral;
```

`sv_top.sv`:
```systemverilog
module top;
    logic [7:0] a, b, sum;

    // Instantiate VHDL component
    adder u_adder (
        .a(a),
        .b(b),
        .sum(sum)
    );

    initial begin
        a = 8'h10;
        b = 8'h20;
        #10;
        $display("Sum = %h", sum);
        $finish;
    end
endmodule
```

**Compilation**:
```bash
# Compile VHDL
vcom vhdl_component.vhd

# Compile SystemVerilog
vlog sv_top.sv

# Simulate
vsim top -do "run -all"
```

---

#### Practical Exercise 3: Questa Project

**Assignment**: Implement and verify an AXI4-Lite slave using Questa

**Requirements**:
1. AXI4-Lite slave with register file
2. SystemVerilog Assertions for protocol compliance
3. Functional coverage for all transactions
4. UVM testbench (optional but recommended)
5. Achieve 100% code and functional coverage
6. Document with waveforms from Questa GUI

**Deliverables**:
- [ ] RTL (`axi_lite_slave.sv`)
- [ ] Assertions (`axi_lite_assertions.sv`)
- [ ] Testbench (`axi_lite_tb.sv`)
- [ ] DO scripts for compilation and simulation
- [ ] Coverage report
- [ ] Waveform screenshots

---

## Week 5-6: Formal Verification Tools

### Week 5: Formal Verification Fundamentals

#### Introduction to Formal Methods

**What is Formal Verification?**

Formal verification uses mathematical techniques to prove/disprove properties about a design, without simulation.

**Advantages**:
- Exhaustive verification (all possible states)
- Finds corner cases simulation might miss
- Proves absence of bugs (not just presence)

**Disadvantages**:
- State space explosion for large designs
- Requires formal properties (SVA)
- Steep learning curve

---

**Types of Formal Verification**:

1. **Model Checking**: Verify properties
2. **Equivalence Checking**: Compare two designs
3. **Theorem Proving**: Mathematical proofs (rarely used in industry)

---

#### Property Specification (SVA)

**Basic SVA Syntax**:

```systemverilog
// Immediate assertions (procedural)
assert (condition) else $error("Message");

// Concurrent assertions (declarative)
assert property (@(posedge clk) property_expression);

// Property definition
property property_name;
    @(posedge clk) disable iff (reset)
    antecedent |-> consequent;
endproperty

// Sequence definition
sequence seq_name;
    signal1 ##1 signal2 ##2 signal3;
endsequence
```

---

**SVA Examples for Formal**:

`handshake_properties.sv`:
```systemverilog
module handshake_properties (
    input logic clk,
    input logic rst_n,
    input logic valid,
    input logic ready,
    input logic [31:0] data
);

    // Property 1: Valid remains stable until acknowledged
    property valid_stable;
        @(posedge clk) disable iff (!rst_n)
        valid && !ready |=> valid;
    endproperty

    // Property 2: Data stable when valid is high
    property data_stable;
        @(posedge clk) disable iff (!rst_n)
        valid && !ready |=> $stable(data);
    endproperty

    // Property 3: Valid eventually gets acknowledged
    property valid_acked;
        @(posedge clk) disable iff (!rst_n)
        valid |-> ##[1:10] ready;
    endproperty

    // Property 4: No data change during transfer
    property no_data_change_during_transfer;
        @(posedge clk) disable iff (!rst_n)
        (valid && !ready) |=> (data == $past(data));
    endproperty

    // Bind assertions
    assert property (valid_stable);
    assert property (data_stable);
    assert property (valid_acked);
    assert property (no_data_change_during_transfer);

    // Coverage goals
    cover property (@(posedge clk) valid && ready);
    cover property (@(posedge clk) valid && !ready ##1 valid && ready);

endmodule
```

---

#### JasperGold Basics (Cadence)

**Environment Setup**:
```bash
export JG_HOME=/path/to/jaspergold
export PATH=$JG_HOME/bin:$PATH
```

**Basic JasperGold Flow**:

`arbiter.sv`:
```systemverilog
module arbiter #(
    parameter NUM_CLIENTS = 4
) (
    input  logic                     clk,
    input  logic                     rst_n,
    input  logic [NUM_CLIENTS-1:0]   req,
    output logic [NUM_CLIENTS-1:0]   gnt
);

    logic [$clog2(NUM_CLIENTS)-1:0] ptr;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            gnt <= '0;
            ptr <= '0;
        end else begin
            gnt <= '0;
            for (int i = 0; i < NUM_CLIENTS; i++) begin
                if (req[(ptr + i) % NUM_CLIENTS]) begin
                    gnt[(ptr + i) % NUM_CLIENTS] <= 1'b1;
                    ptr <= (ptr + i + 1) % NUM_CLIENTS;
                    break;
                end
            end
        end
    end

    // Formal properties
    // Property 1: Only one grant at a time
    property one_hot_grant;
        @(posedge clk) disable iff (!rst_n)
        $onehot0(gnt);  // At most one bit set
    endproperty

    // Property 2: Grant only if request
    property gnt_implies_req;
        @(posedge clk) disable iff (!rst_n)
        |gnt |-> (gnt & req) != '0;
    endproperty

    // Property 3: No starvation (liveness - difficult in formal)
    // Using bounded liveness instead
    property no_starvation;
        @(posedge clk) disable iff (!rst_n)
        req[0] |-> ##[0:100] gnt[0];
    endproperty

    assert property (one_hot_grant);
    assert property (gnt_implies_req);
    assert property (no_starvation);

endmodule
```

**JasperGold TCL Script** (`run_formal.tcl`):
```tcl
# Clear previous session
clear -all

# Analyze design files
analyze -sv arbiter.sv

# Elaborate design
elaborate -top arbiter -parameters {NUM_CLIENTS 4}

# Set up clocks and resets
clock clk
reset -expression {!rst_n}

# Prove all properties
prove -all

# Generate reports
report -file formal_report.txt
```

**Run JasperGold**:
```bash
jg -proj arbiter_formal -batch run_formal.tcl
```

---

#### VC Formal (Synopsys)

**Environment Setup**:
```bash
export VCS_HOME=/path/to/vcs
export PATH=$VCS_HOME/bin:$PATH
```

**VC Formal Flow**:

`vcf_script.tcl`:
```tcl
# Create formal session
create_clock clk -period 10
create_reset rst_n -sense low

# Analyze design
analyze -sv arbiter.sv

# Elaborate
elaborate arbiter

# Set up formal environment
set_prove_time_limit 1h
set_prove_per_property_time_limit 10m

# Prove
prove -all

# Check coverage
check_fv_coverage

# Report
report_fv > formal_results.rpt
```

**Run VC Formal**:
```bash
vcf -f vcf_script.tcl
```

---

### Week 6: Advanced Formal Techniques

#### Formal Testbench (Constraints)

**Constraining Inputs for Better Convergence**:

`fifo_formal.sv`:
```systemverilog
module fifo_formal #(
    parameter DEPTH = 4,
    parameter WIDTH = 8
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             push,
    input  logic             pop,
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out,
    output logic             full,
    output logic             empty
);

    // ... FIFO implementation ...

    // Formal assumptions (constraints on inputs)

    // Assumption 1: Don't push when full
    assume property (@(posedge clk) disable iff (!rst_n)
        full |-> !push
    );

    // Assumption 2: Don't pop when empty
    assume property (@(posedge clk) disable iff (!rst_n)
        empty |-> !pop
    );

    // Assumption 3: Reset valid for at least 2 cycles
    assume property (
        $fell(rst_n) |-> ##1 !rst_n
    );

    // Assertions (properties to prove)

    // Assert 1: Full and empty are mutually exclusive
    assert property (@(posedge clk) disable iff (!rst_n)
        !(full && empty)
    );

    // Assert 2: Count never exceeds depth
    assert property (@(posedge clk) disable iff (!rst_n)
        count <= DEPTH
    );

    // Assert 3: Data integrity (what goes in comes out)
    // This requires auxiliary code (shadow memory)

endmodule
```

---

#### Equivalence Checking

**Use Case**: Verify RTL optimizations don't change functionality

**Example: Formality (Synopsys)**:

```tcl
# Formality script for equivalence checking

# Read reference design (golden)
read_sverilog -container r -libname WORK -12 {counter_v1.sv}
set_top r:/WORK/counter

# Read implementation design (revised)
read_sverilog -container i -libname WORK -12 {counter_v2.sv}
set_top i:/WORK/counter

# Match compare points
match

# Verify
verify

# Report
report_failing_points > failing_points.rpt
report_passing_points > passing_points.rpt
```

---

#### Connectivity Checking

**Verifying Hierarchical Connections**:

Formal tools can verify:
- All outputs driven
- No unconnected inputs
- No floating nets
- Proper bit-width matching

**Example: Conformal (Cadence)**:
```tcl
read design -systemverilog soc_top.sv
elaborate

check connectivity
check x_propagation

report > connectivity_report.txt
```

---

#### Practical Exercise 4: Formal Verification Project

**Assignment**: Formal verification of a priority arbiter

**Requirements**:
1. Design a 4-input priority arbiter (fixed priority)
2. Write comprehensive SVA properties:
   - One-hot grant
   - Grant only if request
   - Priority enforcement
   - No starvation (bounded)
3. Add assumptions to constrain inputs
4. Prove all properties using formal tool
5. Cover interesting scenarios

**Properties to Prove**:
```systemverilog
// 1. One-hot grant
assert property ($onehot0(gnt));

// 2. Highest priority wins
assert property (req[3] |-> gnt == 4'b1000);
assert property (req[2] && !req[3] |-> gnt == 4'b0100);
// ... etc

// 3. Grant implies request
assert property ((gnt & req) == gnt);

// 4. Bounded response
assert property (req |-> ##[0:10] |gnt);
```

**Deliverables**:
- [ ] RTL with embedded assertions
- [ ] Formal script (TCL)
- [ ] Proof results showing all properties PASS
- [ ] Coverage report
- [ ] Debug trace for any failures

---

## Integrated Workflow

### Multi-Tool Verification Flow

**Typical Industry Flow**:

```
1. RTL Development
   ↓
2. Formal Connectivity Check
   ↓
3. Simulation (VCS/Questa)
   ├→ Functional verification
   ├→ Code coverage
   └→ Assertion checking
   ↓
4. Debug (Verdi)
   ├→ Waveform analysis
   ├→ Transaction debug
   └→ Root cause analysis
   ↓
5. Formal Property Verification
   ├→ Corner case checking
   └→ Proof of correctness
   ↓
6. Regression Testing
   ├→ Nightly regressions
   └→ Coverage closure
   ↓
7. Gate-level Simulation
   └→ Timing verification
```

---

### Example: Complete Verification Project

**Project**: AXI4 Master Verification

**Week 1-2**: VCS simulation
- Implement directed tests
- Constrained random testing
- Collect code coverage

**Week 3**: Verdi debug
- Debug failing tests
- Waveform analysis
- Transaction viewer

**Week 4**: Questa simulation
- Cross-check with different simulator
- Mixed-language testbench (if VHDL components)
- Assertion verification

**Week 5-6**: Formal verification
- Prove protocol compliance
- Check corner cases
- Equivalence with spec

---

### Makefile for Complete Flow

`Makefile.complete`:
```makefile
# Complete verification Makefile

.PHONY: all vcs questa formal clean

# VCS targets
vcs_compile:
	vcs -sverilog -kdb -debug_access+all \
	    -cm line+cond+fsm+tgl+branch \
	    -f files.f

vcs_sim: vcs_compile
	./simv -cm line+cond+fsm+tgl+branch

vcs_cov:
	urg -dir coverage.vdb -report vcs_coverage

# Verdi targets
verdi:
	verdi -sv -f files.f -ssf dump.fsdb &

# Questa targets
questa_compile:
	vlib work
	vlog +cover=bcesf -f files.f

questa_sim: questa_compile
	vsim -coverage -do "run -all; coverage save questa_cov.ucdb"

questa_cov:
	vsim -viewcov questa_cov.ucdb

# Formal targets
formal:
	jg -proj formal_proj -batch formal.tcl

# Merge coverages
merge_cov:
	# Tool-specific merge commands
	@echo "Merging VCS and Questa coverage..."

# Complete flow
all: vcs_sim questa_sim formal

clean:
	rm -rf simv* csrc coverage.vdb DVEfiles
	rm -rf work questa_cov.ucdb *.wlf transcript
	rm -rf jgproject formal_proj *.fsdb verdiLog
```

---

## Best Practices

### Simulation Best Practices

1. **Use Filelists**: Maintain version control friendly filelists
2. **Incremental Compilation**: Leverage tool features for faster compilation
3. **Parallel Simulations**: Run independent tests in parallel
4. **Coverage-Driven**: Let coverage guide test development
5. **Reproducible**: Use seeds for random tests

---

### Debug Best Practices

1. **Minimal Dump**: Only dump necessary signals
2. **Selective Dumping**: Use `$fsdbDumpon/off` for specific time windows
3. **Hierarchy**: Dump at appropriate hierarchy level
4. **Annotations**: Add markers and comments in waveform
5. **Save Sessions**: Save Verdi/Questa sessions for collaboration

---

### Formal Best Practices

1. **Start Simple**: Begin with simple properties
2. **Constrain Inputs**: Use assumptions wisely
3. **Bounded Liveness**: Use bounded operators for liveness properties
4. **Leverage Cover**: Use cover properties to ensure properties are not vacuous
5. **Incremental**: Prove properties incrementally

---

### General Best Practices

1. **Version Control**: Keep scripts and properties under version control
2. **Documentation**: Document complex properties and assumptions
3. **Regression Suite**: Maintain automated regression tests
4. **Review**: Peer review assertions and formal properties
5. **Continuous Integration**: Integrate with CI/CD pipeline

---

## Additional Resources

### Official Documentation

1. **VCS**:
   - VCS User Guide
   - VCS Command Reference
   - Synopsys SolvNet

2. **Verdi**:
   - Verdi User Guide
   - Verdi Debug Methodology Guide
   - nWave Tutorial

3. **Questa**:
   - Questa Advanced Simulator User Manual
   - Questa Visualizer User Manual
   - ModelSim/Questa Tutorial

4. **Formal**:
   - JasperGold App Notes
   - VC Formal User Guide
   - Questa Formal Verification User Manual

---

### Online Resources

1. **Forums and Communities**:
   - Verification Academy (verificationacademy.com)
   - Stack Overflow (tag: systemverilog)
   - Reddit: r/FPGA, r/ECE
   - EDA Playground (edaplayground.com)

2. **Training**:
   - Synopsys University Courses
   - Siemens Learning Center
   - Cadence Training Services

3. **Blogs and Tutorials**:
   - Verification Gentleman Blog
   - ASIC World
   - ChipVerify

---

### Books

1. **Simulation and Debug**:
   - "SystemVerilog for Verification" - Chris Spear
   - "Writing Testbenches using SystemVerilog" - Janick Bergeron
   - "Advanced UVM" - Brian Hunter

2. **Formal Verification**:
   - "SystemVerilog Assertions and Functional Coverage" - Ashok Mehta
   - "Formal Verification: An Essential Toolkit" - Erik Seligman
   - "A Practical Introduction to PSL" - Cindy Eisner

3. **General**:
   - "Digital Design and Computer Architecture" - Harris & Harris
   - "RTL Modeling with SystemVerilog" - Stuart Sutherland

---

### Practice Projects

**Project Ideas** (in increasing difficulty):

1. **Beginner**:
   - 8-bit ALU
   - UART transmitter/receiver
   - Simple state machine

2. **Intermediate**:
   - FIFO with error injection
   - SPI/I2C master/slave
   - Simple DMA controller

3. **Advanced**:
   - AXI4 interconnect
   - Cache controller
   - Memory controller (DDR)

4. **Expert**:
   - RISC-V core subset
   - PCIe transaction layer
   - Network-on-Chip router

---

## Weekly Progress Checklist

### Week 1
- [ ] VCS environment set up
- [ ] Compiled first design
- [ ] Generated waveforms (VPD/FSDB)
- [ ] Ran coverage analysis
- [ ] Created basic Makefile

### Week 2
- [ ] UVM testbench compilation
- [ ] DPI integration
- [ ] Regression script
- [ ] FIFO project completed
- [ ] Verdi basics learned

### Week 3
- [ ] Verdi waveform analysis proficiency
- [ ] Active annotation used
- [ ] Transaction debug attempted
- [ ] Questa environment set up
- [ ] First Questa simulation

### Week 4
- [ ] Questa coverage analysis
- [ ] Assertion-based verification
- [ ] Mixed-language simulation
- [ ] AXI project in progress
- [ ] Visualizer explored

### Week 5
- [ ] First formal property written
- [ ] JasperGold/VC Formal setup
- [ ] Properties proven
- [ ] Counterexample analyzed
- [ ] Formal constraints applied

### Week 6
- [ ] Advanced formal properties
- [ ] Equivalence checking performed
- [ ] Formal project completed
- [ ] Integrated flow demonstrated
- [ ] All exercises submitted

---

## Troubleshooting Guide

### Common VCS Issues

**Issue**: License errors
```bash
# Solution: Check license file and server
echo $LM_LICENSE_FILE
lmstat -a

# Verify port and server are correct
```

**Issue**: Slow compilation
```bash
# Solution: Use parallel compilation
vcs -j8 ...  # Use 8 cores
```

**Issue**: Large FSDB files
```systemverilog
// Solution: Selective dumping
$fsdbDumpvars(2, testbench);  // Only 2 levels deep
$fsdbDumpoff;  // Turn off dumping when not needed
```

---

### Common Verdi Issues

**Issue**: FSDB file not found
```bash
# Solution: Check file path and dumping
# Ensure $fsdbDumpfile was called in testbench
```

**Issue**: Missing source code
```bash
# Solution: Compile with -kdb and provide source
verdi -sv design.sv -ssf dump.fsdb
```

---

### Common Questa Issues

**Issue**: "vsim not found"
```bash
# Solution: Check PATH and QUESTA_HOME
export PATH=$QUESTA_HOME/bin:$PATH
```

**Issue**: Optimization prevents debug
```bash
# Solution: Disable optimization
vsim -voptargs=+acc ...
```

---

### Common Formal Issues

**Issue**: Property doesn't converge
```
# Solution: Add assumptions to constrain state space
assume property (valid_input_range);
```

**Issue**: Vacuous property (proves trivially)
```
# Solution: Add cover property to ensure reachability
cover property (antecedent_happens);
```

---

## Certification and Career

### Industry Certifications

1. **Synopsys Certification**:
   - VCS Certified User
   - Verdi Certified User

2. **Siemens Certification**:
   - Questa Advanced Simulator Certification

3. **Cadence Certification**:
   - JasperGold Formal Verification Certification

---

### Career Paths

With these skills, you can pursue:

1. **Verification Engineer**: Focus on testbench development
2. **DV (Design Verification) Engineer**: Comprehensive verification
3. **Formal Verification Engineer**: Specialize in formal methods
4. **CAD/EDA Engineer**: Tool development and support
5. **Technical Lead**: Guide verification strategy

**Salary Range** (US, 2024):
- Entry Level: $90K - $120K
- Mid-Level: $120K - $160K
- Senior: $160K - $220K
- Principal/Staff: $220K+

---

## Conclusion

This guide has provided a comprehensive 4-6 week curriculum for learning industry-standard EDA tools. The key to mastery is **consistent practice** and **hands-on projects**.

### Next Steps

1. **Complete all exercises** in this guide
2. **Build a portfolio** with verification projects
3. **Contribute to open-source** verification projects
4. **Join communities** and ask questions
5. **Stay updated** with latest tool features

### Final Advice

- **Don't rush**: Take time to understand concepts deeply
- **Debug, debug, debug**: Most learning happens during debugging
- **Read documentation**: Official docs are invaluable
- **Network**: Connect with other verification engineers
- **Keep learning**: EDA tools evolve rapidly

---

**Good luck with your journey in semiconductor verification!**

---

*Last Updated: 2025-11-18*
*Version: 1.0*

---

## Appendix A: Quick Reference Commands

### VCS Quick Reference
```bash
# Compilation
vcs -sverilog -debug_access+all -kdb design.sv tb.sv

# With coverage
vcs -sverilog -cm line+cond+fsm+tgl+branch design.sv tb.sv

# UVM
vcs -sverilog -ntb_opts uvm-1.2 design.sv tb.sv

# Run simulation
./simv

# Generate coverage report
urg -dir coverage.vdb
```

### Verdi Quick Reference
```bash
# Launch Verdi
verdi -sv design.sv -ssf dump.fsdb &

# With KDB
verdi -kdb simv.daidir -ssf dump.fsdb &

# Coverage
verdi -cov -covdir coverage.vdb
```

### Questa Quick Reference
```bash
# Create library
vlib work

# Compile
vlog design.sv tb.sv

# Simulate GUI
vsim tb

# Simulate batch
vsim -c tb -do "run -all; quit"

# With coverage
vlog +cover=bcesf design.sv tb.sv
vsim -coverage tb
```

### Formal Quick Reference
```bash
# JasperGold
jg -proj my_proj -batch formal.tcl

# VC Formal
vcf -f vcf_script.tcl
```

---

## Appendix B: Sample File Structure

```
project/
├── rtl/
│   ├── design1.sv
│   ├── design2.sv
│   └── include/
│       └── defines.svh
├── tb/
│   ├── testbench.sv
│   ├── tests/
│   │   ├── test_base.sv
│   │   └── test1.sv
│   └── include/
├── formal/
│   ├── properties.sv
│   └── formal.tcl
├── scripts/
│   ├── run_vcs.sh
│   ├── run_questa.sh
│   └── run_formal.sh
├── sim/
│   ├── vcs/
│   └── questa/
├── cov/
├── Makefile
└── README.md
```

---

*End of Document*
