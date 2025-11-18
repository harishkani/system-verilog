# Advanced Verification - UVM and Formal Methods
### From Fundamentals to Industry Best Practices

---

## Table of Contents

### Part 1: Verification Fundamentals
1. [Introduction to Verification](#1-introduction-to-verification)
2. [Verification Methodology Evolution](#2-verification-methodology-evolution)
3. [Constrained Random Verification](#3-constrained-random-verification)
4. [Functional Coverage](#4-functional-coverage)
5. [Assertions (SVA)](#5-assertions-sva)

### Part 2: Universal Verification Methodology (UVM)
6. [UVM Introduction](#6-uvm-introduction)
7. [UVM Testbench Architecture](#7-uvm-testbench-architecture)
8. [UVM Components](#8-uvm-components)
9. [UVM Sequences](#9-uvm-sequences)
10. [UVM Configuration and Factory](#10-uvm-configuration-and-factory)
11. [UVM Register Layer](#11-uvm-register-layer)
12. [Complete UVM Example](#12-complete-uvm-example)

### Part 3: Formal Verification
13. [Formal Verification Introduction](#13-formal-verification-introduction)
14. [Formal Property Verification](#14-formal-property-verification)
15. [Model Checking](#15-model-checking)
16. [Equivalence Checking](#16-equivalence-checking)
17. [Formal vs Simulation](#17-formal-vs-simulation)

### Part 4: Advanced Topics
18. [Coverage-Driven Verification](#18-coverage-driven-verification)
19. [Verification Planning](#19-verification-planning)
20. [Industry Best Practices](#20-industry-best-practices)

---

## Part 1: Verification Fundamentals

## 1. Introduction to Verification

### 1.1 Why Verification?

**The Verification Crisis:**
```
Design Complexity: Doubling every ~18 months
Verification Complexity: Doubling every ~12 months!

Modern SoC:
- 100M+ gates
- 1000+ IPs
- 100+ engineers
- 70% of project time = Verification!
```

**Cost of Bugs:**
```
Bug Found At          Cost to Fix
─────────────────────────────────
RTL design           $1
RTL verification     $10
Post-synthesis       $100
Post-silicon         $10,000
In the field         $1,000,000+
```

### 1.2 Verification Goals

**Primary Goal:** Prove design correctness

**Coverage Metrics:**
1. **Code Coverage** - Which lines executed?
2. **Functional Coverage** - Which scenarios tested?
3. **Assertion Coverage** - Which properties checked?

**Verification Complete When:**
- All features verified
- All coverage goals met
- All bugs found and fixed
- Confidence high enough to tape out

### 1.3 Verification Approaches

```
┌──────────────────────────────────────┐
│ Verification Approaches              │
├──────────────────────────────────────┤
│ 1. Directed Testing                  │
│    - Manual test cases               │
│    - Predictable, limited coverage   │
│                                      │
│ 2. Constrained Random                │
│    - Automated test generation       │
│    - High coverage, unpredictable    │
│                                      │
│ 3. Formal Verification               │
│    - Mathematical proof              │
│    - Exhaustive, complex designs hard│
│                                      │
│ 4. Emulation                         │
│    - Hardware acceleration           │
│    - Run real software               │
└──────────────────────────────────────┘
```

---

## 2. Verification Methodology Evolution

### 2.1 History

```
1980s: Verilog Test Benches
       - Simple, procedural
       - Manual stimulus

1990s: Vera, e Language
       - Object-oriented
       - Constrained random

2000s: SystemVerilog + OVM
       - Unified language
       - Standardized methodology

2010s: UVM (Universal Verification Methodology)
       - Industry standard
       - Accellera/IEEE standard
       - Used in >90% of ASIC projects

2020s: Portable Stimulus (PSS)
       - Abstract test descriptions
       - Reusable across platforms
```

### 2.2 Why SystemVerilog?

**SystemVerilog = Verilog + OOP + Assertions + Coverage**

```systemverilog
// Object-Oriented Programming
class packet;
  rand bit [7:0] addr;
  rand bit [31:0] data;

  constraint addr_range {
    addr inside {[0:15]};
  }
endclass

// Assertions
property req_ack;
  @(posedge clk) req |-> ##[1:3] ack;
endproperty
assert property (req_ack);

// Coverage
covergroup cg @(posedge clk);
  addr_cp: coverpoint addr {
    bins low = {[0:7]};
    bins high = {[8:15]};
  }
endgroup
```

---

## 3. Constrained Random Verification

### 3.1 Basic Randomization

```systemverilog
class basic_packet;
  rand bit [7:0] length;
  rand bit [31:0] payload;
  rand bit parity;

  // Randomize
  function void display();
    $display("Length=%0d, Payload=%0h, Parity=%0b",
             length, payload, parity);
  endfunction
endclass

module test;
  initial begin
    basic_packet pkt = new();

    repeat (10) begin
      pkt.randomize();
      pkt.display();
    end
  end
endmodule
```

### 3.2 Constraints

```systemverilog
class constrained_packet;
  rand bit [7:0] addr;
  rand bit [31:0] data;
  rand bit [1:0] packet_type;

  // Simple constraint
  constraint addr_range {
    addr inside {[0:63]};
  }

  // Conditional constraint
  constraint data_valid {
    if (packet_type == 2'b00)
      data == 32'h0;
    else
      data != 32'h0;
  }

  // Distribution constraint
  constraint addr_dist {
    addr dist {
      [0:15]   := 40,  // 40% weight
      [16:31]  := 30,  // 30% weight
      [32:63]  := 30   // 30% weight
    };
  }

  // Implication constraint
  constraint payload_size {
    (packet_type == 2'b01) -> (addr < 32);
  }

  // Solve-before constraint
  constraint solve_order {
    solve packet_type before data;
    solve addr before data;
  }
endclass
```

### 3.3 Advanced Randomization

```systemverilog
class transaction;
  rand bit [31:0] data[];
  rand int length;

  // Dynamic array constraint
  constraint data_size {
    length inside {[1:16]};
    data.size() == length;
  }

  // Iterate over array
  constraint all_unique {
    foreach (data[i])
      foreach (data[j])
        if (i != j) data[i] != data[j];
  }

  // Custom randomization
  function void post_randomize();
    // Called after randomization succeeds
    $display("Generated transaction with %0d words", length);
  endfunction

  function void pre_randomize();
    // Called before randomization
    // Can set up variables
  endfunction
endclass
```

### 3.4 In-line Constraints

```systemverilog
initial begin
  transaction txn = new();

  // Override constraints
  txn.randomize() with {
    length < 8;
    data[0] == 32'hDEADBEEF;
  };

  // Disable constraints
  txn.addr_range.constraint_mode(0);
  txn.randomize();
end
```

---

## 4. Functional Coverage

### 4.1 Covergroups

```systemverilog
module dut_monitor;
  logic [2:0] opcode;
  logic [7:0] addr;
  logic       valid;

  // Define coverage
  covergroup operation_cov @(posedge clk);
    // Coverpoint for opcode
    opcode_cp: coverpoint opcode {
      bins read  = {3'b000};
      bins write = {3'b001};
      bins add   = {3'b010};
      bins sub   = {3'b011};
      bins mul   = {3'b100};
      bins div   = {3'b101};
      illegal_bins illegal = {3'b110, 3'b111};
    }

    // Coverpoint for address
    addr_cp: coverpoint addr {
      bins low    = {[0:63]};
      bins medium = {[64:127]};
      bins high   = {[128:191]};
      bins max    = {[192:255]};
    }

    // Coverpoint with valid signal
    valid_cp: coverpoint valid;

    // Cross coverage
    op_addr_cross: cross opcode_cp, addr_cp {
      // Ignore certain combinations
      ignore_bins invalid = binsof(opcode_cp.illegal);
    }

    // Cross with condition
    valid_op_cross: cross opcode_cp, valid_cp {
      bins valid_reads = binsof(opcode_cp.read) && binsof(valid_cp) intersect {1};
    }
  endgroup

  // Instantiate
  operation_cov cov_inst = new();

endmodule
```

### 4.2 Transition Coverage

```systemverilog
covergroup state_transitions @(posedge clk);
  state_cp: coverpoint current_state {
    bins idle    = {IDLE};
    bins active  = {ACTIVE};
    bins wait_st = {WAIT};
    bins done    = {DONE};

    // State transitions
    bins idle_to_active = (IDLE => ACTIVE);
    bins active_to_wait = (ACTIVE => WAIT);
    bins wait_to_active = (WAIT => ACTIVE);
    bins any_to_done    = (IDLE, ACTIVE, WAIT => DONE);

    // Sequence transitions
    bins normal_flow = (IDLE => ACTIVE => WAIT => DONE);

    // Wildcard transitions
    bins back_to_idle = (ACTIVE, WAIT => IDLE);
  }
endgroup
```

### 4.3 Coverage Options

```systemverilog
covergroup advanced_cov @(posedge clk);
  option.per_instance = 1;       // Separate coverage per instance
  option.at_least = 10;          // Each bin hit 10 times minimum
  option.auto_bin_max = 64;      // Max auto bins

  data_cp: coverpoint data {
    option.weight = 2;           // Higher weight in coverage calc
    option.goal = 100;           // Target 100% coverage
    option.comment = "Data values";

    bins zero = {0};
    bins low  = {[1:100]};
    bins high = {[101:255]};
  }
endgroup
```

### 4.4 Querying Coverage

```systemverilog
initial begin
  automatic real coverage_val;

  #1000;

  coverage_val = $get_coverage();
  $display("Overall coverage: %0f%%", coverage_val);

  // Per covergroup
  coverage_val = operation_cov::get_coverage();
  $display("Operation coverage: %0f%%", coverage_val);

  // Per coverpoint
  coverage_val = operation_cov::opcode_cp.get_coverage();
  $display("Opcode coverage: %0f%%", coverage_val);
end
```

---

## 5. Assertions (SVA)

### 5.1 Immediate Assertions

```systemverilog
module assertions_example (
  input logic clk,
  input logic req,
  input logic ack,
  input logic [7:0] data
);

  // Immediate assertion (combinational)
  always_comb begin
    assert (data != 8'hXX) else $error("Data contains X");
  end

  // Check at specific event
  always @(posedge req) begin
    assert (data inside {[0:127]})
      else $error("Invalid data %0d on request", data);
  end

endmodule
```

### 5.2 Concurrent Assertions

**Basic Temporal Operators:**
```systemverilog
// ##n : Delay by n cycles
property delay_example;
  @(posedge clk) req |-> ##3 ack;  // ack comes 3 cycles after req
endproperty

// ##[m:n] : Delay range
property range_delay;
  @(posedge clk) req |-> ##[1:5] ack;  // ack comes 1-5 cycles after
endproperty

// [*n] : Consecutive repetition
property consecutive;
  @(posedge clk) valid[*3] |-> done;  // valid high for 3 cycles
endproperty

// [->n] : Goto repetition (non-consecutive)
property goto_rep;
  @(posedge clk) start |-> (event[->3]) ##1 finish;
  // event happens 3 times (not necessarily consecutive), then finish
endproperty

// [=n] : Non-consecutive repetition ending
property nonconsec_end;
  @(posedge clk) start |-> (req[=4]) ##1 done;
endproperty
```

### 5.3 Real-World Assertion Examples

```systemverilog
module protocol_checker (
  input logic clk,
  input logic rst_n,
  input logic req,
  input logic gnt,
  input logic valid,
  input logic ready
);

  // Request-Grant protocol
  property req_gnt_protocol;
    @(posedge clk) disable iff (!rst_n)
      req |-> ##[1:10] gnt;
  endproperty
  assert property (req_gnt_protocol)
    else $error("Grant not received within 10 cycles");

  // Handshake protocol
  property valid_ready_handshake;
    @(posedge clk) disable iff (!rst_n)
      valid && !ready |=> valid;  // Valid stays high until ready
  endproperty
  assert property (valid_ready_handshake);

  // Mutual exclusion
  property mutex;
    @(posedge clk) disable iff (!rst_n)
      !(req && gnt);  // Never both high
  endproperty
  assert property (mutex);

  // Stability check
  property data_stable;
    @(posedge clk) disable iff (!rst_n)
      $rose(valid) |-> $stable(data) until ready;
  endproperty
  assert property (data_stable);

  // Eventually
  property eventual_done;
    @(posedge clk) disable iff (!rst_n)
      start |-> s_eventually done;
  endproperty
  assert property (eventual_done);

endmodule
```

### 5.4 Assertion-Based Verification

```systemverilog
// Assume-Guarantee paradigm
module interface_checker (
  input logic clk,
  input logic req,
  input logic ack
);

  // Assume (environment promise)
  assume property (@(posedge clk) req |-> ##1 !req);
    // Environment won't assert req on consecutive cycles

  // Assert (design promise)
  assert property (@(posedge clk) req |-> ##[1:3] ack);
    // Design will ack within 1-3 cycles

  // Cover (check reachability)
  cover property (@(posedge clk) req ##[2:2] ack);
    // Check if 2-cycle ack happens

endmodule
```

---

## Part 2: Universal Verification Methodology (UVM)

## 6. UVM Introduction

### 6.1 What is UVM?

**UVM** = Standardized methodology for verification using SystemVerilog

**Key Benefits:**
- Reusable testbench components
- Scalable to large designs
- Industry standard (Accellera/IEEE)
- Rich ecosystem (VIP, tools, training)

### 6.2 UVM Philosophy

```
Separation of Concerns:
- Stimulus generation (sequences)
- DUT interface (driver)
- Response checking (monitor, scoreboard)
- Coverage collection (separate)

Configurability:
- Factory pattern for polymorphism
- Configuration database for parameters
- Phases for coordinated execution
```

### 6.3 UVM Class Hierarchy

```
uvm_object
    ├── uvm_transaction
    ├── uvm_sequence_item
    └── uvm_sequence

uvm_component
    ├── uvm_driver
    ├── uvm_monitor
    ├── uvm_agent
    ├── uvm_scoreboard
    ├── uvm_env
    └── uvm_test
```

---

## 7. UVM Testbench Architecture

### 7.1 Typical UVM Testbench

```
┌─────────────────────────────────────────────┐
│ UVM Test                                    │
│  ┌───────────────────────────────────────┐ │
│  │ Environment (ENV)                     │ │
│  │  ┌─────────────┐   ┌───────────────┐ │ │
│  │  │ Agent       │   │ Scoreboard    │ │ │
│  │  │ ┌─────────┐ │   │               │ │ │
│  │  │ │Sequencer│ │   │               │ │ │
│  │  │ └────┬────┘ │   │               │ │ │
│  │  │      │      │   │               │ │ │
│  │  │ ┌────▼────┐ │   │               │ │ │
│  │  │ │ Driver  │ │   │               │ │ │
│  │  │ └────┬────┘ │   │               │ │ │
│  │  │      │      │   │               │ │ │
│  │  │ ┌────▼────┐ │   │      ▲        │ │ │
│  │  │ │Interface│ │   │      │        │ │ │
│  │  │ └────┬────┘ │   │      │        │ │ │
│  │  │      │      │   │  ┌───┴──────┐ │ │ │
│  │  │      ▼      │   │  │ Monitor  │ │ │ │
│  │  │   ┌─────┐  │   │  └───▲──────┘ │ │ │
│  │  │   │ DUT │◄─┼───┼──────┘        │ │ │
│  │  │   └─────┘  │   │               │ │ │
│  │  └─────────────┘   └───────────────┘ │ │
│  └───────────────────────────────────────┘ │
└─────────────────────────────────────────────┘
```

---

## 8. UVM Components

### 8.1 Transaction

```systemverilog
class my_transaction extends uvm_sequence_item;
  rand bit [7:0] addr;
  rand bit [31:0] data;
  rand bit we;  // Write enable

  `uvm_object_utils_begin(my_transaction)
    `uvm_field_int(addr, UVM_ALL_ON)
    `uvm_field_int(data, UVM_ALL_ON)
    `uvm_field_int(we, UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name = "my_transaction");
    super.new(name);
  endfunction

  constraint addr_c {
    addr inside {[0:127]};
  }

  constraint data_c {
    if (we == 0)
      data == 0;
  }
endclass
```

### 8.2 Driver

```systemverilog
class my_driver extends uvm_driver #(my_transaction);
  `uvm_component_utils(my_driver)

  virtual my_interface vif;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual my_interface)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "Virtual interface not set")
  endfunction

  task run_phase(uvm_phase phase);
    forever begin
      seq_item_port.get_next_item(req);
      drive_transaction(req);
      seq_item_port.item_done();
    end
  endtask

  task drive_transaction(my_transaction trans);
    @(posedge vif.clk);
    vif.addr <= trans.addr;
    vif.data <= trans.data;
    vif.we   <= trans.we;
    vif.valid <= 1'b1;

    @(posedge vif.clk);
    while (!vif.ready) @(posedge vif.clk);

    vif.valid <= 1'b0;
  endtask
endclass
```

### 8.3 Monitor

```systemverilog
class my_monitor extends uvm_monitor;
  `uvm_component_utils(my_monitor)

  virtual my_interface vif;
  uvm_analysis_port #(my_transaction) ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual my_interface)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "Virtual interface not set")
  endfunction

  task run_phase(uvm_phase phase);
    my_transaction trans;

    forever begin
      @(posedge vif.clk);
      if (vif.valid && vif.ready) begin
        trans = my_transaction::type_id::create("trans");
        trans.addr = vif.addr;
        trans.data = vif.data;
        trans.we   = vif.we;

        ap.write(trans);  // Send to scoreboard
      end
    end
  endtask
endclass
```

### 8.4 Agent

```systemverilog
class my_agent extends uvm_agent;
  `uvm_component_utils(my_agent)

  my_driver    driver;
  my_sequencer sequencer;
  my_monitor   monitor;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    monitor = my_monitor::type_id::create("monitor", this);

    if (get_is_active() == UVM_ACTIVE) begin
      driver = my_driver::type_id::create("driver", this);
      sequencer = my_sequencer::type_id::create("sequencer", this);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    if (get_is_active() == UVM_ACTIVE) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);
    end
  endfunction
endclass
```

### 8.5 Scoreboard

```systemverilog
class my_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(my_scoreboard)

  uvm_analysis_imp #(my_transaction, my_scoreboard) ap;

  int transactions_checked;
  int errors;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  function void write(my_transaction trans);
    my_transaction expected;

    // Check transaction
    expected = predict(trans);

    if (trans.data != expected.data) begin
      `uvm_error("MISMATCH",
        $sformatf("Data mismatch! Got: %0h, Expected: %0h",
                  trans.data, expected.data))
      errors++;
    end

    transactions_checked++;
  endfunction

  function my_transaction predict(my_transaction trans);
    // Reference model logic
    my_transaction exp = new();
    exp.addr = trans.addr;
    exp.data = memory[trans.addr];  // Simplified
    return exp;
  endfunction

  function void report_phase(uvm_phase phase);
    `uvm_info("SCOREBOARD",
      $sformatf("Checked %0d transactions, %0d errors",
                transactions_checked, errors), UVM_LOW)
  endfunction
endclass
```

---

## 9. UVM Sequences

### 9.1 Basic Sequence

```systemverilog
class my_sequence extends uvm_sequence #(my_transaction);
  `uvm_object_utils(my_sequence)

  function new(string name = "my_sequence");
    super.new(name);
  endfunction

  task body();
    my_transaction trans;

    repeat (10) begin
      trans = my_transaction::type_id::create("trans");

      start_item(trans);
      assert(trans.randomize());
      finish_item(trans);

      get_response(rsp);  // Optional
    end
  endtask
endclass
```

### 9.2 Directed Sequence

```systemverilog
class directed_sequence extends uvm_sequence #(my_transaction);
  `uvm_object_utils(directed_sequence)

  task body();
    my_transaction trans;

    // Write to address 0
    trans = my_transaction::type_id::create("trans");
    start_item(trans);
    trans.addr = 8'h00;
    trans.data = 32'hDEADBEEF;
    trans.we = 1'b1;
    finish_item(trans);

    // Read from address 0
    trans = my_transaction::type_id::create("trans");
    start_item(trans);
    trans.addr = 8'h00;
    trans.we = 1'b0;
    finish_item(trans);
  endtask
endclass
```

### 9.3 Layered Sequences

```systemverilog
class burst_sequence extends uvm_sequence #(my_transaction);
  `uvm_object_utils(burst_sequence)

  rand int num_transfers;

  constraint num_c {
    num_transfers inside {[4:16]};
  }

  task body();
    my_transaction trans;
    bit [7:0] start_addr;

    start_addr = $urandom();

    for (int i = 0; i < num_transfers; i++) begin
      trans = my_transaction::type_id::create($sformatf("trans_%0d", i));
      start_item(trans);
      assert(trans.randomize() with {
        addr == start_addr + i;
      });
      finish_item(trans);
    end
  endtask
endclass

class complex_test_sequence extends uvm_sequence;
  `uvm_object_utils(complex_test_sequence)

  task body();
    burst_sequence burst_seq;
    directed_sequence dir_seq;

    // Run burst sequence
    burst_seq = burst_sequence::type_id::create("burst_seq");
    burst_seq.start(m_sequencer);

    // Run directed sequence
    dir_seq = directed_sequence::type_id::create("dir_seq");
    dir_seq.start(m_sequencer);
  endtask
endclass
```

---

## 10. UVM Configuration and Factory

### 10.1 Configuration Database

```systemverilog
class my_env extends uvm_env;
  `uvm_component_utils(my_env)

  my_agent agent;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Set configuration
    uvm_config_db#(int)::set(this, "agent", "num_transactions", 1000);
    uvm_config_db#(bit)::set(this, "agent", "coverage_enable", 1);

    agent = my_agent::type_id::create("agent", this);
  endfunction
endclass

class my_agent extends uvm_agent;
  int num_transactions;
  bit coverage_enable;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Get configuration
    if (!uvm_config_db#(int)::get(this, "", "num_transactions", num_transactions))
      num_transactions = 100;  // Default

    if (!uvm_config_db#(bit)::get(this, "", "coverage_enable", coverage_enable))
      coverage_enable = 0;

    `uvm_info("CONFIG",
      $sformatf("num_transactions=%0d, coverage=%0b",
                num_transactions, coverage_enable), UVM_MEDIUM)
  endfunction
endclass
```

### 10.2 Factory Pattern

```systemverilog
// Base transaction
class base_transaction extends uvm_sequence_item;
  rand bit [7:0] addr;
  `uvm_object_utils(base_transaction)
  // ...
endclass

// Extended transaction
class extended_transaction extends base_transaction;
  rand bit [31:0] extra_data;
  `uvm_object_utils(extended_transaction)
  // ...
endclass

// Test using factory override
class my_test extends uvm_test;
  `uvm_component_utils(my_test)

  my_env env;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Override base with extended
    base_transaction::type_id::set_type_override(
      extended_transaction::get_type());

    env = my_env::type_id::create("env", this);
  endfunction
endclass
```

---

## 11. UVM Register Layer

### 11.1 Register Model

```systemverilog
// Register definition
class status_reg extends uvm_reg;
  rand uvm_reg_field ready;
  rand uvm_reg_field error;
  rand uvm_reg_field done;

  `uvm_object_utils(status_reg)

  function new(string name = "status_reg");
    super.new(name, 32, UVM_NO_COVERAGE);
  endfunction

  virtual function void build();
    ready = uvm_reg_field::type_id::create("ready");
    error = uvm_reg_field::type_id::create("error");
    done = uvm_reg_field::type_id::create("done");

    ready.configure(this, 1, 0, "RO", 0, 1'b0, 1, 1, 0);
    error.configure(this, 1, 1, "W1C", 0, 1'b0, 1, 1, 0);
    done.configure(this, 1, 2, "RO", 0, 1'b0, 1, 1, 0);
  endfunction
endclass

// Register block
class my_reg_block extends uvm_reg_block;
  rand status_reg status;
  rand data_reg data;

  `uvm_object_utils(my_reg_block)

  function new(string name = "my_reg_block");
    super.new(name, UVM_NO_COVERAGE);
  endfunction

  virtual function void build();
    status = status_reg::type_id::create("status");
    status.configure(this, null, "status");
    status.build();

    // Create address map
    default_map = create_map("default_map", 0, 4, UVM_LITTLE_ENDIAN);
    default_map.add_reg(status, 32'h00, "RW");

    lock_model();  // Finalize
  endfunction
endclass
```

### 11.2 Register Access

```systemverilog
class reg_test_sequence extends uvm_sequence;
  `uvm_object_utils(reg_test_sequence)

  my_reg_block regmodel;

  task body();
    uvm_status_e status;
    uvm_reg_data_t data;

    // Write register
    regmodel.status.write(status, 32'h1, .parent(this));

    // Read register
    regmodel.status.read(status, data, .parent(this));
    `uvm_info("REG", $sformatf("Status = %0h", data), UVM_LOW)

    // Field access
    regmodel.status.ready.set(1'b1);
    regmodel.status.update(status, .parent(this));

    // Peek (backdoor)
    regmodel.status.peek(status, data, .parent(this));
  endtask
endclass
```

---

## 12. Complete UVM Example

```systemverilog
// Complete testbench for simple memory

// Transaction
class mem_transaction extends uvm_sequence_item;
  rand bit [7:0] addr;
  rand bit [31:0] data;
  rand bit we;

  `uvm_object_utils_begin(mem_transaction)
    `uvm_field_int(addr, UVM_ALL_ON)
    `uvm_field_int(data, UVM_ALL_ON)
    `uvm_field_int(we, UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name = "mem_transaction");
    super.new(name);
  endfunction
endclass

// Sequencer
typedef uvm_sequencer #(mem_transaction) mem_sequencer;

// Driver (already shown above)
// Monitor (already shown above)
// Agent (already shown above)
// Scoreboard (already shown above)

// Environment
class mem_env extends uvm_env;
  `uvm_component_utils(mem_env)

  mem_agent agent;
  mem_scoreboard scoreboard;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent = mem_agent::type_id::create("agent", this);
    scoreboard = mem_scoreboard::type_id::create("scoreboard", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    agent.monitor.ap.connect(scoreboard.ap);
  endfunction
endclass

// Test
class mem_test extends uvm_test;
  `uvm_component_utils(mem_test)

  mem_env env;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = mem_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    my_sequence seq;

    phase.raise_objection(this);

    seq = my_sequence::type_id::create("seq");
    seq.start(env.agent.sequencer);

    phase.drop_objection(this);
  endtask
endclass

// Top module
module top;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  logic clk;
  mem_interface vif(clk);

  memory dut (
    .clk(vif.clk),
    .addr(vif.addr),
    .data(vif.data),
    .we(vif.we),
    .valid(vif.valid),
    .ready(vif.ready)
  );

  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  initial begin
    uvm_config_db#(virtual mem_interface)::set(null, "*", "vif", vif);
    run_test("mem_test");
  end
endmodule
```

---

## Part 3: Formal Verification

## 13. Formal Verification Introduction

### 13.1 What is Formal?

**Formal Verification** = Mathematical proof of correctness

**vs Simulation:**
```
┌─────────────────┬───────────┬────────────┐
│ Aspect          │ Formal    │ Simulation │
├─────────────────┼───────────┼────────────┤
│ Coverage        │ Exhaustive│ Sample     │
│ Counterexample  │ Always    │ Random     │
│ Capacity        │ Limited   │ Unlimited  │
│ Runtime         │ Hours-Days│ Minutes    │
│ Setup Effort    │ High      │ Medium     │
└─────────────────┴───────────┴────────────┘
```

### 13.2 Formal Methods

```
1. Model Checking
   - Exhaustively check state space
   - Find bugs or prove correctness

2. Equivalence Checking
   - Prove two designs equivalent
   - RTL vs Gates, pre vs post-optimization

3. Theorem Proving
   - Manual proof construction
   - For very complex properties
```

---

## 14. Formal Property Verification

### 14.1 SVA for Formal

```systemverilog
module fifo_properties (
  input logic clk,
  input logic rst_n,
  input logic push,
  input logic pop,
  input logic empty,
  input logic full,
  input logic [3:0] count
);

  // Safety properties (must never violate)
  property no_push_when_full;
    @(posedge clk) disable iff (!rst_n)
      full |-> !push;
  endproperty
  assert property (no_push_when_full);

  property no_pop_when_empty;
    @(posedge clk) disable iff (!rst_n)
      empty |-> !pop;
  endproperty
  assert property (no_pop_when_empty);

  // Liveness properties (eventually happens)
  property push_increases_count;
    @(posedge clk) disable iff (!rst_n)
      push && !full |=> count > $past(count);
  endproperty
  assert property (push_increases_count);

  // Invariants (always true)
  property count_bounds;
    @(posedge clk) disable iff (!rst_n)
      count <= 16;
  endproperty
  assert property (count_bounds);

  property empty_iff_zero;
    @(posedge clk) disable iff (!rst_n)
      empty == (count == 0);
  endproperty
  assert property (empty_iff_zero);

endmodule

// Bind to design
bind fifo fifo_properties fifo_props (.*);
```

### 14.2 Assumptions for Formal

```systemverilog
// Constrain inputs for formal
module formal_constraints;
  // Assume proper reset
  assume property (@(posedge clk) $rose(rst_n) |-> ##1 count == 0);

  // Assume valid inputs (not X/Z)
  assume property (@(posedge clk) !$isunknown(push));
  assume property (@(posedge clk) !$isunknown(pop));

  // Assume mutually exclusive
  assume property (@(posedge clk) !(push && pop && empty));

endmodule
```

### 14.3 Formal Verification Script

```tcl
# Jasper Gold / OneSpin example

# Read design
analyze -sv fifo.sv
elaborate -top fifo

# Set clocks and resets
clock clk
reset rst_n

# Prove properties
prove -all

# Generate counterexamples if any fail
visualize -violation -property no_push_when_full

# Coverage
get_property_info -all
```

---

## 15. Model Checking

### 15.1 State Space Exploration

**Concept:** Explore all reachable states

```
State Graph:
     IDLE
      │
    ┌─┴─┐
    │   │
   REQ GNT
    │   │
    └─┬─┘
      │
    DONE
```

**Formal checks:** Can bad state be reached?

### 15.2 Bounded Model Checking

```systemverilog
// Check property up to N cycles
property bounded_response;
  @(posedge clk) disable iff (!rst_n)
    req |-> ##[1:$] ack;  // Eventually ack (unbounded)
endproperty

// Formal will check up to bound (e.g., 100 cycles)
// If no violation found within bound, "inconclusive"
```

### 15.3 Abstraction

Reduce state space for complex designs:

```systemverilog
// Abstract away data, focus on control
module abstract_fifo (
  input  logic push,
  input  logic pop,
  output logic empty,
  output logic full
);
  // Ignore actual data storage
  // Model only state transitions

  typedef enum {EMPTY, PARTIAL, FULL} state_t;
  state_t state;

  always @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      state <= EMPTY;
    else case (state)
      EMPTY:   if (push) state <= PARTIAL;
      PARTIAL: if (push && !pop) state <= FULL;
               else if (pop && !push) state <= EMPTY;
      FULL:    if (pop) state <= PARTIAL;
    endcase
  end

  assign empty = (state == EMPTY);
  assign full = (state == FULL);

endmodule
```

---

## 16. Equivalence Checking

### 16.1 Combinational Equivalence

```
RTL Design          Gate-Level Netlist
┌─────────┐         ┌──────────────┐
│ RTL     │         │ AND, OR,     │
│ Assign  │  ===    │ NOT gates    │
│ Exprs   │         │              │
└─────────┘         └──────────────┘

Prove: Outputs identical for all inputs
```

**Example Script:**
```tcl
# Conformal / Formality

# Read golden (RTL)
read_verilog -golden rtl/design.v

# Read revised (Gates)
read_verilog -revised netlist/design.v

# Set top modules
set_top golden/design
set_top revised/design

# Map key points
match

# Verify
verify

# Report
report_unequal
```

### 16.2 Sequential Equivalence

```
More complex: Prove state machines equivalent

Requires:
- State mapping
- Retiming information
- Reset equivalence
```

---

## 17. Formal vs Simulation

### 17.1 When to Use Formal

**✓ Use Formal For:**
- Control-heavy designs (FSMs, arbiters)
- Complex corner cases
- Proving absence of bugs
- Protocol compliance

**✗ Don't Use Formal For:**
- Large datapaths (adders, multipliers)
- Full SoC verification
- Performance metrics

### 17.2 Hybrid Approach

```
Best Practice: Combine formal + simulation

Formal:
- Protocol checkers
- Control logic
- Safety properties

Simulation:
- System-level tests
- Performance tests
- Full-chip regression

Result: Higher confidence, faster debug
```

---

## 18. Coverage-Driven Verification

### 18.1 Coverage Closure

```
Coverage Goal: 100%
   ├─ Code Coverage: 98%+ (excluding unreachable code)
   ├─ Functional Coverage: 95%+ (all interesting scenarios)
   └─ Assertion Coverage: 100% (all properties checked)
```

### 18.2 Coverage-Driven Flow

```
1. Define coverage model (covergroups)
   ↓
2. Run random tests
   ↓
3. Measure coverage
   ↓
4. Identify holes
   ↓
5. Write directed tests for holes
   ↓
6. Repeat until goals met
```

### 18.3 Coverage Analysis

```systemverilog
// Coverage analysis task
task analyze_coverage();
  real code_cov, func_cov, total_cov;

  code_cov = $get_coverage();  // Code coverage
  func_cov = cg.get_coverage(); // Functional coverage

  $display("Code Coverage: %0.2f%%", code_cov);
  $display("Functional Coverage: %0.2f%%", func_cov);

  if (code_cov < 95.0)
    `uvm_warning("COV", "Code coverage below target")

  if (func_cov < 90.0)
    `uvm_warning("COV", "Functional coverage below target")
endtask
```

---

## 19. Verification Planning

### 19.1 Verification Plan Template

```
1. Feature List
   - List all DUT features
   - Prioritize (P0, P1, P2)

2. Test Plan
   - Tests per feature
   - Directed vs random
   - Coverage goals

3. Checkers
   - Assertions
   - Scoreboard checks
   - Protocol monitors

4. Coverage Model
   - Covergroups
   - Cross coverage
   - Targets

5. Schedule
   - Testbench development: 2 weeks
   - Directed tests: 1 week
   - Random testing: 2 weeks
   - Coverage closure: 2 weeks
   - Regression: 1 week
```

### 19.2 Verification Metrics

```
Metrics to Track:
- Code coverage (line, toggle, branch, FSM)
- Functional coverage
- Assertions (passed, failed, covered)
- Bugs found vs fixed
- Tests passing
- Simulation runtime
```

---

## 20. Industry Best Practices

### 20.1 Verification Commandments

1. **Plan Before You Code**
   - Write verification plan first
   - Define coverage model upfront

2. **Automate Everything**
   - Regression scripts
   - Coverage collection
   - Bug tracking

3. **Review Regularly**
   - Weekly coverage review
   - Bug triage meetings
   - Test plan updates

4. **Reuse Components**
   - Standard VIP (Verification IP)
   - UVM agents
   - Assertion libraries

5. **Trust But Verify**
   - Random + directed tests
   - Formal + simulation
   - Multiple checkers

### 20.2 Common Pitfalls

**❌ Mistakes to Avoid:**
1. No verification plan
2. Only directed tests (low coverage)
3. No functional coverage
4. No assertions
5. Late testbench development
6. Ignoring coverage holes
7. No code reviews
8. Poor documentation

**✓ Do Instead:**
1. Comprehensive verification plan
2. Mix of random and directed
3. Coverage-driven methodology
4. Assertions everywhere
5. Early testbench (concurrent with RTL)
6. Aggressive coverage closure
7. Peer reviews
8. Document all tests

### 20.3 Verification Checklist

**Before Tape-Out:**
- [ ] All features tested
- [ ] Code coverage >98%
- [ ] Functional coverage >95%
- [ ] All assertions passing
- [ ] No open P0/P1 bugs
- [ ] Regression 100% pass
- [ ] Formal proofs complete
- [ ] Emulation tests passed
- [ ] Reviews completed
- [ ] Documentation updated

---

## Conclusion

Verification is the most critical phase of chip development. Success requires:

**Technical Skills:**
- SystemVerilog/UVM expertise
- Understanding of formal methods
- Coverage analysis
- Debugging skills

**Methodology:**
- Coverage-driven verification
- Constrained random + directed tests
- Formal + simulation hybrid
- Continuous integration

**Best Practices:**
- Plan early
- Automate everything
- Review regularly
- Never compromise on quality

**Career Path:**
```
Junior Verification Engineer
  → Write testbenches, debug
  ↓
Mid-Level Verification Engineer
  → UVM environments, coverage closure
  ↓
Senior Verification Engineer
  → Verification planning, methodology
  ↓
Verification Architect/Manager
  → Team leadership, strategy
```

**Key Takeaway:** Verification is 70% of the project effort—invest accordingly!

---

*For related topics, see:*
- [Verilog_Mastery_Complete_Guide.md](Verilog_Mastery_Complete_Guide.md) - RTL design
- [ASIC_Design_Flow_Guide.md](ASIC_Design_Flow_Guide.md) - Full design flow
- [Communication_Protocols_Complete_Guide.md](Communication_Protocols_Complete_Guide.md) - Protocol verification

---
