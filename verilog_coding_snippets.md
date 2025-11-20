# Verilog Coding Practice Snippets

Quick reference for tasks, functions, blocking/non-blocking, and fork-join.

---

## Functions

### 1. Basic Function - Parity Calculator
```verilog
function logic calc_parity(input logic [7:0] data);
    return ^data;  // XOR reduction
endfunction

// Usage
logic [7:0] byte_val = 8'b10110011;
logic parity_bit = calc_parity(byte_val);
```

### 2. Function with Multiple Inputs
```verilog
function logic [7:0] add_with_carry(
    input logic [7:0] a, b,
    input logic cin
);
    return a + b + cin;
endfunction
```

### 3. Automatic Function (Reentrant)
```verilog
function automatic int factorial(input int n);
    if (n <= 1) return 1;
    else return n * factorial(n-1);
endfunction
```

### 4. Gray Code Converter
```verilog
function [3:0] bin2gray(input [3:0] bin);
    bin2gray = bin ^ (bin >> 1);
endfunction

function [3:0] gray2bin(input [3:0] gray);
    gray2bin[3] = gray[3];
    gray2bin[2] = gray2bin[3] ^ gray[2];
    gray2bin[1] = gray2bin[2] ^ gray[1];
    gray2bin[0] = gray2bin[1] ^ gray[0];
endfunction
```

### 5. Priority Encoder
```verilog
function [2:0] priority_encode(input [7:0] req);
    for (int i = 7; i >= 0; i--)
        if (req[i]) return i;
    return 0;
endfunction
```

---

## Tasks

### 6. Simple Display Task
```verilog
task display_transaction(input [7:0] addr, input [31:0] data);
    $display("@%0t: Write [0x%h] = 0x%h", $time, addr, data);
endtask

// Usage
display_transaction(8'h10, 32'hDEADBEEF);
```

### 7. Task with Timing Control
```verilog
task write_data(input [7:0] addr, input [31:0] data);
    @(posedge clk);
    addr_bus <= addr;
    data_bus <= data;
    we <= 1'b1;
    @(posedge clk);
    we <= 1'b0;
endtask
```

### 8. Task with Output
```verilog
task read_data(
    input  [7:0] addr,
    output [31:0] data
);
    @(posedge clk);
    addr_bus <= addr;
    re <= 1'b1;
    @(posedge clk);
    data = data_bus;
    re <= 1'b0;
endtask
```

### 9. Task with inout (Bidirectional)
```verilog
task bus_transaction(
    input  logic rd_wr,  // 1=read, 0=write
    input  [7:0] addr,
    inout  [31:0] data
);
    if (rd_wr) begin
        // Read
        @(posedge clk);
        data = memory[addr];
    end else begin
        // Write
        @(posedge clk);
        memory[addr] = data;
    end
endtask
```

### 10. Clock Generation Task
```verilog
task generate_clocks(input int num_cycles);
    repeat(num_cycles) begin
        #5 clk = ~clk;
    end
endtask
```

---

## Blocking vs Non-Blocking

### 11. Blocking (=) - Immediate Assignment
```verilog
always @(posedge clk) begin
    a = b;  // Execute immediately
    c = a;  // Uses NEW value of 'a'
end
// Result: a=b, c=b (both get same value)
```

### 12. Non-Blocking (<=) - Scheduled Assignment
```verilog
always @(posedge clk) begin
    a <= b;  // Schedule assignment
    c <= a;  // Uses OLD value of 'a'
end
// Result: a=b, c=old_a (swapped!)
```

### 13. Swap Using Blocking - WRONG!
```verilog
always @(posedge clk) begin
    a = b;  // a becomes 20
    b = a;  // b becomes 20 (FAIL - both are 20!)
end
```

### 14. Swap Using Non-Blocking - CORRECT!
```verilog
always @(posedge clk) begin
    a <= b;  // Schedule: a will be 20
    b <= a;  // Schedule: b will be 10
end
// After clock: a=20, b=10 (SUCCESS!)
```

### 15. Shift Register - Blocking vs Non-Blocking
```verilog
// WRONG - Using blocking
always @(posedge clk) begin
    sr[3] = sr[2];  // sr[3] gets sr[2]
    sr[2] = sr[1];  // sr[2] gets sr[1]
    sr[1] = sr[0];  // sr[1] gets sr[0]
    sr[0] = din;    // sr[0] gets din
    // Result: All bits get din value in one clock!
end

// CORRECT - Using non-blocking
always @(posedge clk) begin
    sr[3] <= sr[2];  // Schedule sr[3] = old sr[2]
    sr[2] <= sr[1];  // Schedule sr[2] = old sr[1]
    sr[1] <= sr[0];  // Schedule sr[1] = old sr[0]
    sr[0] <= din;    // Schedule sr[0] = din
    // Result: Proper shift - each bit moves one position
end
```

### 16. Counter - Always Non-Blocking
```verilog
always @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        count <= 4'b0;
    else
        count <= count + 1;  // Use <= for sequential logic
end
```

### 17. Combinational - Always Blocking
```verilog
always @(*) begin
    sum = a + b;     // Use = for combinational
    carry = a & b;
end
```

### 18. Mixed Example - Race Condition
```verilog
reg [3:0] count1, count2;

// Block 1
always @(posedge clk) begin
    count1 = count1 + 1;  // Blocking
end

// Block 2
always @(posedge clk) begin
    count2 = count1;  // RACE! Which value of count1?
end
```

### 19. Fixed - No Race Condition
```verilog
reg [3:0] count1, count2;

always @(posedge clk) begin
    count1 <= count1 + 1;  // Non-blocking
    count2 <= count1;      // Always uses old count1
end
```

### 20. Pipeline Register
```verilog
always @(posedge clk) begin
    stage1 <= din;
    stage2 <= stage1;
    stage3 <= stage2;
    dout <= stage3;
    // All use old values - proper pipeline
end
```

---

## Fork-Join

### 21. fork-join - Wait for ALL
```verilog
initial begin
    fork
        #10 $display("Thread 1 done");
        #20 $display("Thread 2 done");
        #15 $display("Thread 3 done");
    join
    $display("All threads complete");  // Prints at t=20
end
```

### 22. fork-join_any - Wait for FIRST
```verilog
initial begin
    fork
        #10 $display("Thread 1 done");
        #20 $display("Thread 2 done");
    join_any
    $display("First thread done");  // Prints at t=10
end
```

### 23. fork-join_none - Don't Wait
```verilog
initial begin
    fork
        #10 $display("Background task 1");
        #20 $display("Background task 2");
    join_none
    $display("Continue immediately");  // Prints at t=0
end
```

### 24. Parallel Stimulus
```verilog
initial begin
    fork
        // Thread 1: Generate write transactions
        repeat(5) begin
            write_data(addr++, data++);
        end

        // Thread 2: Generate read transactions
        repeat(5) begin
            read_data(addr++, rdata);
        end
    join
end
```

### 25. Timeout Pattern
```verilog
initial begin
    fork
        // Operation
        begin
            wait(done);
            $display("Operation completed");
        end

        // Timeout
        begin
            #1000;
            $display("TIMEOUT!");
            $finish;
        end
    join_any
    disable fork;  // Kill other thread
end
```

### 26. Parallel Port Writes
```verilog
task write_parallel;
    fork
        write_port_a(8'h10, 32'hAAAA);
        write_port_b(8'h20, 32'hBBBB);
        write_port_c(8'h30, 32'hCCCC);
    join
endtask
```

### 27. Race Condition Simulation
```verilog
initial begin
    a = 0;
    fork
        a = 10;  // Thread 1
        a = 20;  // Thread 2
    join
    $display("a = %d", a);  // Could be 10 or 20!
end
```

### 28. Multiple Monitors
```verilog
initial begin
    fork
        // Monitor 1: Check protocol
        forever @(posedge valid) check_protocol();

        // Monitor 2: Count transactions
        forever @(posedge done) trans_count++;

        // Monitor 3: Performance tracking
        forever @(posedge clk) measure_latency();
    join_none  // Run in background
end
```

### 29. Test with Timeout
```verilog
initial begin
    fork
        begin
            // Main test
            send_packet();
            wait(ack);
            $display("Test PASS");
        end

        begin
            // Watchdog
            #5000;
            $display("Test TIMEOUT - FAIL");
            $finish;
        end
    join_any
    disable fork;
end
```

### 30. Nested Fork-Join
```verilog
initial begin
    fork
        // Group 1
        begin
            fork
                #10 task_a();
                #20 task_b();
            join
        end

        // Group 2
        begin
            fork
                #15 task_c();
                #25 task_d();
            join
        end
    join  // Wait for both groups
end
```

---

## Quick Rules

**Functions:**
- Return a value
- No timing control (#, @, wait)
- Use in expressions
- Can be automatic (reentrant)

**Tasks:**
- Can have timing control
- Multiple outputs via output/inout
- Can call other tasks
- Used for sequences

**Blocking (=):**
- Use in combinational always @(*)
- Executes immediately
- Sequential execution within block

**Non-Blocking (<=):**
- Use in sequential always @(posedge clk)
- Schedules assignment
- All RHS evaluated first, then LHS updated
- Prevents race conditions

**Fork-Join:**
- `join` - Wait for ALL threads
- `join_any` - Wait for FIRST thread
- `join_none` - Don't wait, continue
- `disable fork` - Kill all child threads

---

*Quick reference for Verilog coding practice - focus on practical examples*
