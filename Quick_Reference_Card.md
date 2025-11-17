# SystemVerilog Functions and Tasks - Quick Reference Card

A concise reference guide for SystemVerilog functions and tasks syntax, patterns, and best practices.

---

## Quick Comparison

| Feature | Function | Task |
|---------|----------|------|
| **Return Value** | MUST return a value | NO return value |
| **Timing** | ZERO simulation time | CAN have delays |
| **Delays (#)** | ❌ NOT allowed | ✅ Allowed |
| **Events (@)** | ❌ NOT allowed | ✅ Allowed |
| **fork/join** | ❌ NOT allowed | ✅ Allowed |
| **Used in expressions** | ✅ Yes | ❌ No (statement only) |
| **Call another task** | ❌ No | ✅ Yes |
| **Call another function** | ✅ Yes | ✅ Yes |
| **Recursion** | ✅ Yes (with `automatic`) | ✅ Yes (with `automatic`) |

---

## Basic Syntax

### Function Declaration

```systemverilog
// Basic function
function return_type function_name(arguments);
    // body
    return value;
endfunction

// Void function (no return)
function void func_name(arguments);
    // body
endfunction

// Automatic (reentrant) function
function automatic return_type func_name(arguments);
    // body
endfunction

// With default return type (logic)
function func_name(arguments);
    return value;  // Returns 1-bit logic
endfunction
```

### Task Declaration

```systemverilog
// Basic task
task task_name(arguments);
    // body (can have timing)
endtask

// Automatic (reentrant) task
task automatic task_name(arguments);
    // body
endtask

// Task with early exit
task my_task(int value);
    if (value < 0) return;  // Early exit
    // process value
endtask
```

---

## Parameter Modes

### Syntax

```systemverilog
function/task name(
    input  type var1,    // Read-only (default)
    output type var2,    // Write-only, copied at end
    inout  type var3,    // Bidirectional
    ref    type var4     // Pass by reference
);
```

### Behavior

| Mode | Direction | Copy | Efficiency | Use Case |
|------|-----------|------|------------|----------|
| **input** | In | Yes | Slow for large data | Read-only parameters |
| **output** | Out | Yes (at end) | Medium | Return multiple values |
| **inout** | Both | Yes | Medium | Bidirectional data |
| **ref** | Both | No (reference) | Fast | Large arrays, classes |

### Examples

```systemverilog
// Input (read-only)
function int add(input int a, input int b);
    return a + b;
endfunction

// Output (write-only)
task divide(input int a, input int b, output int quotient, output int remainder);
    quotient = a / b;
    remainder = a % b;
endtask

// Ref (efficient for large data)
function void process_array(ref int arr[]);
    foreach(arr[i]) arr[i] *= 2;
endfunction
```

---

## Default Arguments

```systemverilog
// Syntax: parameter = default_value
function void config(
    string name,              // Required
    int timeout = 100,        // Optional (default = 100)
    bit debug = 0             // Optional (default = 0)
);
    $display("%s: timeout=%0d, debug=%b", name, timeout, debug);
endfunction

// Usage
config("test1");                  // Uses defaults
config("test2", 500);             // timeout=500, debug=0
config("test3", 200, 1);          // All specified
config("test4", .debug(1));       // Named argument, timeout=100
```

---

## Automatic vs Static

### Comparison

| Aspect | Static (default) | Automatic |
|--------|------------------|-----------|
| **Storage** | Single copy shared | New copy per call |
| **Lifetime** | Entire simulation | Duration of call |
| **Reentrant** | ❌ No | ✅ Yes |
| **Recursion** | ❌ Not safe | ✅ Safe |
| **Performance** | Slightly faster | Slightly slower |

### Examples

```systemverilog
// Static (default) - maintains state
function int counter_static();
    static int count = 0;  // Persists across calls
    return count++;
endfunction
// Calls return: 0, 1, 2, 3, ...

// Automatic - fresh each time
function automatic int counter_auto();
    int count = 0;  // New variable each call
    return count++;
endfunction
// Calls return: 0, 0, 0, 0, ...

// Recursion REQUIRES automatic
function automatic int factorial(int n);
    if (n <= 1) return 1;
    return n * factorial(n-1);  // Recursive call
endfunction
```

---

## Class Methods

```systemverilog
class MyClass;
    int data;

    // Constructor
    function new(int d = 0);
        data = d;
    endfunction

    // Regular method
    function int get_data();
        return data;
    endfunction

    // Void method
    function void set_data(int d);
        data = d;
    endfunction

    // Static method (class-level)
    static function int max(int a, int b);
        return (a > b) ? a : b;
    endfunction

    // Virtual method (for polymorphism)
    virtual function void display();
        $display("Data: %0d", data);
    endfunction

    // Task in class
    task wait_and_process();
        #10;
        data *= 2;
    endtask
endclass

// Usage
MyClass obj = new(5);
int val = obj.get_data();          // Instance method
int m = MyClass::max(10, 20);      // Static method (use ::)
```

---

## Virtual Functions (Polymorphism)

```systemverilog
// Base class
class Animal;
    virtual function void sound();
        $display("Generic sound");
    endfunction
endclass

// Derived class
class Dog extends Animal;
    virtual function void sound();
        $display("Woof!");
    endfunction
endclass

// Usage
Animal a = new Dog();  // Polymorphic handle
a.sound();             // Calls Dog::sound() - "Woof!"
```

### Pure Virtual (Abstract Class)

```systemverilog
virtual class Shape;
    pure virtual function real area();  // Must implement in derived
endclass

class Circle extends Shape;
    real radius;
    virtual function real area();
        return 3.14159 * radius * radius;
    endfunction
endclass
```

---

## Return Types

### Simple Types

```systemverilog
function int func1();              // Integer
function bit func2();              // Single bit
function real func3();             // Real number
function string func4();           // String
function void func5();             // No return (void)
```

### Complex Types

```systemverilog
function int[] func6();            // Dynamic array
function int[10] func7();          // Fixed array
function int[$] func8();           // Queue
function MyClass func9();          // Class object
```

---

## Fork/Join in Tasks

```systemverilog
// fork/join - wait for ALL threads
task demo_join();
    fork
        #10 $display("Thread 1");
        #20 $display("Thread 2");
    join
    $display("All done");  // Prints at time 20
endtask

// fork/join_any - wait for FIRST thread
task demo_join_any();
    fork
        #10 $display("Thread 1");
        #20 $display("Thread 2");
    join_any
    $display("First done");  // Prints at time 10
    disable fork;  // Kill remaining threads
endtask

// fork/join_none - don't wait
task demo_join_none();
    fork
        #10 $display("Thread 1");
        #20 $display("Thread 2");
    join_none
    $display("Continue immediately");  // Prints at time 0
endtask
```

---

## Common Patterns

### 1. Timeout Pattern

```systemverilog
task operation_with_timeout(int timeout_cycles);
    bit done = 0;
    fork
        begin
            do_operation();
            done = 1;
        end
        begin
            repeat(timeout_cycles) @(posedge clk);
        end
    join_any
    disable fork;

    if (!done)
        $error("Timeout!");
endtask
```

### 2. Retry Pattern

```systemverilog
task retry_operation(int max_retries, ref bit success);
    success = 0;
    for (int i = 0; i < max_retries; i++) begin
        if (try_operation()) begin
            success = 1;
            return;
        end
        #100;  // Wait before retry
    end
endtask
```

### 3. Function Chaining

```systemverilog
class Packet;
    function Packet set_addr(int a);
        addr = a;
        return this;  // Return self
    endfunction

    function Packet set_data(int d);
        data = d;
        return this;
    endfunction
endclass

// Usage
pkt.set_addr(0x1000).set_data(0xFF);  // Chained calls
```

### 4. Callback Pattern

```systemverilog
typedef function void callback_fn(int value);

class Manager;
    callback_fn callbacks[$];

    function void register_callback(callback_fn cb);
        callbacks.push_back(cb);
    endfunction

    function void trigger(int value);
        foreach(callbacks[i])
            callbacks[i](value);
    endfunction
endclass
```

### 5. Factory Pattern

```systemverilog
class Factory;
    static function BaseClass create(string type);
        case (type)
            "TypeA": return new ClassA();
            "TypeB": return new ClassB();
            default: return null;
        endcase
    endfunction
endclass
```

---

## DPI (C Interface)

### Import C Functions

```systemverilog
// Import C function to use in SV
import "DPI-C" function int c_add(int a, int b);
import "DPI-C" function void c_print(string msg);
import "DPI-C" context function void c_callback(int val);

// Usage in SV
int result = c_add(10, 20);
c_print("Hello from SV");
```

### Export SV Functions

```systemverilog
// Export SV function for C to call
export "DPI-C" function sv_function;

function void sv_function(int value);
    $display("Called from C with value: %0d", value);
endfunction
```

---

## Decision Flowcharts

### When to Use Function vs Task?

```
Need timing control? (#, @, wait)
├─ YES → Use TASK
└─ NO
   ├─ Need return value?
   │  ├─ YES → Use FUNCTION
   │  └─ NO → Use VOID FUNCTION or TASK
   └─ Used in expression? (a = func())
      ├─ YES → Use FUNCTION
      └─ NO → Either works
```

### When to Use automatic?

```
Concurrent calls? (fork/join)
├─ YES → Use AUTOMATIC
└─ NO
   ├─ Recursive?
   │  ├─ YES → Use AUTOMATIC
   │  └─ NO → Static OK
   └─ Need persistent state?
      ├─ YES → Use STATIC
      └─ NO → AUTOMATIC preferred
```

### When to Use ref vs input?

```
Large data? (arrays, classes)
├─ YES
│  ├─ Need to modify?
│  │  ├─ YES → Use REF
│  │  └─ NO → Use CONST REF (if supported) or REF
│  └─
└─ NO (small data: int, bit, etc.)
   ├─ Need to modify?
   │  ├─ YES → Use OUTPUT or INOUT
   │  └─ NO → Use INPUT
   └─
```

---

## Common Pitfalls & Solutions

### ❌ Pitfall: Non-automatic recursion

```systemverilog
// WRONG - will not work correctly
function int factorial(int n);
    if (n <= 1) return 1;
    return n * factorial(n-1);  // BUG!
endfunction

// CORRECT
function automatic int factorial(int n);
    if (n <= 1) return 1;
    return n * factorial(n-1);  // OK
endfunction
```

### ❌ Pitfall: Timing in function

```systemverilog
// WRONG - syntax error
function int wait_and_return();
    #10;  // ERROR: delay not allowed in function
    return 42;
endfunction

// CORRECT - use task
task wait_and_display(output int result);
    #10;  // OK in task
    result = 42;
endtask
```

### ❌ Pitfall: Task in expression

```systemverilog
// WRONG - tasks cannot be used in expressions
int x = my_task();  // ERROR

// CORRECT - use function for expressions
int x = my_function();  // OK
```

### ❌ Pitfall: Uninitialized variables

```systemverilog
// WRONG - max is uninitialized
function int find_max(int arr[]);
    int max;  // Could be X or garbage
    foreach(arr[i])
        if (arr[i] > max) max = arr[i];
    return max;
endfunction

// CORRECT - initialize
function int find_max(int arr[]);
    int max = arr[0];  // Or INT_MIN
    foreach(arr[i])
        if (arr[i] > max) max = arr[i];
    return max;
endfunction
```

### ❌ Pitfall: Race condition without semaphore

```systemverilog
// WRONG - race condition
int counter = 0;
task increment();
    counter++;  // Read-modify-write race!
endtask

// CORRECT - use semaphore
semaphore sem = new(1);
task increment();
    sem.get();
    counter++;
    sem.put();
endtask
```

---

## Best Practices

### ✅ DO:

- **Always specify return type explicitly**
  ```systemverilog
  function int add(...);  // Good
  // vs
  function add(...);      // Bad (defaults to logic)
  ```

- **Use `automatic` for recursive or concurrent calls**
  ```systemverilog
  function automatic int factorial(int n);
  ```

- **Use `ref` for large data structures**
  ```systemverilog
  function void process(ref int large_array[]);
  ```

- **Initialize all variables**
  ```systemverilog
  int count = 0;  // Good
  // vs
  int count;      // Bad (uninitialized)
  ```

- **Use meaningful names**
  ```systemverilog
  function int calculate_checksum(...);  // Good
  // vs
  function int calc(...);                // Bad
  ```

### ❌ DON'T:

- **Don't use timing in functions**
  ```systemverilog
  function int bad() #10 return 1; endfunction  // ERROR
  ```

- **Don't call tasks from functions**
  ```systemverilog
  function int bad() my_task(); return 1; endfunction  // ERROR
  ```

- **Don't forget `disable fork` after `join_any`**
  ```systemverilog
  fork ... join_any
  disable fork;  // Important! Kill other threads
  ```

- **Don't use non-automatic for recursion**
  ```systemverilog
  function int factorial(int n) ... // Wrong for recursion
  ```

---

## Syntax Cheat Sheet

### Function Syntax

```systemverilog
[virtual] function [automatic] [return_type] name (
    [direction] [type] param1 [= default],
    ...
);
    [local variables]
    [statements]
    return value;
endfunction [: name]
```

### Task Syntax

```systemverilog
task [automatic] name (
    [direction] [type] param1 [= default],
    ...
);
    [local variables]
    [statements with timing allowed]
    [return;]  // Early exit
endtask [: name]
```

### Class Method Syntax

```systemverilog
class ClassName;
    [local|protected] [static] [virtual] function ...
    [local|protected] [virtual] task ...
endclass
```

---

## Quick Example Templates

### Template 1: Basic Driver Task

```systemverilog
task automatic drive_transaction(transaction_t tr);
    @(posedge clk);
    vif.valid <= 1;
    vif.data <= tr.data;
    do @(posedge clk); while (!vif.ready);
    vif.valid <= 0;
endtask
```

### Template 2: Monitor Task

```systemverilog
task automatic monitor_bus();
    forever begin
        @(posedge clk);
        if (vif.valid && vif.ready) begin
            transaction_t tr = new();
            tr.data = vif.data;
            tr.addr = vif.addr;
            analysis_port.write(tr);
        end
    end
endtask
```

### Template 3: Scoreboard Function

```systemverilog
function bit compare_transactions(
    transaction_t expected,
    transaction_t actual
);
    if (expected.data != actual.data) begin
        $error("Data mismatch");
        return 0;
    end
    if (expected.addr != actual.addr) begin
        $error("Addr mismatch");
        return 0;
    end
    return 1;
endfunction
```

---

## Memory Aid: Function vs Task

**FUNCTION** = Fast, Returns value, Zero time
**TASK** = Timing allowed, Actions only

**Mnemonic**:
- **F**unctions are **F**ast (no time)
- **T**asks **T**ake **T**ime

---

**Print this page for quick reference during coding!**

---

**Version**: 1.0
**Last Updated**: 2025
**Pages**: 2 (when printed)
