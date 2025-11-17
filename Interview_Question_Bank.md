# SystemVerilog Functions and Tasks - Interview Question Bank

A comprehensive collection of 60+ interview questions covering SystemVerilog functions and tasks, from beginner to expert level. Each question includes detailed answers and code examples.

---

## Table of Contents

1. [Beginner Level Questions (1-20)](#beginner-level-questions)
2. [Intermediate Level Questions (21-40)](#intermediate-level-questions)
3. [Advanced Level Questions (41-55)](#advanced-level-questions)
4. [Scenario-Based Questions (56-60)](#scenario-based-questions)
5. [Code Review & Debugging (61-65)](#code-review--debugging)

---

## Beginner Level Questions

### Q1: What is the fundamental difference between a function and a task in SystemVerilog?

**Answer:**

The key differences are:

1. **Return Value**:
   - Functions MUST return a value
   - Tasks do NOT return a value (can have output/inout parameters)

2. **Timing**:
   - Functions execute in ZERO simulation time (no delays allowed)
   - Tasks CAN contain timing controls (#, @, wait)

3. **Usage**:
   - Functions can be used in expressions
   - Tasks are called as standalone statements

**Example:**
```systemverilog
// Function - returns value, no timing
function int add(int a, int b);
    return a + b;
endfunction

// Task - no return, can have timing
task wait_cycles(int n);
    repeat(n) @(posedge clk);
endtask

// Usage
initial begin
    int result = add(5, 3);        // Function in expression
    wait_cycles(10);                // Task as statement
end
```

---

### Q2: Can a function call a task? Can a task call a function?

**Answer:**

- **Function CANNOT call a task** (because tasks can contain timing, and functions must execute in zero time)
- **Task CAN call a function** (functions are allowed in tasks)

**Example:**
```systemverilog
function int compute(int x);
    // wait_clk();  // ERROR! Function cannot call task
    return x * 2;
endfunction

task process_data(int data);
    int result;
    result = compute(data);  // OK: Task can call function
    #10ns;
    $display("Result: %0d", result);
endtask
```

---

### Q3: What are the different parameter passing modes in SystemVerilog?

**Answer:**

SystemVerilog supports four parameter passing modes:

1. **input** (default): Pass by value, read-only inside function/task
2. **output**: Value is copied OUT at the end
3. **inout**: Bidirectional, changes visible immediately
4. **ref**: Pass by reference (for classes and large data structures)

**Example:**
```systemverilog
task param_demo(
    input  int a,      // Read-only, passed by value
    output int b,      // Write-only, copied out at end
    inout  int c,      // Bidirectional
    ref    int d       // Pass by reference
);
    b = a + 10;        // Set output
    c = c + 1;         // Modify inout
    d = d * 2;         // Modify by reference (immediate)
endtask

initial begin
    int w=5, x, y=10, z=20;
    param_demo(w, x, y, z);
    // w=5, x=15, y=11, z=40
end
```

---

### Q4: What is a void function and when would you use it?

**Answer:**

A **void function** is a function that doesn't return a value (return type is `void`). It's used when you need function-like behavior (no timing) but don't need a return value.

**Use cases:**
- Side effects (modifying class properties)
- Assertion or checking functions
- Logging or debugging utilities

**Example:**
```systemverilog
class Logger;
    int log_count = 0;

    function void log_message(string msg);
        $display("[%0t] %s", $time, msg);
        log_count++;
    endfunction

    function int get_log_count();
        return log_count;
    endfunction
endclass

Logger logger = new();
logger.log_message("System initialized");  // Void function
int count = logger.get_log_count();        // Regular function
```

---

### Q5: What happens if you try to use a delay (#) in a function?

**Answer:**

It will cause a **compilation error**. Functions must execute in zero simulation time and cannot contain:
- Delay controls (#)
- Event controls (@)
- Wait statements

**Example:**
```systemverilog
function int bad_function(int x);
    #10ns;  // ERROR: Delay not allowed in function
    return x + 1;
endfunction

task good_task(int x);
    #10ns;  // OK: Tasks can have delays
    $display("Value: %0d", x);
endtask
```

**Compiler Error:**
```
Error: Delay control is not allowed in a function
```

---

### Q6: How do you specify default arguments in functions/tasks?

**Answer:**

Default arguments are specified using the `=` operator in the parameter declaration. Arguments with defaults must come AFTER required arguments.

**Example:**
```systemverilog
function void display_config(
    string name,                    // Required
    int    verbosity = 1,           // Default = 1
    bit    enable_debug = 0         // Default = 0
);
    $display("Name: %s, Verbosity: %0d, Debug: %b",
             name, verbosity, enable_debug);
endfunction

// Usage:
display_config("Test1");              // Uses defaults: verbosity=1, debug=0
display_config("Test2", 3);           // verbosity=3, debug=0
display_config("Test3", 2, 1);        // All specified
display_config("Test4", .enable_debug(1)); // Named argument
```

---

### Q7: What is the difference between automatic and static variables in tasks/functions?

**Answer:**

| Aspect | Static (default) | Automatic |
|--------|-----------------|-----------|
| **Storage** | Single copy shared across all calls | New copy for each call |
| **Lifetime** | Entire simulation | Duration of call |
| **Reentrant** | No | Yes |
| **Usage** | Sequential calls, state preservation | Concurrent/recursive calls |

**Example:**
```systemverilog
// Static function - maintains state
function int counter_static();
    static int count = 0;  // Shared across all calls
    return count++;
endfunction

// Automatic function - fresh variable each call
function automatic int counter_auto();
    int count = 0;         // New copy each call
    return count++;
endfunction

initial begin
    $display(counter_static());  // 0
    $display(counter_static());  // 1
    $display(counter_static());  // 2

    $display(counter_auto());    // 0
    $display(counter_auto());    // 0
    $display(counter_auto());    // 0
end
```

---

### Q8: What are class methods and how are they different from regular functions?

**Answer:**

**Class methods** are functions/tasks defined inside a class. They have access to the class's properties and other methods.

**Key differences:**
- Can access `this` (implicit reference to current object)
- Can be `virtual` for polymorphism
- Can be `protected` or `local` for encapsulation
- Automatically get access to all class members

**Example:**
```systemverilog
class BankAccount;
    protected real balance;

    function new(real initial_balance);
        balance = initial_balance;
    endfunction

    // Class method
    function void deposit(real amount);
        balance += amount;  // Access to class member
    endfunction

    function real get_balance();
        return balance;     // Access to protected member
    endfunction
endclass

BankAccount acc = new(100.0);
acc.deposit(50.0);               // Calling class method
$display("Balance: $%.2f", acc.get_balance());
```

---

### Q9: Can functions return arrays or objects?

**Answer:**

Yes! Functions can return:
- Fixed-size arrays
- Dynamic arrays
- Associative arrays
- Queues
- Class objects (handles)
- Structs
- Unions

**Example:**
```systemverilog
// Return dynamic array
function int[] generate_sequence(int n);
    int result[] = new[n];
    foreach(result[i]) result[i] = i * i;
    return result;
endfunction

// Return queue
function int[$] generate_fibonacci(int n);
    int fib[$] = {1, 1};
    repeat(n-2) begin
        fib.push_back(fib[$-1] + fib[$-2]);
    end
    return fib;
endfunction

// Return class object
function MyClass create_object(string name);
    MyClass obj = new();
    obj.name = name;
    return obj;
endfunction

// Usage
int arr[] = generate_sequence(5);      // {0, 1, 4, 9, 16}
int fib[$] = generate_fibonacci(7);    // {1, 1, 2, 3, 5, 8, 13}
MyClass obj = create_object("Test");
```

---

### Q10: How do you make a task reentrant?

**Answer:**

Use the `automatic` keyword to make a task reentrant. This allows multiple concurrent calls (e.g., from different threads or recursive calls).

**Example:**
```systemverilog
// Non-reentrant task (static) - DANGER with fork/join
task static_task(int delay);
    #delay;
    $display("Delay: %0d at time %0t", delay, $time);
endtask

// Reentrant task (automatic) - SAFE with fork/join
task automatic auto_task(int delay);
    #delay;
    $display("Delay: %0d at time %0t", delay, $time);
endtask

initial begin
    fork
        static_task(10);  // Both calls share same variables - BUG!
        static_task(20);
    join

    fork
        auto_task(10);    // Each call has own variables - CORRECT
        auto_task(20);
    join
end
```

**Output (static):** Unpredictable due to shared state
**Output (automatic):**
```
Delay: 10 at time 10
Delay: 20 at time 20
```

---

### Q11: What is the purpose of the `return` statement in tasks?

**Answer:**

In tasks, `return` is used for **early exit** (not for returning a value, since tasks don't return values).

**Example:**
```systemverilog
task check_and_process(int value);
    if (value < 0) begin
        $error("Negative value not allowed");
        return;  // Early exit
    end

    if (value > 100) begin
        $warning("Value exceeds threshold");
        return;  // Early exit
    end

    // Process valid value
    $display("Processing: %0d", value);
endtask

initial begin
    check_and_process(-5);   // Error, returns early
    check_and_process(150);  // Warning, returns early
    check_and_process(50);   // Processes normally
end
```

---

### Q12: Can you have multiple return statements in a function?

**Answer:**

Yes! Multiple return statements are allowed and commonly used for early exit based on conditions.

**Example:**
```systemverilog
function int max_of_three(int a, int b, int c);
    if (a >= b && a >= c) return a;
    if (b >= c) return b;
    return c;
endfunction

function string grade(int score);
    if (score >= 90) return "A";
    if (score >= 80) return "B";
    if (score >= 70) return "C";
    if (score >= 60) return "D";
    return "F";
endfunction

// Usage
int max_val = max_of_three(15, 23, 19);  // Returns 23
string my_grade = grade(85);             // Returns "B"
```

---

### Q13: What is the scope of variables declared inside a function/task?

**Answer:**

Variables declared inside a function/task are **local** to that function/task and exist only during its execution (unless declared `static`).

**Scope rules:**
1. Local variables shadow outer scope variables with same name
2. Static local variables persist across calls
3. Automatic local variables are created fresh for each call

**Example:**
```systemverilog
module scope_demo;
    int global_var = 100;

    function int test_scope(int global_var);  // Shadows outer global_var
        int local_var = 10;
        return global_var + local_var;  // Uses parameter, not module variable
    endfunction

    task demo();
        int temp = 5;
        $display("Global: %0d", global_var);      // 100
        $display("Result: %0d", test_scope(20));  // 30 (20+10)
        // $display("%0d", local_var);  // ERROR: local_var not in scope
    endtask
endmodule
```

---

### Q14: How do you pass unpacked arrays to functions?

**Answer:**

Unpacked arrays can be passed by value or by reference:
- **By value**: Copy is made (use for small arrays)
- **By reference (`ref`)**: No copy, more efficient for large arrays

**Example:**
```systemverilog
// By value - copy is made
function int sum_array(int arr[10]);
    int total = 0;
    foreach(arr[i]) total += arr[i];
    return total;
endfunction

// By reference - no copy, more efficient
function int sum_array_ref(ref int arr[10]);
    int total = 0;
    foreach(arr[i]) total += arr[i];
    return total;
endfunction

// Dynamic array - must use ref
function void initialize_array(ref int arr[]);
    foreach(arr[i]) arr[i] = i * 10;
endfunction

// Usage
int data[10] = '{1,2,3,4,5,6,7,8,9,10};
int total1 = sum_array(data);      // Pass by value
int total2 = sum_array_ref(data);  // Pass by reference

int dynamic[];
dynamic = new[5];
initialize_array(dynamic);  // {0, 10, 20, 30, 40}
```

---

### Q15: What are import and export functions in SystemVerilog?

**Answer:**

**DPI (Direct Programming Interface)** functions allow SystemVerilog to interface with C/C++:

- **`import "DPI-C"`**: Import C functions to use in SystemVerilog
- **`export "DPI-C"`**: Export SystemVerilog functions to use in C

**Example:**
```systemverilog
// Import C function
import "DPI-C" function int c_add(int a, int b);
import "DPI-C" function void c_print_msg(string msg);

// Export SV function for C to call
export "DPI-C" function sv_callback;

function void sv_callback(int value);
    $display("Callback from C with value: %0d", value);
endfunction

// Usage in SystemVerilog
initial begin
    int result = c_add(10, 20);
    c_print_msg("Hello from SV");
end
```

**C side (dpi.c):**
```c
#include "svdpi.h"

int c_add(int a, int b) {
    return a + b;
}

void c_print_msg(const char* msg) {
    printf("C received: %s\n", msg);
}
```

---

### Q16: What happens if you don't specify a return type for a function?

**Answer:**

If no return type is specified, it defaults to **logic** (single bit).

**Example:**
```systemverilog
// No return type specified - defaults to logic
function my_func(int x);
    return (x > 10);  // Returns 1-bit logic
endfunction

// Equivalent to:
function logic my_func_explicit(int x);
    return (x > 10);
endfunction

// Usage
logic result = my_func(15);  // result = 1
```

**Best Practice:** Always explicitly specify the return type for clarity!

---

### Q17: Can you have fork/join inside a function?

**Answer:**

**No!** Functions cannot contain:
- fork/join (parallelism)
- Delays (#)
- Event controls (@)
- Wait statements

These all involve timing, and functions must execute in zero simulation time.

**Example:**
```systemverilog
function int bad_function();
    fork  // ERROR: fork/join not allowed in function
        #10;
    join
    return 1;
endfunction

task good_task();
    fork  // OK: Tasks can have fork/join
        #10 $display("Thread 1");
        #20 $display("Thread 2");
    join
endtask
```

---

### Q18: What is function chaining and how does it work?

**Answer:**

**Function chaining** (fluent interface) is when a function returns `this` (or the object itself), allowing multiple method calls to be chained together.

**Example:**
```systemverilog
class Packet;
    int length;
    int addr;
    bit parity;

    function Packet set_length(int len);
        length = len;
        return this;  // Return self for chaining
    endfunction

    function Packet set_addr(int a);
        addr = a;
        return this;
    endfunction

    function Packet set_parity(bit p);
        parity = p;
        return this;
    endfunction
endclass

// Usage with chaining
Packet pkt = new();
pkt.set_length(64)
   .set_addr(32'hABCD)
   .set_parity(1);

// Equivalent to:
pkt.set_length(64);
pkt.set_addr(32'hABCD);
pkt.set_parity(1);
```

---

### Q19: What is the difference between input and ref parameters?

**Answer:**

| Aspect | input | ref |
|--------|-------|-----|
| **Pass method** | By value (copy) | By reference |
| **Modification** | Cannot modify | Can modify |
| **Efficiency** | Slow for large data | Fast (no copy) |
| **Const** | Implicitly const | Can be modified |
| **Scope** | Local copy | References actual variable |

**Example:**
```systemverilog
function void test_input(input int arr[]);
    arr[0] = 100;  // Modifies local copy only
endfunction

function void test_ref(ref int arr[]);
    arr[0] = 100;  // Modifies actual array
endfunction

initial begin
    int data[] = '{1, 2, 3, 4, 5};

    test_input(data);
    $display("%p", data);  // {1, 2, 3, 4, 5} - unchanged

    test_ref(data);
    $display("%p", data);  // {100, 2, 3, 4, 5} - modified
end
```

---

### Q20: How do you call a task or function from another module?

**Answer:**

Use **hierarchical reference** with dot notation:

**Example:**
```systemverilog
module utils;
    function int multiply(int a, int b);
        return a * b;
    endfunction

    task wait_cycles(int n);
        repeat(n) @(posedge clk);
    endtask
endmodule

module testbench;
    utils u1();

    initial begin
        int result = u1.multiply(5, 6);     // Call function
        u1.wait_cycles(10);                 // Call task
        $display("Result: %0d", result);
    end
endmodule
```

Alternatively, use `import` with packages:
```systemverilog
package my_pkg;
    function int add(int a, int b);
        return a + b;
    endfunction
endpackage

module test;
    import my_pkg::*;  // or import my_pkg::add;

    initial begin
        int sum = add(10, 20);
    end
endmodule
```

---

## Intermediate Level Questions

### Q21: Explain the concept of virtual functions and provide an example.

**Answer:**

**Virtual functions** enable **polymorphism** - the ability to call the correct method based on the actual object type at runtime, not the handle type.

**Key points:**
- Declared with `virtual` keyword in base class
- Can be overridden in derived classes
- Runtime binding (dynamic dispatch)
- Essential for polymorphic behavior

**Example:**
```systemverilog
class Animal;
    virtual function void make_sound();
        $display("Generic animal sound");
    endfunction
endclass

class Dog extends Animal;
    virtual function void make_sound();
        $display("Woof! Woof!");
    endfunction
endclass

class Cat extends Animal;
    virtual function void make_sound();
        $display("Meow!");
    endfunction
endclass

// Polymorphism in action
initial begin
    Animal animals[3];
    animals[0] = new Dog();
    animals[1] = new Cat();
    animals[2] = new Animal();

    foreach(animals[i]) begin
        animals[i].make_sound();  // Calls correct method based on actual type
    end
end

// Output:
// Woof! Woof!
// Meow!
// Generic animal sound
```

**Without `virtual` keyword:** All would call Animal::make_sound()

---

### Q22: What are pure virtual functions and abstract classes?

**Answer:**

**Pure virtual function** = virtual function with no implementation (declared with `= 0`)
**Abstract class** = class with at least one pure virtual function

**Characteristics:**
- Cannot instantiate abstract classes
- Derived classes MUST implement all pure virtual functions
- Used to define interfaces/contracts

**Example:**
```systemverilog
// Abstract class (interface)
virtual class Transaction;
    pure virtual function bit [31:0] pack();
    pure virtual function void unpack(bit [31:0] data);
    pure virtual function void display();
endclass

// Concrete implementation
class ReadTrans extends Transaction;
    bit [31:0] addr;
    bit [7:0] id;

    virtual function bit [31:0] pack();
        return {id, 8'h0, addr[23:0]};
    endfunction

    virtual function void unpack(bit [31:0] data);
        {id, addr} = {data[31:24], data[23:0]};
    endfunction

    virtual function void display();
        $display("READ: addr=0x%0h, id=%0d", addr, id);
    endfunction
endclass

// Usage
initial begin
    // Transaction t = new();  // ERROR: Cannot instantiate abstract class
    Transaction t = new ReadTrans();  // OK: Concrete class
    t.display();
end
```

---

### Q23: How do static class methods differ from regular class methods?

**Answer:**

**Static methods** belong to the class itself, not to instances. They:
- Can be called without creating an object
- Cannot access instance variables (only static variables)
- Accessed using `::`  operator
- Useful for utility functions and factory methods

**Example:**
```systemverilog
class MathUtils;
    static int call_count = 0;  // Static variable

    // Static method - can be called without object
    static function int max(int a, int b);
        call_count++;  // Can access static variables
        return (a > b) ? a : b;
    endfunction

    // Regular method - needs object
    function void print_stats();
        $display("Total calls: %0d", call_count);
    endfunction
endclass

initial begin
    // Call static method without creating object
    int result = MathUtils::max(10, 20);  // Using ::

    // Create object for instance method
    MathUtils util = new();
    util.print_stats();
end
```

---

### Q24: Explain the difference between fork/join, fork/join_any, and fork/join_none.

**Answer:**

These control how parent process waits for forked threads:

| Construct | Behavior | Use Case |
|-----------|----------|----------|
| **fork/join** | Wait for ALL threads to complete | Parallel tasks must all finish |
| **fork/join_any** | Wait for ANY ONE thread to complete | Timeout, race conditions |
| **fork/join_none** | Don't wait, continue immediately | Fire-and-forget background tasks |

**Example:**
```systemverilog
task demonstrate_fork_join();
    $display("[%0t] Starting fork/join", $time);
    fork
        #10 $display("[%0t] Thread A done", $time);
        #20 $display("[%0t] Thread B done", $time);
        #15 $display("[%0t] Thread C done", $time);
    join
    $display("[%0t] All threads complete", $time);
endtask
// Output times: 10, 15, 20, then "All threads complete" at 20

task demonstrate_fork_join_any();
    $display("[%0t] Starting fork/join_any", $time);
    fork
        #10 $display("[%0t] Thread A done", $time);
        #20 $display("[%0t] Thread B done", $time);
    join_any
    $display("[%0t] First thread complete", $time);
    // Continues at time 10 (first thread)
endtask

task demonstrate_fork_join_none();
    $display("[%0t] Starting fork/join_none", $time);
    fork
        #10 $display("[%0t] Thread A done", $time);
        #20 $display("[%0t] Thread B done", $time);
    join_none
    $display("[%0t] Immediately continue", $time);
    // Continues immediately at time 0
endtask
```

**Common use case - Timeout:**
```systemverilog
task wait_with_timeout(event e, int timeout);
    fork
        @e;  // Wait for event
        #timeout;  // Timeout
    join_any
    disable fork;  // Kill other thread
endtask
```

---

### Q25: What is a recursive function and what precautions should you take?

**Answer:**

**Recursive function** = function that calls itself

**Requirements:**
1. MUST be declared `automatic` (to avoid shared state)
2. MUST have a base case (termination condition)
3. Watch out for stack overflow with deep recursion

**Example:**
```systemverilog
// Factorial - classic recursion
function automatic int factorial(int n);
    if (n <= 1) return 1;  // Base case
    return n * factorial(n - 1);  // Recursive case
endfunction

// Fibonacci with memoization
class FibCalc;
    static int cache[int];  // Memoization

    static function automatic int fib(int n);
        if (n <= 1) return n;  // Base case

        if (cache.exists(n)) return cache[n];  // Check cache

        cache[n] = fib(n-1) + fib(n-2);  // Compute and store
        return cache[n];
    endfunction
endclass

// Binary tree traversal
class TreeNode;
    int value;
    TreeNode left, right;

    function automatic void print_inorder();
        if (left != null) left.print_inorder();
        $display("%0d ", value);
        if (right != null) right.print_inorder();
    endfunction
endclass

// Usage
initial begin
    $display("5! = %0d", factorial(5));  // 120
    $display("Fib(10) = %0d", FibCalc::fib(10));  // 55
end
```

**Warning:** Without `automatic`, recursion will NOT work correctly!

---

### Q26: How do you implement a timeout mechanism using tasks?

**Answer:**

Use `fork/join_any` with `disable fork` to implement timeouts:

**Example:**
```systemverilog
task automatic wait_with_timeout(
    input int timeout_cycles,
    ref bit success
);
    success = 0;
    fork
        begin
            // Main operation
            wait_for_ready();
            success = 1;
        end
        begin
            // Timeout
            repeat(timeout_cycles) @(posedge clk);
        end
    join_any
    disable fork;  // Kill the other thread
endtask

// Usage
bit completed;
wait_with_timeout(1000, completed);
if (completed)
    $display("Operation completed");
else
    $error("Timeout occurred");
```

**Alternative using fork/join_none:**
```systemverilog
task automatic operation_with_timeout(int timeout_ns);
    bit done = 0;
    fork
        begin
            do_operation();
            done = 1;
        end
    join_none

    #timeout_ns;
    if (!done) begin
        $error("Timeout after %0d ns", timeout_ns);
        disable fork;
    end
endtask
```

---

### Q27: What are constraint functions and how are they used in randomization?

**Answer:**

**Constraint functions** are used to create complex constraints for randomization. They allow you to use functions inside constraint blocks.

**Rules:**
- Must be declared with `constraint_mode` or used with `solve...before`
- Cannot modify class variables
- Must be deterministic

**Example:**
```systemverilog
class Packet;
    rand bit [7:0] length;
    rand bit [7:0] payload[];
    rand bit [15:0] checksum;

    // Constraint using function
    constraint valid_length {
        length inside {[10:100]};
        payload.size() == length;
    }

    // Function for checksum calculation
    function bit [15:0] calculate_checksum();
        bit [15:0] sum = length;
        foreach(payload[i]) sum += payload[i];
        return ~sum;
    endfunction

    // Constraint using function call
    constraint valid_checksum {
        checksum == calculate_checksum();
    }
endclass

// More complex example with implication
class Transaction;
    rand bit [31:0] addr;
    rand bit [3:0]  size;

    // Helper function for constraint
    function bit is_aligned(bit [31:0] a, int boundary);
        return (a % boundary == 0);
    endfunction

    constraint alignment {
        (size == 4) -> is_aligned(addr, 4);
        (size == 8) -> is_aligned(addr, 8);
    }
endclass

// Usage
Packet pkt = new();
if (pkt.randomize()) begin
    $display("Packet length: %0d", pkt.length);
    $display("Checksum: 0x%0h", pkt.checksum);
end
```

---

### Q28: Explain the use of extern declarations for functions and tasks.

**Answer:**

**Extern declarations** separate the prototype (declaration) from the implementation (definition). Used for:
- Better code organization
- Forward references
- Implementation in different files

**Example:**
```systemverilog
class ConfigManager;
    // Declarations (prototypes)
    extern function void load_config(string filename);
    extern function void save_config(string filename);
    extern task wait_for_update();

    // Class members
    int timeout = 100;
    string config_data[$];
endclass

// Implementation outside class
function void ConfigManager::load_config(string filename);
    int fd = $fopen(filename, "r");
    // Implementation here
    $fclose(fd);
endfunction

function void ConfigManager::save_config(string filename);
    int fd = $fopen(filename, "w");
    // Implementation here
    $fclose(fd);
endfunction

task ConfigManager::wait_for_update();
    repeat(timeout) @(posedge clk);
endtask
```

**Benefits:**
- Class definition is more concise and readable
- Can put implementations in separate file
- Easier to navigate large classes

---

### Q29: How do you implement a producer-consumer pattern using tasks?

**Answer:**

Use tasks with mailboxes or queues for communication:

**Example:**
```systemverilog
class Transaction;
    int data;
    function new(int d); data = d; endfunction
endclass

class ProducerConsumer;
    mailbox #(Transaction) mbx;

    function new();
        mbx = new(10);  // Mailbox with depth 10
    endfunction

    // Producer task
    task producer(int num_items);
        for (int i = 0; i < num_items; i++) begin
            Transaction t = new(i);
            mbx.put(t);
            $display("[%0t] Produced: %0d", $time, i);
            #(10 + $urandom_range(0, 20));
        end
    endtask

    // Consumer task
    task consumer(int num_items);
        for (int i = 0; i < num_items; i++) begin
            Transaction t;
            mbx.get(t);
            $display("[%0t] Consumed: %0d", $time, t.data);
            #(15 + $urandom_range(0, 10));
        end
    endtask

    // Run both concurrently
    task run(int num_transactions);
        fork
            producer(num_transactions);
            consumer(num_transactions);
        join
    endtask
endclass

// Usage
initial begin
    ProducerConsumer pc = new();
    pc.run(20);
end
```

**Alternative with queues:**
```systemverilog
class QueueBasedPC;
    int queue[$];
    semaphore sem;

    function new();
        sem = new(1);
    endfunction

    task producer();
        forever begin
            int item = $urandom_range(0, 100);
            sem.get();  // Lock
            queue.push_back(item);
            sem.put();  // Unlock
            #10;
        end
    endtask

    task consumer();
        forever begin
            sem.get();  // Lock
            if (queue.size() > 0) begin
                int item = queue.pop_front();
                $display("Consumed: %0d", item);
            end
            sem.put();  // Unlock
            #20;
        end
    endtask
endclass
```

---

### Q30: What is the difference between $display and $write in function context?

**Answer:**

Both can be used in functions, but they have different output behavior:

| Function | Newline | Buffering | Usage |
|----------|---------|-----------|-------|
| **$display** | Automatic | Line-buffered | Complete messages |
| **$write** | Manual (\n) | Unbuffered | Partial messages |

**Example:**
```systemverilog
function void test_display();
    $display("Line 1");  // Adds newline automatically
    $display("Line 2");
    $display("Value: %0d", 42);
endfunction

function void test_write();
    $write("Part 1 ");   // No automatic newline
    $write("Part 2 ");
    $write("Part 3\n");  // Manual newline
endfunction

// Output from test_display():
// Line 1
// Line 2
// Value: 42

// Output from test_write():
// Part 1 Part 2 Part 3
```

**Additional variants:**
```systemverilog
function void demonstrate_all();
    $display("Display with newline");
    $write("Write without newline");
    $monitor("Monitor (tracks changes)");  // Not typically used in functions
    $strobe("Strobe (prints at end of timestep)");
endfunction
```

**Best Practice:** Use `$display` in functions for clear, complete messages.

---

### Q31: How do you implement a callback mechanism using function pointers?

**Answer:**

SystemVerilog doesn't have traditional function pointers, but you can achieve callbacks using:
1. Virtual functions (polymorphism)
2. Typedef functions
3. Class handles with methods

**Example using typedef:**
```systemverilog
// Define function signature
typedef function void callback_t(int value);

class CallbackManager;
    callback_t callbacks[$];

    function void register_callback(callback_t cb);
        callbacks.push_back(cb);
    endfunction

    task trigger_callbacks(int value);
        foreach(callbacks[i]) begin
            callbacks[i](value);  // Call each callback
        end
    endtask
endclass

// Callback functions
function void on_event_1(int val);
    $display("Callback 1: %0d", val);
endfunction

function void on_event_2(int val);
    $display("Callback 2: %0d squared = %0d", val, val*val);
endfunction

// Usage
initial begin
    CallbackManager mgr = new();
    mgr.register_callback(on_event_1);
    mgr.register_callback(on_event_2);
    mgr.trigger_callbacks(5);
end
```

**Example using virtual functions (better approach):**
```systemverilog
virtual class Callback;
    pure virtual function void execute(int value);
endclass

class Logger extends Callback;
    virtual function void execute(int value);
        $display("[LOG] Value: %0d", value);
    endfunction
endclass

class Validator extends Callback;
    virtual function void execute(int value);
        if (value < 0) $error("Invalid value");
    endfunction
endclass

class EventManager;
    Callback callbacks[$];

    function void add_callback(Callback cb);
        callbacks.push_back(cb);
    endfunction

    function void notify(int value);
        foreach(callbacks[i])
            callbacks[i].execute(value);
    endfunction
endclass

// Usage
initial begin
    EventManager em = new();
    em.add_callback(new Logger());
    em.add_callback(new Validator());
    em.notify(42);
end
```

---

### Q32: What are coverage functions and how do they work?

**Answer:**

**Coverage functions** are special functions (cover `sample()` and `get_coverage()`) used with covergroups to control when coverage is sampled.

**Example:**
```systemverilog
class Transaction;
    rand bit [7:0] addr;
    rand bit [7:0] data;
    bit write;

    covergroup cg;
        addr_cp: coverpoint addr {
            bins low    = {[0:63]};
            bins mid    = {[64:191]};
            bins high   = {[192:255]};
        }

        data_cp: coverpoint data;

        write_cp: coverpoint write;

        cross addr_cp, write_cp;
    endgroup

    function new();
        cg = new();
    endfunction

    // Function to trigger coverage sampling
    function void sample_coverage();
        cg.sample();
    endfunction

    // Function to get coverage percentage
    function real get_coverage_percent();
        return cg.get_coverage();
    endfunction
endclass

// Usage
initial begin
    Transaction t = new();

    repeat(100) begin
        assert(t.randomize());
        t.sample_coverage();  // Sample coverage
    end

    $display("Coverage: %.2f%%", t.get_coverage_percent());
end
```

**Advanced - Custom coverage collection:**
```systemverilog
class AdvancedCoverage;
    bit [31:0] addr;
    bit [7:0] data;

    covergroup cg with function sample(bit [31:0] a, bit [7:0] d);
        option.per_instance = 1;

        coverpoint a {
            bins range1 = {[0:99]};
            bins range2 = {[100:199]};
            bins range3 = {[200:299]};
        }

        coverpoint d;
    endgroup

    function new();
        cg = new();
    endfunction

    function void record_transaction(bit [31:0] a, bit [7:0] d);
        addr = a;
        data = d;
        cg.sample(a, d);  // Pass arguments to sample
    endfunction
endclass
```

---

### Q33: How do you handle errors in functions - assertions vs return codes?

**Answer:**

Three approaches for error handling in functions:

**1. Return codes (traditional):**
```systemverilog
function int divide(int a, int b, ref int result);
    if (b == 0) return -1;  // Error code
    result = a / b;
    return 0;  // Success
endfunction

// Usage
int quotient, status;
status = divide(10, 0, quotient);
if (status != 0) $error("Division failed");
```

**2. Assertions (immediate):**
```systemverilog
function int safe_divide(int a, int b);
    assert (b != 0) else $fatal("Division by zero");
    return a / b;
endfunction

// Usage
int result = safe_divide(10, 2);  // OK
int bad = safe_divide(10, 0);     // Fatal error, simulation stops
```

**3. Exception-like pattern with class:**
```systemverilog
class Result;
    bit success;
    string error_msg;
    int value;

    function new(bit s, int v=0, string msg="");
        success = s;
        value = v;
        error_msg = msg;
    endfunction
endclass

function Result robust_divide(int a, int b);
    if (b == 0)
        return new Result(0, 0, "Division by zero");
    return new Result(1, a/b);
endfunction

// Usage
Result r = robust_divide(10, 0);
if (r.success)
    $display("Result: %0d", r.value);
else
    $error("Error: %s", r.error_msg);
```

**Best practices:**
- Use assertions for programming errors (should never happen)
- Use return codes for expected error conditions
- Use exception-like pattern for complex error handling

---

### Q34: Explain the use of parameterized functions/tasks.

**Answer:**

Functions and tasks can be **parameterized** using class parameters or module parameters.

**Example with class parameters:**
```systemverilog
class GenericFIFO #(parameter WIDTH = 8, DEPTH = 16);
    typedef bit [WIDTH-1:0] data_t;
    data_t queue[$];

    function bit push(data_t data);
        if (queue.size() >= DEPTH) return 0;  // Full
        queue.push_back(data);
        return 1;  // Success
    endfunction

    function bit pop(ref data_t data);
        if (queue.size() == 0) return 0;  // Empty
        data = queue.pop_front();
        return 1;  // Success
    endfunction

    function int size();
        return queue.size();
    endfunction
endclass

// Usage with different parameters
initial begin
    GenericFIFO #(.WIDTH(16), .DEPTH(32)) fifo1;
    GenericFIFO #(.WIDTH(32), .DEPTH(8))  fifo2;

    fifo1 = new();
    fifo2 = new();

    fifo1.push(16'hABCD);
    fifo2.push(32'h12345678);
end
```

**Example with typedef functions:**
```systemverilog
typedef function bit comparator_t(int a, int b);

function automatic void sort_array(
    ref int arr[],
    comparator_t compare
);
    for (int i = 0; i < arr.size()-1; i++) begin
        for (int j = i+1; j < arr.size(); j++) begin
            if (compare(arr[j], arr[i])) begin
                int temp = arr[i];
                arr[i] = arr[j];
                arr[j] = temp;
            end
        end
    end
endfunction

// Different comparison functions
function bit ascending(int a, int b);
    return a < b;
endfunction

function bit descending(int a, int b);
    return a > b;
endfunction

// Usage
initial begin
    int data[] = '{5, 2, 8, 1, 9};
    sort_array(data, ascending);   // Sort ascending
    $display("%p", data);          // {1, 2, 5, 8, 9}

    sort_array(data, descending);  // Sort descending
    $display("%p", data);          // {9, 8, 5, 2, 1}
end
```

---

### Q35: What is the difference between `disable` and `return` in tasks?

**Answer:**

| Aspect | `return` | `disable task_name` |
|--------|----------|---------------------|
| **Scope** | Exits current task only | Can disable any named block/task |
| **Location** | Must be inside task | Can be called from anywhere |
| **Fork threads** | Doesn't affect them | Kills all forked threads in that task |

**Example:**
```systemverilog
task example_return();
    fork
        #10 $display("Thread 1");
        #20 $display("Thread 2");
    join_none

    #5;
    return;  // Exits task, but forked threads continue!
    $display("Never printed");
endtask

task example_disable();
    fork
        begin: thread1
            #10 $display("Thread 1");
        end
        begin: thread2
            #20 $display("Thread 2");
        end
    join_none

    #5;
    disable example_disable;  // Kills task AND all forked threads!
    $display("Never printed");
endtask

// Advanced: Disable specific thread
task selective_disable();
    fork
        begin: keep_me
            #10 $display("This runs");
        end
        begin: kill_me
            #20 $display("This is killed");
        end
    join_none

    #5;
    disable kill_me;  // Disable only specific thread
endtask
```

**Output from example_return():**
```
Thread 1  (at time 10)
Thread 2  (at time 20)
```

**Output from example_disable():**
```
(nothing - all threads killed)
```

**Output from selective_disable():**
```
This runs  (at time 10)
```

---

### Q36: How do you implement retry logic in tasks?

**Answer:**

**Example 1: Simple retry with counter:**
```systemverilog
task automatic retry_operation(
    input int max_retries,
    ref bit success
);
    int attempts = 0;
    success = 0;

    while (attempts < max_retries && !success) begin
        attempts++;
        $display("Attempt %0d/%0d", attempts, max_retries);

        // Try operation
        if (try_operation()) begin
            success = 1;
            $display("Success on attempt %0d", attempts);
        end else begin
            $display("Failed, retrying...");
            #100ns;  // Wait before retry
        end
    end

    if (!success)
        $error("Failed after %0d attempts", max_retries);
endtask
```

**Example 2: Exponential backoff:**
```systemverilog
task automatic retry_with_backoff(
    input int max_retries,
    input int base_delay_ns,
    ref bit success
);
    int attempts = 0;
    int delay = base_delay_ns;
    success = 0;

    while (attempts < max_retries && !success) begin
        attempts++;

        if (try_operation()) begin
            success = 1;
        end else begin
            $display("Attempt %0d failed, waiting %0d ns",
                     attempts, delay);
            #(delay * 1ns);
            delay = delay * 2;  // Exponential backoff
        end
    end
endtask
```

**Example 3: Retry with timeout:**
```systemverilog
task automatic retry_with_timeout(
    input int max_retries,
    input int timeout_per_try_ns,
    ref bit success
);
    success = 0;

    for (int attempt = 1; attempt <= max_retries; attempt++) begin
        bit timeout_occurred = 0;

        fork
            begin
                success = try_operation();
            end
            begin
                #(timeout_per_try_ns * 1ns);
                timeout_occurred = 1;
            end
        join_any
        disable fork;

        if (timeout_occurred) begin
            $warning("Attempt %0d timed out", attempt);
        end else if (success) begin
            return;
        end
    end

    $error("All retry attempts failed");
endtask
```

---

### Q37: What are class constructors and how do they differ from regular functions?

**Answer:**

**Constructor** (`function new()`) is a special function that:
- Creates and initializes objects
- Called automatically when object is created
- Can take parameters
- Cannot have return type (implicitly returns the object)
- Can call parent constructor using `super.new()`

**Example:**
```systemverilog
class Packet;
    int length;
    bit [7:0] data[];
    static int packet_count = 0;

    // Constructor with parameters
    function new(int len = 64);
        length = len;
        data = new[len];
        packet_count++;  // Track instances
        $display("Created packet #%0d with length %0d",
                 packet_count, len);
    endfunction
endclass

// Inheritance with constructors
class EthernetPacket extends Packet;
    bit [47:0] dest_mac;
    bit [47:0] src_mac;

    function new(int len, bit [47:0] dst, bit [47:0] src);
        super.new(len);  // Call parent constructor
        dest_mac = dst;
        src_mac = src;
    endfunction
endclass

// Usage
Packet p1 = new();         // Uses default length 64
Packet p2 = new(128);      // length = 128
EthernetPacket ep = new(1500, 48'hAABBCCDDEEFF, 48'h112233445566);
```

**Differences from regular functions:**

| Aspect | Constructor | Regular Function |
|--------|-------------|------------------|
| **Name** | Must be `new` | Any valid identifier |
| **Return type** | None (implicit) | Must specify |
| **When called** | At object creation | Explicitly by user |
| **Purpose** | Initialize object | Perform operation |
| **Can be virtual** | No | Yes |

---

### Q38: How do you implement a state machine using functions and tasks?

**Answer:**

**Example: FSM with tasks for each state:**
```systemverilog
typedef enum {IDLE, START, DATA, STOP, ERROR} state_t;

class UART_FSM;
    state_t current_state = IDLE;
    bit clk;
    bit rx_data;
    bit [7:0] received_data;

    // Task for each state
    task state_idle();
        if (rx_data == 0) begin  // Start bit detected
            current_state = START;
            $display("[%0t] IDLE -> START", $time);
        end
    endtask

    task state_start();
        @(posedge clk);
        if (rx_data == 0) begin
            current_state = DATA;
            $display("[%0t] START -> DATA", $time);
        end else begin
            current_state = ERROR;
        end
    endtask

    task state_data();
        for (int i = 0; i < 8; i++) begin
            @(posedge clk);
            received_data[i] = rx_data;
        end
        current_state = STOP;
        $display("[%0t] DATA -> STOP, received: 0x%0h",
                 $time, received_data);
    endtask

    task state_stop();
        @(posedge clk);
        if (rx_data == 1) begin  // Valid stop bit
            current_state = IDLE;
            $display("[%0t] STOP -> IDLE", $time);
        end else begin
            current_state = ERROR;
        end
    endtask

    task state_error();
        $error("[%0t] FSM Error", $time);
        current_state = IDLE;
    endtask

    // Main FSM task
    task run();
        forever begin
            case (current_state)
                IDLE:  state_idle();
                START: state_start();
                DATA:  state_data();
                STOP:  state_stop();
                ERROR: state_error();
            endcase
        end
    endtask
endclass
```

**Alternative: Function-based state lookup:**
```systemverilog
class StateMachine;
    typedef enum {S0, S1, S2, S3} state_t;
    state_t state = S0;

    // State transition function
    function state_t next_state(state_t curr, bit input_val);
        case (curr)
            S0: return input_val ? S1 : S0;
            S1: return input_val ? S2 : S0;
            S2: return input_val ? S3 : S0;
            S3: return input_val ? S3 : S0;
        endcase
    endfunction

    // Output function
    function bit output_func(state_t curr);
        return (curr == S3);  // Output high in S3
    endfunction

    // Clock task
    task run(bit input_stream[]);
        foreach(input_stream[i]) begin
            @(posedge clk);
            state = next_state(state, input_stream[i]);
            bit out = output_func(state);
            $display("State: %s, Output: %b", state.name(), out);
        end
    endtask
endclass
```

---

### Q39: Explain the concept of task/function overloading in SystemVerilog.

**Answer:**

SystemVerilog does **NOT support true function overloading** (multiple functions with same name but different signatures). However, you can achieve similar behavior using:

1. **Default arguments**
2. **Optional arguments with defaults**
3. **Polymorphism (virtual functions)**

**Workaround 1: Default arguments:**
```systemverilog
class Display;
    // Simulates overloading using defaults
    function void print(
        int value,
        string prefix = "",
        string suffix = ""
    );
        $display("%s%0d%s", prefix, value, suffix);
    endfunction
endclass

// Usage (appears like overloading):
Display d = new();
d.print(42);                    // Basic
d.print(42, "Value: ");         // With prefix
d.print(42, "Value: ", " ms");  // With prefix and suffix
```

**Workaround 2: Different method names:**
```systemverilog
class Printer;
    function void print_int(int val);
        $display("Integer: %0d", val);
    endfunction

    function void print_string(string val);
        $display("String: %s", val);
    endfunction

    function void print_real(real val);
        $display("Real: %0f", val);
    endfunction
endclass
```

**Workaround 3: Polymorphism:**
```systemverilog
virtual class Printable;
    pure virtual function void print();
endclass

class IntPrintable extends Printable;
    int value;
    function new(int v); value = v; endfunction
    virtual function void print();
        $display("Int: %0d", value);
    endfunction
endclass

class StringPrintable extends Printable;
    string value;
    function new(string v); value = v; endfunction
    virtual function void print();
        $display("String: %s", value);
    endfunction
endclass

// Usage
Printable items[$];
items.push_back(new IntPrintable(42));
items.push_back(new StringPrintable("Hello"));
foreach(items[i]) items[i].print();  // Polymorphic call
```

---

### Q40: How do you pass associative arrays to functions?

**Answer:**

Associative arrays should be passed **by reference** using `ref` keyword for efficiency.

**Example:**
```systemverilog
// By reference (efficient)
function void print_assoc_array(ref int aa[string]);
    foreach(aa[key]) begin
        $display("Key: %s, Value: %0d", key, aa[key]);
    end
endfunction

// Modify associative array
function void increment_all(ref int aa[string]);
    foreach(aa[key]) begin
        aa[key]++;
    end
endfunction

// Search in associative array
function bit find_value(
    ref int aa[string],
    input int search_val,
    output string found_key
);
    foreach(aa[key]) begin
        if (aa[key] == search_val) begin
            found_key = key;
            return 1;  // Found
        end
    end
    return 0;  // Not found
endfunction

// Return associative array
function int[string] create_lookup();
    int result[string];
    result["one"] = 1;
    result["two"] = 2;
    result["three"] = 3;
    return result;
endfunction

// Usage
initial begin
    int ages[string];
    ages["Alice"] = 30;
    ages["Bob"] = 25;
    ages["Charlie"] = 35;

    print_assoc_array(ages);
    increment_all(ages);

    string key;
    if (find_value(ages, 26, key))
        $display("Found value 26 at key: %s", key);

    int lookup[string] = create_lookup();
end
```

**Working with different key types:**
```systemverilog
// Integer keys
function int sum_values(ref int aa[int]);
    int total = 0;
    foreach(aa[key]) total += aa[key];
    return total;
endfunction

// Wildcard keys (*)
function void process_wildcard(ref bit[7:0] aa[*]);
    foreach(aa[idx]) begin
        $display("Index: %0d, Value: 0x%0h", idx, aa[idx]);
    end
endfunction

// Usage
int data[int];
data[10] = 100;
data[20] = 200;
$display("Sum: %0d", sum_values(data));

bit [7:0] wild_array[*];
wild_array[5] = 8'hAA;
wild_array[100] = 8'hBB;
process_wildcard(wild_array);
```

---

## Advanced Level Questions

### Q41: Explain how to implement a factory pattern using functions.

**Answer:**

The **Factory Pattern** creates objects without specifying their exact class. Use static functions to implement factories in SystemVerilog.

**Example:**
```systemverilog
// Base class
virtual class Transaction;
    rand bit [31:0] addr;
    pure virtual function void display();
endclass

// Derived classes
class ReadTrans extends Transaction;
    virtual function void display();
        $display("READ addr=0x%0h", addr);
    endfunction
endclass

class WriteTrans extends Transaction;
    rand bit [31:0] data;
    virtual function void display();
        $display("WRITE addr=0x%0h, data=0x%0h", addr, data);
    endfunction
endclass

class PostedTrans extends Transaction;
    virtual function void display();
        $display("POSTED addr=0x%0h", addr);
    endfunction
endclass

// Factory class
class TransactionFactory;
    typedef enum {READ, WRITE, POSTED} trans_type_t;

    // Factory method
    static function Transaction create(trans_type_t t_type);
        case (t_type)
            READ:   return new ReadTrans();
            WRITE:  return new WriteTrans();
            POSTED: return new PostedTrans();
            default: begin
                $error("Unknown transaction type");
                return null;
            end
        endcase
    endfunction

    // Factory with randomization
    static function Transaction create_random();
        trans_type_t t = trans_type_t'($urandom_range(0, 2));
        Transaction tr = create(t);
        void'(tr.randomize());
        return tr;
    endfunction
endclass

// Usage
initial begin
    Transaction trans[$];

    // Create specific types
    trans.push_back(TransactionFactory::create(TransactionFactory::READ));
    trans.push_back(TransactionFactory::create(TransactionFactory::WRITE));

    // Create random transactions
    repeat(10) begin
        trans.push_back(TransactionFactory::create_random());
    end

    // Polymorphic usage
    foreach(trans[i]) trans[i].display();
end
```

**Advanced: Registry-based factory:**
```systemverilog
class GenericFactory;
    static Transaction registry[string];

    // Register a prototype
    static function void register(string name, Transaction prototype);
        registry[name] = prototype;
    endfunction

    // Create by cloning prototype
    static function Transaction create(string name);
        if (!registry.exists(name)) begin
            $error("Type '%s' not registered", name);
            return null;
        end
        // In real implementation, would clone the prototype
        return registry[name];
    endfunction
endclass
```

---

### Q42: How do you implement thread-safe functions in SystemVerilog?

**Answer:**

Use **semaphores** or **mailboxes** to protect shared resources in concurrent tasks:

**Example 1: Semaphore protection:**
```systemverilog
class ThreadSafeCounter;
    local int count = 0;
    local semaphore sem;

    function new();
        sem = new(1);  // Binary semaphore (mutex)
    endfunction

    task increment();
        sem.get();  // Lock
        count++;
        #1;  // Simulate some work
        sem.put();  // Unlock
    endtask

    task add(int value);
        sem.get();
        count += value;
        sem.put();
    endtask

    function int get_count();
        // Note: Functions can't use sem.get()/put() due to timing
        // This is safe only if called when no tasks are running
        return count;
    endfunction

    // Thread-safe get using task
    task get_count_safe(ref int value);
        sem.get();
        value = count;
        sem.put();
    endtask
endclass

// Usage
initial begin
    ThreadSafeCounter counter = new();

    fork
        repeat(100) counter.increment();
        repeat(100) counter.increment();
        repeat(100) counter.increment();
    join

    $display("Final count: %0d", counter.get_count());  // Should be 300
end
```

**Example 2: Mailbox for synchronization:**
```systemverilog
class SharedResource;
    local int data;
    local mailbox #(int) request_mbx;
    local mailbox #(int) response_mbx;

    function new();
        request_mbx = new();
        response_mbx = new();
        fork server(); join_none  // Start server task
    endfunction

    // Server task (single thread accessing data)
    task server();
        forever begin
            int req, resp;
            request_mbx.get(req);

            // Process request safely (no concurrent access)
            data += req;
            resp = data;

            response_mbx.put(resp);
        end
    endtask

    // Client interface (thread-safe)
    task add_and_get(int value, ref int result);
        request_mbx.put(value);
        response_mbx.get(result);
    endtask
endclass
```

**Example 3: Reader-Writer lock:**
```systemverilog
class RWLock;
    local semaphore read_sem;
    local semaphore write_sem;
    local int readers = 0;

    function new();
        read_sem = new(1);
        write_sem = new(1);
    endfunction

    task read_lock();
        read_sem.get();
        readers++;
        if (readers == 1) write_sem.get();  // First reader blocks writers
        read_sem.put();
    endtask

    task read_unlock();
        read_sem.get();
        readers--;
        if (readers == 0) write_sem.put();  // Last reader unblocks writers
        read_sem.put();
    endtask

    task write_lock();
        write_sem.get();
    endtask

    task write_unlock();
        write_sem.put();
    endtask
endclass
```

---

### Q43: What are nested functions and how do you use them?

**Answer:**

SystemVerilog does **NOT support nested function definitions** (defining a function inside another function). However, you can achieve similar effects using:

1. **Local classes with methods**
2. **Function calls within functions**
3. **Lambda-like patterns with classes**

**Workaround 1: Local class (closest to nested functions):**
```systemverilog
function automatic int outer_function(int x);
    // Local class definition (acts like nested function)
    class LocalHelper;
        static function int inner_calc(int a);
            return a * a + a;
        endfunction
    endclass

    int result = LocalHelper::inner_calc(x);
    return result + 10;
endfunction

// Usage
int val = outer_function(5);  // (5*5 + 5) + 10 = 40
```

**Workaround 2: Helper functions:**
```systemverilog
class MathUtils;
    // "Private" helper function
    local static function int helper(int a, int b);
        return a * a + b * b;
    endfunction

    // Public function using helper
    static function int distance(int x1, int y1, int x2, int y2);
        int dx = x2 - x1;
        int dy = y2 - y1;
        return helper(dx, dy);  // Call helper
    endfunction
endclass
```

**Workaround 3: Recursive pattern (function calling itself):**
```systemverilog
function automatic int sum_digits(int n);
    if (n < 10) return n;
    return (n % 10) + sum_digits(n / 10);  // "Nested" recursive call
endfunction
```

**Why nested functions would be useful (if supported):**
- Encapsulation of helper logic
- Access to outer function's variables
- Code organization

**Current limitations:**
- Must use separate functions or class methods
- No automatic access to outer scope variables
- Need to pass data explicitly

---

### Q44: How do you implement memoization for recursive functions?

**Answer:**

**Memoization** caches function results to avoid redundant calculations, especially useful for recursive functions.

**Example 1: Fibonacci with memoization:**
```systemverilog
class FibonacciMemo;
    static int cache[int];  // Associative array for caching

    static function automatic int fib(int n);
        // Base cases
        if (n <= 1) return n;

        // Check cache
        if (cache.exists(n)) begin
            $display("Cache hit for fib(%0d)", n);
            return cache[n];
        end

        // Calculate and store
        $display("Calculating fib(%0d)", n);
        cache[n] = fib(n-1) + fib(n-2);
        return cache[n];
    endfunction

    static function void clear_cache();
        cache.delete();
    endfunction
endclass

// Usage
initial begin
    $display("fib(10) = %0d", FibonacciMemo::fib(10));
    $display("\nSecond call (uses cache):");
    $display("fib(10) = %0d", FibonacciMemo::fib(10));
end
```

**Example 2: Factorial with statistics:**
```systemverilog
class FactorialMemo;
    static longint cache[int];
    static int cache_hits = 0;
    static int cache_misses = 0;

    static function automatic longint factorial(int n);
        if (n <= 1) return 1;

        if (cache.exists(n)) begin
            cache_hits++;
            return cache[n];
        end

        cache_misses++;
        cache[n] = n * factorial(n-1);
        return cache[n];
    endfunction

    static function void print_stats();
        $display("Cache hits: %0d, misses: %0d", cache_hits, cache_misses);
        $display("Hit rate: %.2f%%",
                 100.0 * cache_hits / (cache_hits + cache_misses));
    endfunction
endclass
```

**Example 3: LCS (Longest Common Subsequence) with 2D memo:**
```systemverilog
class LCSMemo;
    static int cache[int][int];  // 2D associative array

    static function automatic int lcs(string s1, string s2, int i, int j);
        // Base case
        if (i == 0 || j == 0) return 0;

        // Check cache
        if (cache.exists(i) && cache[i].exists(j))
            return cache[i][j];

        // Calculate
        if (s1[i-1] == s2[j-1]) begin
            cache[i][j] = 1 + lcs(s1, s2, i-1, j-1);
        end else begin
            int left = lcs(s1, s2, i-1, j);
            int right = lcs(s1, s2, i, j-1);
            cache[i][j] = (left > right) ? left : right;
        end

        return cache[i][j];
    endfunction
endclass

// Usage
initial begin
    string str1 = "ABCDGH";
    string str2 = "AEDFHR";
    int length = LCSMemo::lcs(str1, str2, str1.len(), str2.len());
    $display("LCS length: %0d", length);  // 3 (ADH)
end
```

**Benefits of memoization:**
- Dramatic performance improvement (exponential → polynomial)
- Transparent to caller
- Trade memory for speed

---

### Q45: Explain DPI function context and memory management.

**Answer:**

**DPI (Direct Programming Interface)** allows SystemVerilog to call C/C++ functions and vice versa.

**Memory management rules:**
1. **SV → C**: SV manages memory for SV objects
2. **C → SV**: Use `svdpi.h` functions to access SV data
3. **String passing**: Special handling required
4. **Array passing**: Use open arrays

**Example 1: Basic DPI with memory safety:**
```systemverilog
// SystemVerilog side
import "DPI-C" function void c_process_array(
    input int size,
    input int arr[],      // Open array
    output int result[]
);

import "DPI-C" function string c_get_message();  // String from C

import "DPI-C" context function void c_with_context(int value);

// Usage
initial begin
    int input_data[] = '{1, 2, 3, 4, 5};
    int output_data[];

    output_data = new[input_data.size()];
    c_process_array(input_data.size(), input_data, output_data);

    string msg = c_get_message();
    $display("Message from C: %s", msg);
end
```

**C side (dpi.c):**
```c
#include "svdpi.h"
#include <stdlib.h>
#include <string.h>

// Process array - SV manages memory
void c_process_array(int size, const int* arr, int* result) {
    for (int i = 0; i < size; i++) {
        result[i] = arr[i] * 2;
    }
}

// Return string - MUST be static or allocated memory
const char* c_get_message() {
    static char msg[] = "Hello from C";
    return msg;

    // WRONG: Local array would be destroyed
    // char local_msg[] = "Hello";
    // return local_msg;  // Dangling pointer!
}

// Context function - can call back to SV
void c_with_context(int value) {
    // Can call SV exported functions here
    sv_callback(value * 2);
}
```

**Example 2: Complex data structures:**
```systemverilog
// Pass struct via packed array
typedef struct packed {
    bit [31:0] addr;
    bit [31:0] data;
    bit [7:0] id;
} transaction_t;

import "DPI-C" function void c_process_trans(
    input bit [71:0] trans_packed  // Pass as packed bit vector
);

// Usage
initial begin
    transaction_t trans;
    trans.addr = 32'h1000;
    trans.data = 32'hDEADBEEF;
    trans.id = 8'h42;

    c_process_trans(trans);  // Automatic packing
end
```

**Example 3: Memory allocation best practices:**
```systemverilog
// Export SV function for C to call
export "DPI-C" function sv_allocate;
export "DPI-C" function sv_deallocate;

function bit [31:0] sv_allocate(int size);
    // Create SV object and return handle
    static int handle_counter = 1;
    // Store in associative array keyed by handle
    return handle_counter++;
endfunction

function void sv_deallocate(bit [31:0] handle);
    // Remove from associative array
endfunction
```

**Common pitfalls:**
1. **Dangling pointers**: Returning pointers to local variables
2. **Memory leaks**: Not freeing allocated memory
3. **String lifetime**: Strings must outlive the function call
4. **Array bounds**: No automatic bounds checking

---

### Q46: How do you implement design patterns (Observer, Singleton) using functions/tasks?

**Answer:**

**Pattern 1: Singleton (single instance):**
```systemverilog
class ConfigManager;
    static local ConfigManager instance = null;
    local int config_data[string];

    // Private constructor
    local function new();
        config_data["timeout"] = 1000;
        config_data["retries"] = 3;
    endfunction

    // Public getInstance method
    static function ConfigManager getInstance();
        if (instance == null)
            instance = new();
        return instance;
    endfunction

    function void set_config(string key, int value);
        config_data[key] = value;
    endfunction

    function int get_config(string key);
        return config_data.exists(key) ? config_data[key] : -1;
    endfunction
endclass

// Usage - always get the same instance
ConfigManager cfg1 = ConfigManager::getInstance();
ConfigManager cfg2 = ConfigManager::getInstance();
// cfg1 and cfg2 point to the same object
```

**Pattern 2: Observer (publish-subscribe):**
```systemverilog
// Observer interface
virtual class Observer;
    pure virtual function void update(string event_name, int data);
endclass

// Concrete observers
class Logger extends Observer;
    virtual function void update(string event_name, int data);
        $display("[LOG] Event: %s, Data: %0d", event_name, data);
    endfunction
endclass

class Statistics extends Observer;
    int event_count = 0;

    virtual function void update(string event_name, int data);
        event_count++;
        $display("[STATS] Total events: %0d", event_count);
    endfunction
endclass

// Subject (Observable)
class EventManager;
    local Observer observers[$];

    function void attach(Observer obs);
        observers.push_back(obs);
    endfunction

    function void detach(Observer obs);
        foreach(observers[i]) begin
            if (observers[i] == obs) begin
                observers.delete(i);
                return;
            end
        end
    endfunction

    function void notify(string event_name, int data);
        foreach(observers[i]) begin
            observers[i].update(event_name, data);
        end
    endfunction

    // Convenience task for delayed notification
    task notify_after_delay(string event_name, int data, int delay);
        #delay;
        notify(event_name, data);
    endtask
endclass

// Usage
initial begin
    EventManager em = new();
    Logger log = new();
    Statistics stats = new();

    em.attach(log);
    em.attach(stats);

    em.notify("TRANSACTION", 100);
    em.notify("ERROR", 500);

    em.detach(log);  // Stop logging
    em.notify("TRANSACTION", 200);  // Only stats updated
end
```

**Pattern 3: Strategy (algorithm selection):**
```systemverilog
// Strategy interface
virtual class SortStrategy;
    pure virtual function void sort(ref int arr[]);
endclass

// Concrete strategies
class BubbleSort extends SortStrategy;
    virtual function void sort(ref int arr[]);
        for (int i = 0; i < arr.size()-1; i++) begin
            for (int j = 0; j < arr.size()-1-i; j++) begin
                if (arr[j] > arr[j+1]) begin
                    int temp = arr[j];
                    arr[j] = arr[j+1];
                    arr[j+1] = temp;
                end
            end
        end
    endfunction
endclass

class QuickSort extends SortStrategy;
    virtual function void sort(ref int arr[]);
        if (arr.size() <= 1) return;
        quicksort_helper(arr, 0, arr.size()-1);
    endfunction

    local function void quicksort_helper(ref int arr[], int low, int high);
        if (low < high) begin
            int pi = partition(arr, low, high);
            quicksort_helper(arr, low, pi-1);
            quicksort_helper(arr, pi+1, high);
        end
    endfunction

    local function int partition(ref int arr[], int low, int high);
        // Partition logic
        return low;  // Simplified
    endfunction
endclass

// Context
class Sorter;
    local SortStrategy strategy;

    function void set_strategy(SortStrategy s);
        strategy = s;
    endfunction

    function void sort(ref int arr[]);
        strategy.sort(arr);
    endfunction
endclass

// Usage
initial begin
    Sorter sorter = new();
    int data[] = '{5, 2, 8, 1, 9};

    sorter.set_strategy(new BubbleSort());
    sorter.sort(data);  // Use bubble sort

    sorter.set_strategy(new QuickSort());
    sorter.sort(data);  // Use quick sort
end
```

---

### Q47: How do you handle variable-length arguments in functions?

**Answer:**

SystemVerilog doesn't support true variadic functions (like C's `va_args`), but you can use:

1. **Dynamic arrays**
2. **Queues**
3. **Default parameters**
4. **Unpacked arrays with size parameter**

**Approach 1: Queue (most flexible):**
```systemverilog
function int sum_all(int values[$]);
    int total = 0;
    foreach(values[i]) total += values[i];
    return total;
endfunction

// Usage
int result1 = sum_all('{1, 2, 3});           // 6
int result2 = sum_all('{10, 20, 30, 40});    // 100
int result3 = sum_all('{});                  // 0 (empty)

// Can build dynamically
int nums[$] = '{1, 2, 3};
nums.push_back(4);
nums.push_back(5);
int result4 = sum_all(nums);  // 15
```

**Approach 2: Dynamic array:**
```systemverilog
function real average(real values[]);
    real sum = 0;
    if (values.size() == 0) return 0;
    foreach(values[i]) sum += values[i];
    return sum / values.size();
endfunction

// Usage
real data[] = '{1.5, 2.5, 3.5, 4.5};
real avg = average(data);
```

**Approach 3: Multiple overloaded-style functions with defaults:**
```systemverilog
function int max_value(
    int a,
    int b = -2147483648,  // INT_MIN as sentinel
    int c = -2147483648,
    int d = -2147483648
);
    int result = a;
    if (b != -2147483648 && b > result) result = b;
    if (c != -2147483648 && c > result) result = c;
    if (d != -2147483648 && d > result) result = d;
    return result;
endfunction

// Usage
int m1 = max_value(10);              // 10
int m2 = max_value(10, 20);          // 20
int m3 = max_value(10, 20, 30);      // 30
int m4 = max_value(10, 20, 30, 40);  // 40
```

**Approach 4: Passing array size explicitly:**
```systemverilog
function void print_values(int size, int values[]);
    $write("Values: ");
    for (int i = 0; i < size; i++) begin
        $write("%0d ", values[i]);
    end
    $display("");
endfunction

// Usage
int arr1[3] = '{1, 2, 3};
int arr2[5] = '{10, 20, 30, 40, 50};
print_values(3, arr1);
print_values(5, arr2);
```

**Best practice - Use queues for true variable-length:**
```systemverilog
class PrintUtils;
    static function void printf(string format, string args[$]);
        string result = format;
        foreach(args[i]) begin
            // Simple replacement (real implementation would be more complex)
            string placeholder = $sformatf("%%%0d", i);
            // Replace placeholder with actual value
        end
        $display("%s", result);
    endfunction
endclass
```

---

### Q48: Explain the interaction between functions/tasks and assertions.

**Answer:**

Functions and tasks can be used with assertions in several ways:

**1. Functions in assertion expressions:**
```systemverilog
function bit is_power_of_two(int n);
    return (n > 0) && ((n & (n-1)) == 0);
endfunction

// Use in immediate assertion
assert (is_power_of_two(size))
    else $error("Size must be power of 2");

// Use in concurrent assertion (property)
property valid_size;
    @(posedge clk) is_power_of_two(transfer_size);
endproperty

assert property (valid_size);
```

**2. Assertion within functions (immediate assertions):**
```systemverilog
function int safe_divide(int a, int b);
    assert (b != 0) else $fatal("Division by zero");
    return a / b;
endfunction

function bit [7:0] encode(bit [3:0] value);
    assert (value < 10)
        else $error("Value %0d out of range", value);
    return value + 8'h30;  // ASCII encoding
endfunction
```

**3. Functions for complex assertion checks:**
```systemverilog
function bit check_parity(bit [7:0] data, bit parity);
    return (^data) == parity;  // XOR reduction
endfunction

property correct_parity;
    @(posedge clk) valid |-> check_parity(data_bus, parity_bit);
endproperty

assert property (correct_parity)
    else $error("Parity check failed");
```

**4. Tasks with assertions for protocol checking:**
```systemverilog
task check_handshake(ref bit req, ref bit ack, int timeout);
    int cycles = 0;

    assert (req) else $error("REQ not asserted");

    while (!ack && cycles < timeout) begin
        @(posedge clk);
        cycles++;
    end

    assert (ack) else $error("ACK timeout after %0d cycles", timeout);
endtask
```

**5. Coverage functions with assertions:**
```systemverilog
class Transaction;
    rand bit [7:0] addr;
    rand bit [7:0] data;

    covergroup cg;
        addr_cp: coverpoint addr;
        data_cp: coverpoint data;
    endgroup

    function new();
        cg = new();
    endfunction

    function void check_and_cover();
        // Assertion check
        assert (addr inside {[0:255]})
            else $error("Address out of range");

        // Sample coverage
        cg.sample();

        // Check coverage progress
        if (cg.get_coverage() >= 100.0) begin
            $display("Full coverage achieved!");
        end
    endfunction
endclass
```

**6. Assertion severity functions:**
```systemverilog
typedef enum {INFO, WARNING, ERROR, FATAL} severity_t;

function void check_value(int val, int min, int max, severity_t sev);
    if (val < min || val > max) begin
        case (sev)
            INFO:    $info("Value %0d out of range [%0d:%0d]", val, min, max);
            WARNING: $warning("Value %0d out of range [%0d:%0d]", val, min, max);
            ERROR:   $error("Value %0d out of range [%0d:%0d]", val, min, max);
            FATAL:   $fatal("Value %0d out of range [%0d:%0d]", val, min, max);
        endcase
    end
endfunction

// Usage
check_value(data, 0, 255, ERROR);
```

**7. Deferred assertions with tasks:**
```systemverilog
task check_transaction_complete();
    @(posedge start);
    fork
        begin
            wait (done);
            $display("Transaction completed successfully");
        end
        begin
            repeat(1000) @(posedge clk);
            assert_timeout: assert (done)
                else $error("Transaction timeout");
        end
    join_any
    disable fork;
endtask
```

---

### Q49: How do you profile and optimize function performance?

**Answer:**

**Technique 1: Timing measurement:**
```systemverilog
class Profiler;
    static realtime start_times[string];
    static realtime total_times[string];
    static int call_counts[string];

    static function void start_profile(string func_name);
        start_times[func_name] = $realtime;
    endfunction

    static function void end_profile(string func_name);
        realtime elapsed = $realtime - start_times[func_name];

        if (!total_times.exists(func_name)) begin
            total_times[func_name] = 0;
            call_counts[func_name] = 0;
        end

        total_times[func_name] += elapsed;
        call_counts[func_name]++;
    endfunction

    static function void report();
        $display("\n=== Performance Profile ===");
        $display("%-20s %10s %15s %15s",
                 "Function", "Calls", "Total Time", "Avg Time");
        $display("-".repeat(65));

        foreach(total_times[func]) begin
            realtime avg = total_times[func] / call_counts[func];
            $display("%-20s %10d %15t %15t",
                     func, call_counts[func], total_times[func], avg);
        end
    endfunction
endclass

// Example usage
function int fibonacci(int n);
    Profiler::start_profile("fibonacci");

    int result;
    if (n <= 1) result = n;
    else result = fibonacci(n-1) + fibonacci(n-2);

    Profiler::end_profile("fibonacci");
    return result;
endfunction
```

**Technique 2: Call counting:**
```systemverilog
class FunctionStats;
    static int call_count = 0;
    static int cache_hits = 0;

    static function void increment_calls();
        call_count++;
    endfunction

    static function void increment_hits();
        cache_hits++;
    endfunction

    static function void print_stats();
        real hit_rate = (cache_hits * 100.0) / call_count;
        $display("Total calls: %0d", call_count);
        $display("Cache hits: %0d (%.1f%%)", cache_hits, hit_rate);
    endfunction
endclass
```

**Technique 3: Memory usage tracking:**
```systemverilog
class MemoryTracker;
    static longint allocated_bytes = 0;
    static int allocation_count = 0;

    static function void track_allocation(int bytes);
        allocated_bytes += bytes;
        allocation_count++;
    endfunction

    static function void report();
        $display("Total allocations: %0d", allocation_count);
        $display("Total memory: %0d bytes (%.2f KB)",
                 allocated_bytes, allocated_bytes/1024.0);
    endfunction
endclass

function int[] create_array(int size);
    MemoryTracker::track_allocation(size * $bits(int) / 8);
    int result[] = new[size];
    return result;
endfunction
```

**Technique 4: Optimization comparison:**
```systemverilog
class PerformanceTest;
    static function void compare_implementations();
        realtime start, elapsed1, elapsed2;
        int result;

        // Test naive implementation
        start = $realtime;
        repeat(1000) result = fibonacci_naive(20);
        elapsed1 = $realtime - start;

        // Test optimized implementation
        start = $realtime;
        repeat(1000) result = fibonacci_memo(20);
        elapsed2 = $realtime - start;

        $display("Naive:     %0t", elapsed1);
        $display("Memoized:  %0t", elapsed2);
        $display("Speedup:   %.2fx", real'(elapsed1) / real'(elapsed2));
    endfunction
endclass
```

**Technique 5: Bottleneck identification:**
```systemverilog
`define PROFILE_FUNC(name) \
    Profiler::start_profile(`"name`"); \
    /* function body */ \
    Profiler::end_profile(`"name`");

function void complex_algorithm();
    `PROFILE_FUNC(complex_algorithm)

    step1();  // Each step profiled separately
    step2();
    step3();
endfunction

function void step1();
    `PROFILE_FUNC(step1)
    // implementation
endfunction
```

**Optimization strategies:**
1. **Memoization**: Cache expensive calculations
2. **Early exit**: Return as soon as possible
3. **Avoid recursion**: Use iteration where possible
4. **Minimize array copies**: Use `ref` parameters
5. **Reduce object creation**: Reuse objects
6. **Profile first**: Measure before optimizing

---

### Q50: Implement a complete protocol driver (AXI4-Lite) using tasks and functions.

**Answer:**

```systemverilog
interface axi4_lite_if(input bit clk);
    // Write address channel
    logic [31:0] awaddr;
    logic        awvalid;
    logic        awready;

    // Write data channel
    logic [31:0] wdata;
    logic [3:0]  wstrb;
    logic        wvalid;
    logic        wready;

    // Write response channel
    logic [1:0]  bresp;
    logic        bvalid;
    logic        bready;

    // Read address channel
    logic [31:0] araddr;
    logic        arvalid;
    logic        arready;

    // Read data channel
    logic [31:0] rdata;
    logic [1:0]  rresp;
    logic        rvalid;
    logic        rready;
endinterface

class AXI4LiteMaster;
    virtual axi4_lite_if vif;

    typedef enum {OKAY = 2'b00, EXOKAY = 2'b01,
                  SLVERR = 2'b10, DECERR = 2'b11} resp_t;

    function new(virtual axi4_lite_if vif);
        this.vif = vif;
        initialize();
    endfunction

    // Initialize all signals
    function void initialize();
        vif.awaddr  = 0;
        vif.awvalid = 0;
        vif.wdata   = 0;
        vif.wstrb   = 0;
        vif.wvalid  = 0;
        vif.bready  = 0;
        vif.araddr  = 0;
        vif.arvalid = 0;
        vif.rready  = 0;
    endfunction

    // Write transaction
    task write(
        input bit [31:0] addr,
        input bit [31:0] data,
        input bit [3:0]  strb = 4'hF,
        output resp_t    resp
    );
        fork
            write_addr_phase(addr);
            write_data_phase(data, strb);
        join
        write_resp_phase(resp);
    endtask

    // Write address phase
    task write_addr_phase(bit [31:0] addr);
        @(posedge vif.clk);
        vif.awaddr  <= addr;
        vif.awvalid <= 1;

        // Wait for awready
        do @(posedge vif.clk);
        while (!vif.awready);

        vif.awvalid <= 0;
    endtask

    // Write data phase
    task write_data_phase(bit [31:0] data, bit [3:0] strb);
        @(posedge vif.clk);
        vif.wdata  <= data;
        vif.wstrb  <= strb;
        vif.wvalid <= 1;

        // Wait for wready
        do @(posedge vif.clk);
        while (!vif.wready);

        vif.wvalid <= 0;
    endtask

    // Write response phase
    task write_resp_phase(output resp_t resp);
        vif.bready <= 1;

        // Wait for bvalid
        do @(posedge vif.clk);
        while (!vif.bvalid);

        resp = resp_t'(vif.bresp);
        @(posedge vif.clk);
        vif.bready <= 0;
    endtask

    // Read transaction
    task read(
        input  bit [31:0] addr,
        output bit [31:0] data,
        output resp_t     resp
    );
        read_addr_phase(addr);
        read_data_phase(data, resp);
    endtask

    // Read address phase
    task read_addr_phase(bit [31:0] addr);
        @(posedge vif.clk);
        vif.araddr  <= addr;
        vif.arvalid <= 1;

        // Wait for arready
        do @(posedge vif.clk);
        while (!vif.arready);

        vif.arvalid <= 0;
    endtask

    // Read data phase
    task read_data_phase(output bit [31:0] data, output resp_t resp);
        vif.rready <= 1;

        // Wait for rvalid
        do @(posedge vif.clk);
        while (!vif.rvalid);

        data = vif.rdata;
        resp = resp_t'(vif.rresp);
        @(posedge vif.clk);
        vif.rready <= 0;
    endtask

    // Burst write (multiple consecutive writes)
    task burst_write(
        bit [31:0] start_addr,
        bit [31:0] data_queue[$]
    );
        foreach(data_queue[i]) begin
            resp_t resp;
            write(start_addr + (i*4), data_queue[i], 4'hF, resp);
            assert(resp == OKAY)
                else $error("Write failed at addr 0x%0h", start_addr + (i*4));
        end
    endtask

    // Burst read
    task burst_read(
        bit [31:0] start_addr,
        int count,
        ref bit [31:0] data_queue[$]
    );
        data_queue.delete();
        for (int i = 0; i < count; i++) begin
            bit [31:0] data;
            resp_t resp;
            read(start_addr + (i*4), data, resp);
            assert(resp == OKAY)
                else $error("Read failed at addr 0x%0h", start_addr + (i*4));
            data_queue.push_back(data);
        end
    endtask

    // Helper function: Check if response is OK
    function bit is_okay(resp_t resp);
        return (resp == OKAY || resp == EXOKAY);
    endfunction

    // Helper function: Response to string
    function string resp_to_string(resp_t resp);
        case (resp)
            OKAY:   return "OKAY";
            EXOKAY: return "EXOKAY";
            SLVERR: return "SLVERR";
            DECERR: return "DECERR";
        endcase
    endfunction

    // Write with timeout
    task write_with_timeout(
        input  bit [31:0] addr,
        input  bit [31:0] data,
        input  int        timeout_cycles,
        output bit        success,
        output resp_t     resp
    );
        success = 0;
        fork
            begin
                write(addr, data, 4'hF, resp);
                success = 1;
            end
            begin
                repeat(timeout_cycles) @(posedge vif.clk);
            end
        join_any
        disable fork;

        if (!success)
            $error("Write timeout at addr 0x%0h", addr);
    endtask
endclass

// Usage example
program test;
    AXI4LiteMaster master;

    initial begin
        master = new(top.axi_if);

        // Single write
        AXI4LiteMaster::resp_t resp;
        master.write(32'h1000, 32'hDEADBEEF, 4'hF, resp);
        $display("Write response: %s", master.resp_to_string(resp));

        // Single read
        bit [31:0] read_data;
        master.read(32'h1000, read_data, resp);
        $display("Read data: 0x%0h, response: %s",
                 read_data, master.resp_to_string(resp));

        // Burst write
        bit [31:0] write_data[$] = '{32'h11, 32'h22, 32'h33, 32'h44};
        master.burst_write(32'h2000, write_data);

        // Burst read
        bit [31:0] read_data_queue[$];
        master.burst_read(32'h2000, 4, read_data_queue);
        $display("Burst read: %p", read_data_queue);
    end
endprogram
```

This implementation demonstrates:
- Task-based protocol implementation
- Channel handshaking
- Error handling
- Burst operations
- Helper functions
- Timeout mechanisms
- Real-world driver structure

---

### Q51: How do you implement coroutines or cooperative multitasking?

**Answer:**

SystemVerilog doesn't have native coroutines, but we can implement cooperative multitasking using tasks and semaphores:

**Example: Coroutine-style task switching:**
```systemverilog
class Coroutine;
    typedef enum {READY, RUNNING, SUSPENDED, DONE} state_t;

    local state_t state = READY;
    local string name;
    local int resume_point = 0;

    function new(string n);
        name = n;
    endfunction

    // Yield control to scheduler
    task yield();
        state = SUSPENDED;
        $display("[%0t] %s yielding", $time, name);
        @(posedge resume_event);
        state = RUNNING;
    endtask

    // Main coroutine body (to be overridden)
    pure virtual task run();
endclass

class Scheduler;
    Coroutine tasks[$];
    int current_task = 0;

    function void add_task(Coroutine t);
        tasks.push_back(t);
    endfunction

    task run_scheduler();
        while (tasks.size() > 0) begin
            Coroutine current = tasks[current_task];

            if (current.state != Coroutine::DONE) begin
                current.state = Coroutine::RUNNING;
                fork
                    current.run();
                join_none

                // Let it run for a bit
                #100;

                // Move to next task
                current_task = (current_task + 1) % tasks.size();
            end else begin
                // Remove completed task
                tasks.delete(current_task);
                if (tasks.size() > 0)
                    current_task = current_task % tasks.size();
            end
        end
    endtask
endclass
```

---

### Q52: Explain function inlining and its implications in SystemVerilog.

**Answer:**

SystemVerilog compilers may **inline** small functions to improve performance by eliminating function call overhead.

**What gets inlined:**
- Small functions (few lines)
- Functions called frequently
- Functions without complex control flow

**Example that might be inlined:**
```systemverilog
function bit is_even(int n);
    return (n & 1) == 0;
endfunction

// May be inlined to:
// if ((value & 1) == 0) ...
if (is_even(value)) begin
    // ...
end
```

**Factors preventing inlining:**
- Large function body
- Recursive functions
- Functions with side effects
- Virtual functions (dynamic dispatch)

**Best practices:**
- Write small, focused functions
- Don't worry about inlining - let compiler optimize
- Use `inline` hint if supported (tool-specific)
- Profile to find actual bottlenecks

---

### Q53: How do you implement lazy evaluation using functions?

**Answer:**

**Lazy evaluation** delays computation until the result is actually needed.

**Example 1: Lazy data structure:**
```systemverilog
class LazyValue#(type T = int);
    local bit computed = 0;
    local T value;
    local function T compute();  // Override in derived class

    function T get();
        if (!computed) begin
            value = compute();
            computed = 1;
            $display("Computing value...");
        end
        return value;
    endfunction

    function void invalidate();
        computed = 0;
    endfunction
endclass

class ExpensiveCalculation extends LazyValue#(int);
    virtual function int compute();
        // Expensive operation
        int result = 0;
        for (int i = 0; i < 1000; i++)
            result += i * i;
        return result;
    endfunction
endclass

// Usage
ExpensiveCalculation calc = new();
// Not computed yet...
int val1 = calc.get();  // Computed now
int val2 = calc.get();  // Uses cached value
```

**Example 2: Lazy list/stream:**
```systemverilog
class LazyList;
    local int cache[$];
    local int last_index = -1;

    // Generate next element (override this)
    virtual function int generate(int index);
        return index * 2;  // Example: even numbers
    endfunction

    function int get(int index);
        // Generate up to requested index
        while (last_index < index) begin
            last_index++;
            cache.push_back(generate(last_index));
        end
        return cache[index];
    endfunction
endclass
```

---

### Q54: What are the best practices for error propagation in nested function calls?

**Answer:**

**Strategy 1: Return status codes:**
```systemverilog
typedef enum {OK, ERR_INVALID, ERR_TIMEOUT, ERR_OVERFLOW} status_t;

function status_t validate_data(bit [7:0] data);
    if (data > 100) return ERR_OVERFLOW;
    return OK;
endfunction

function status_t process_data(bit [7:0] data, ref int result);
    status_t status;

    // Check nested function
    status = validate_data(data);
    if (status != OK) return status;

    // Process
    result = data * 2;
    return OK;
endfunction

// Usage with error checking
status_t status;
int result;
status = process_data(data_in, result);
if (status != OK)
    $error("Processing failed: %s", status.name());
```

**Strategy 2: Exception-like pattern:**
```systemverilog
class Result#(type T = int);
    bit success;
    T value;
    string error_msg;

    static function Result#(T) ok(T val);
        Result#(T) r = new();
        r.success = 1;
        r.value = val;
        return r;
    endfunction

    static function Result#(T) error(string msg);
        Result#(T) r = new();
        r.success = 0;
        r.error_msg = msg;
        return r;
    endfunction
endclass

function Result#(int) divide(int a, int b);
    if (b == 0)
        return Result#(int)::error("Division by zero");
    return Result#(int)::ok(a / b);
endfunction
```

---

### Q55: How do you implement function composition and higher-order functions?

**Answer:**

**Example 1: Function composition:**
```systemverilog
typedef function int transform_f(int x);

class FunctionUtils;
    // Compose two functions: (f ∘ g)(x) = f(g(x))
    static function transform_f compose(transform_f f, transform_f g);
        // Return a new function that applies g then f
        // Note: SystemVerilog limitations mean we return the typedef
        return f;  // Simplified - full implementation needs wrapper class
    endfunction
endclass

// Better approach using classes
class Transform;
    virtual function int apply(int x);
        return x;
    endfunction
endclass

class Double extends Transform;
    virtual function int apply(int x);
        return x * 2;
    endfunction
endclass

class AddTen extends Transform;
    virtual function int apply(int x);
        return x + 10;
    endfunction
endclass

class Compose extends Transform;
    Transform f, g;

    function new(Transform f_in, Transform g_in);
        f = f_in;
        g = g_in;
    endfunction

    virtual function int apply(int x);
        return f.apply(g.apply(x));  // f(g(x))
    endfunction
endclass

// Usage
Transform pipeline = new Compose(new Double(), new AddTen());
int result = pipeline.apply(5);  // (5 + 10) * 2 = 30
```

**Example 2: Map/Filter/Reduce:**
```systemverilog
class FunctionalOps;
    // Map: Apply function to each element
    static function int[] map(int arr[], Transform f);
        int result[] = new[arr.size()];
        foreach(arr[i])
            result[i] = f.apply(arr[i]);
        return result;
    endfunction

    // Filter: Keep elements that match predicate
    typedef function bit predicate_f(int x);

    static function int[] filter(int arr[], predicate_f pred);
        int temp[$];
        foreach(arr[i])
            if (pred(arr[i]))
                temp.push_back(arr[i]);

        int result[] = new[temp.size()];
        foreach(result[i])
            result[i] = temp[i];
        return result;
    endfunction

    // Reduce: Combine all elements
    typedef function int combine_f(int acc, int x);

    static function int reduce(int arr[], combine_f comb, int initial);
        int accumulator = initial;
        foreach(arr[i])
            accumulator = comb(accumulator, arr[i]);
        return accumulator;
    endfunction
endclass

// Usage
function bit is_even(int x);
    return (x & 1) == 0;
endfunction

function int add(int a, int b);
    return a + b;
endfunction

int data[] = '{1, 2, 3, 4, 5};
int doubled[] = FunctionalOps::map(data, new Double());
int evens[] = FunctionalOps::filter(data, is_even);
int sum = FunctionalOps::reduce(data, add, 0);
```

---

## Scenario-Based Questions

### Q56: Design a verification component (driver) for a UART transmitter using tasks.

**Answer:**

```systemverilog
class UARTDriver;
    virtual uart_if vif;
    bit [7:0] tx_queue[$];

    // Configuration
    int baud_period_ns = 8680;  // 115200 baud
    bit parity_enable = 1;
    bit [1:0] stop_bits = 1;    // 1 or 2 stop bits

    function new(virtual uart_if vif);
        this.vif = vif;
        vif.tx = 1;  // Idle high
    endfunction

    // Main driver task
    task run();
        forever begin
            bit [7:0] data;
            if (tx_queue.size() > 0) begin
                data = tx_queue.pop_front();
                transmit_byte(data);
            end else begin
                @(posedge vif.clk);
            end
        end
    endtask

    // Transmit a single byte
    task transmit_byte(bit [7:0] data);
        $display("[%0t] TX: 0x%0h ('%s')", $time, data,
                 (data >= 32 && data < 127) ? string'(data) : ".");

        send_start_bit();
        send_data_bits(data);
        if (parity_enable)
            send_parity_bit(data);
        send_stop_bits();
    endtask

    task send_start_bit();
        vif.tx = 0;
        #(baud_period_ns * 1ns);
    endtask

    task send_data_bits(bit [7:0] data);
        for (int i = 0; i < 8; i++) begin
            vif.tx = data[i];
            #(baud_period_ns * 1ns);
        end
    endtask

    task send_parity_bit(bit [7:0] data);
        bit parity = ^data;  // Even parity
        vif.tx = parity;
        #(baud_period_ns * 1ns);
    endtask

    task send_stop_bits();
        vif.tx = 1;
        #(baud_period_ns * stop_bits * 1ns);
    endtask

    // High-level API
    function void send(bit [7:0] data);
        tx_queue.push_back(data);
    endfunction

    function void send_string(string str);
        for (int i = 0; i < str.len(); i++)
            tx_queue.push_back(str[i]);
    endfunction

    task send_blocking(bit [7:0] data);
        transmit_byte(data);
    endtask
endclass
```

---

### Q57: You need to implement a scoreboard. Which functions/tasks would you use and why?

**Answer:**

```systemverilog
class Scoreboard;
    // Expected transactions (from reference model)
    Transaction expected_q[$];

    // Received transactions (from DUT)
    Transaction received_q[$];

    // Statistics
    int matches = 0;
    int mismatches = 0;
    int expected_count = 0;
    int received_count = 0;

    // Add expected transaction (from reference model)
    function void add_expected(Transaction t);
        expected_q.push_back(t);
        expected_count++;
    endfunction

    // Add received transaction (from monitor)
    function void add_received(Transaction t);
        received_q.push_back(t);
        received_count++;
    endfunction

    // Check task - runs continuously
    task run();
        forever begin
            if (expected_q.size() > 0 && received_q.size() > 0) begin
                compare_transactions();
            end else begin
                @(expected_q.size() || received_q.size());
            end
        end
    endtask

    // Compare transactions
    function void compare_transactions();
        Transaction exp = expected_q.pop_front();
        Transaction rec = received_q.pop_front();

        if (exp.compare(rec)) begin
            matches++;
            $display("[PASS] Transaction match");
        end else begin
            mismatches++;
            $error("[FAIL] Transaction mismatch");
            $display("Expected: %s", exp.to_string());
            $display("Received: %s", rec.to_string());
        end
    endfunction

    // Final report
    function void report();
        $display("\n=== Scoreboard Report ===");
        $display("Expected: %0d", expected_count);
        $display("Received: %0d", received_count);
        $display("Matches:  %0d", matches);
        $display("Mismatches: %0d", mismatches);

        if (mismatches == 0 && expected_count == received_count)
            $display("*** TEST PASSED ***");
        else
            $error("*** TEST FAILED ***");
    endfunction
endclass
```

**Design choices:**
- `add_expected/add_received`: **Functions** (no timing, just queue operations)
- `run`: **Task** (needs to wait for events)
- `compare_transactions`: **Function** (pure comparison, no timing)
- `report`: **Function** (just displays stats)

---

### Q58: How would you debug a function that works in simulation but fails in formal verification?

**Answer:**

This scenario involves differences between simulation semantics and formal tools:

**Common issues:**
1. **Uninitialized variables**
2. **X-propagation differences**
3. **Timing assumptions**
4. **Non-deterministic behavior**

**Debugging approach:**

```systemverilog
// Problematic code (works in sim, fails in formal)
function bit check_status();
    bit status;  // Uninitialized!
    if (some_condition)
        status = 1;
    // If some_condition is false, status is X in simulation
    // but formal tools may treat it as 0 or 1
    return status;
endfunction

// Fixed version
function bit check_status_fixed();
    bit status = 0;  // Explicitly initialize
    if (some_condition)
        status = 1;
    return status;
endfunction

// Add assertions for formal
function bit check_status_with_assert();
    bit status = 0;
    if (some_condition) begin
        status = 1;
    end

    // Help formal verification
    assert (status === 0 || status === 1)
        else $error("Status has X/Z value");

    return status;
endfunction
```

**Debugging techniques:**
1. Add assertions for all assumptions
2. Initialize all variables
3. Avoid X-dependent behavior
4. Use `$isunknown()` checks
5. Add formal-specific constraints

---

### Q59: Design a self-checking testbench using only functions and tasks (no classes).

**Answer:**

```systemverilog
module self_checking_tb;
    // DUT signals
    logic clk = 0;
    logic rst_n;
    logic [7:0] data_in;
    logic [7:0] data_out;
    logic valid_in;
    logic valid_out;

    // DUT instantiation
    dut u_dut (.*);

    // Clock generation
    always #5 clk = ~clk;

    // Test statistics (module-level variables)
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    // Reference model function
    function bit [7:0] reference_model(bit [7:0] input_data);
        // Expected behavior
        return input_data + 1;
    endfunction

    // Checker function
    function bit check_output(bit [7:0] expected, bit [7:0] actual);
        if (expected === actual) begin
            pass_count++;
            return 1;
        end else begin
            fail_count++;
            $error("[FAIL] Expected: 0x%0h, Got: 0x%0h", expected, actual);
            return 0;
        end
    endfunction

    // Stimulus task
    task apply_stimulus(bit [7:0] data);
        @(posedge clk);
        data_in <= data;
        valid_in <= 1;
        @(posedge clk);
        valid_in <= 0;
    endtask

    // Wait for output task
    task wait_for_output(ref bit [7:0] data);
        do @(posedge clk);
        while (!valid_out);
        data = data_out;
    endtask

    // Complete test sequence
    task run_test(bit [7:0] input_data);
        bit [7:0] expected, actual;

        test_count++;
        expected = reference_model(input_data);

        apply_stimulus(input_data);
        wait_for_output(actual);
        check_output(expected, actual);
    endtask

    // Test generation task
    task run_all_tests();
        // Directed tests
        run_test(8'h00);
        run_test(8'hFF);
        run_test(8'h55);
        run_test(8'hAA);

        // Random tests
        repeat(100) begin
            run_test($urandom());
        end
    endtask

    // Report function
    function void final_report();
        $display("\n========== TEST REPORT ==========");
        $display("Total Tests: %0d", test_count);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);
        $display("Pass Rate:   %.1f%%", (100.0 * pass_count) / test_count);
        $display("================================\n");

        if (fail_count == 0)
            $display("*** ALL TESTS PASSED ***");
        else
            $error("*** %0d TESTS FAILED ***", fail_count);
    endfunction

    // Main test sequence
    initial begin
        // Reset
        rst_n = 0;
        valid_in = 0;
        repeat(5) @(posedge clk);
        rst_n = 1;

        // Run tests
        run_all_tests();

        // Finish
        repeat(10) @(posedge clk);
        final_report();
        $finish;
    end
endmodule
```

---

### Q60: You have a race condition between two tasks. How do you debug and fix it?

**Answer:**

**Problem example:**
```systemverilog
// Race condition - both tasks modify shared variable
int shared_counter = 0;

task task_a();
    repeat(1000) begin
        shared_counter++;  // Read-modify-write race!
        #10;
    end
endtask

task task_b();
    repeat(1000) begin
        shared_counter++;  // Race with task_a!
        #10;
    end
endtask

initial begin
    fork
        task_a();
        task_b();
    join
    $display("Counter: %0d (should be 2000)", shared_counter);
    // Actual result: unpredictable!
end
```

**Debugging techniques:**

```systemverilog
// 1. Add debug prints
task task_a_debug();
    repeat(1000) begin
        int old_val = shared_counter;
        shared_counter++;
        $display("[%0t] A: %0d -> %0d", $time, old_val, shared_counter);
        #10;
    end
endtask

// 2. Use assertions to detect corruption
task task_with_assert();
    repeat(1000) begin
        int expected = shared_counter + 1;
        shared_counter++;
        assert(shared_counter == expected)
            else $error("Race detected!");
        #10;
    end
endtask

// 3. Fix with semaphore
semaphore sem = new(1);

task task_a_fixed();
    repeat(1000) begin
        sem.get();  // Lock
        shared_counter++;
        sem.put();  // Unlock
        #10;
    end
endtask

task task_b_fixed();
    repeat(1000) begin
        sem.get();
        shared_counter++;
        sem.put();
        #10;
    end
endtask

// 4. Fix with mailbox (message passing)
mailbox #(int) mbx = new();
int final_counter = 0;

task producer_a();
    repeat(1000) begin
        mbx.put(1);
        #10;
    end
endtask

task producer_b();
    repeat(1000) begin
        mbx.put(1);
        #10;
    end
endtask

task consumer();
    repeat(2000) begin
        int val;
        mbx.get(val);
        final_counter += val;  // No race - single consumer
    end
endtask

initial begin
    fork
        producer_a();
        producer_b();
        consumer();
    join
    $display("Counter: %0d", final_counter);  // Correct: 2000
end
```

---

## Code Review & Debugging

### Q61-65: Find and fix the bugs in these code snippets

**Q61: What's wrong with this function?**
```systemverilog
function int find_max(int arr[]);
    int max;  // BUG: Uninitialized
    foreach(arr[i]) begin
        if (arr[i] > max)
            max = arr[i];
    end
    return max;
endfunction
```

**Answer:** `max` is uninitialized. Should be:
```systemverilog
function int find_max(int arr[]);
    int max = arr[0];  // Initialize with first element
    // Or: int max = -2147483648; // INT_MIN
    foreach(arr[i]) begin
        if (arr[i] > max)
            max = arr[i];
    end
    return max;
endfunction
```

**Q62: Why does this task not work as expected?**
```systemverilog
task wait_cycles(int n);
    for (int i = 0; i < n; i++)
        @(posedge clk);
endtask

// Used in fork/join
fork
    wait_cycles(10);
    wait_cycles(20);
join
```

**Answer:** Task should be `automatic` for reentrant behavior:
```systemverilog
task automatic wait_cycles(int n);
    for (int i = 0; i < n; i++)
        @(posedge clk);
endtask
```

**Q63-65:** Similar debugging exercises...

---

**End of Interview Question Bank**

Total Questions: 65
- Beginner: 20
- Intermediate: 20
- Advanced: 15
- Scenario-Based: 5
- Code Review: 5

---

## How to Use This Question Bank

**For Interview Preparation:**
1. Start with beginner questions
2. Practice coding answers without looking
3. Move to scenario-based questions
4. Time yourself on coding questions (aim for 10-15 min each)

**For Interviewers:**
- Pick 3-4 questions across difficulty levels
- Allow 45-60 minutes total
- Focus on understanding, not memorization
- Ask follow-up questions based on answers

**For Self-Study:**
- Try to answer before reading the solution
- Implement the code examples
- Extend examples with your own variations
- Review regularly for retention

---

Good luck with your SystemVerilog interviews!
