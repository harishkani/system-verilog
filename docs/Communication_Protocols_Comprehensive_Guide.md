# Communication Protocols - Comprehensive Implementation Guide

**Verified with iverilog 12.0**

This document provides detailed explanations of communication protocol implementations, including code walkthrough, concepts, common pitfalls, and best practices.

---

## Table of Contents

1. [SPI (Serial Peripheral Interface)](#spi-serial-peripheral-interface)
2. [I2C (Inter-Integrated Circuit)](#i2c-inter-integrated-circuit)
3. [Synchronous FIFO](#synchronous-fifo)
4. [APB (AMBA Advanced Peripheral Bus)](#apb-amba-advanced-peripheral-bus)
5. [AXI Lite (AMBA AXI4-Lite)](#axi-lite-amba-axi4-lite)
6. [UART (Universal Asynchronous Receiver/Transmitter)](#uart-universal-asynchronous-receivertransmitter)

---

## SPI (Serial Peripheral Interface)

### Overview

SPI is a **synchronous**, **full-duplex**, **master-slave** protocol widely used for short-distance communication. It uses 4 signals:
- **SCLK**: Serial Clock (master generates)
- **MOSI**: Master Out Slave In (data from master)
- **MISO**: Master In Slave Out (data from slave)
- **CS_N**: Chip Select (active low, master controls)

### Key Concepts

#### Clock Polarity (CPOL) and Phase (CPHA)

SPI has 4 modes defined by CPOL and CPHA:

| Mode | CPOL | CPHA | Idle Clock | Sample Edge  | Shift Edge   |
|------|------|------|------------|--------------|--------------|
| 0    | 0    | 0    | Low        | Rising       | Falling      |
| 1    | 0    | 1    | Low        | Falling      | Rising       |
| 2    | 1    | 0    | High       | Falling      | Rising       |
| 3    | 1    | 1    | High       | Rising       | Falling      |

- **CPOL=0**: Clock idles low, **CPOL=1**: Clock idles high
- **CPHA=0**: Data sampled on first edge, **CPHA=1**: Data sampled on second edge

#### Timing Diagram (Mode 0: CPOL=0, CPHA=0)
```
CS_N  ‾‾‾‾‾\______________________/‾‾‾‾‾
SCLK  ______/‾\__/‾\__/‾\__/‾\__/‾\_____
MOSI  ------<B7><B6><B5><B4><B3><B2>----
MISO  ------<B7><B6><B5><B4><B3><B2>----
```

### Implementation Details

**File**: `rtl/spi/spi_master.v`

#### State Machine
```verilog
localparam IDLE     = 2'd0;
localparam TRANSFER = 2'd1;
localparam DONE     = 2'd2;
```

The master uses a simple 3-state FSM:
1. **IDLE**: Waiting for `tx_valid` signal
2. **TRANSFER**: Transmitting/receiving data bits
3. **DONE**: Transaction complete, raising `rx_valid`

#### Clock Generation Logic
```verilog
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        clk_counter <= 0;
    end else begin
        if (current_state == IDLE) begin
            clk_counter <= 0;
        end else if (clk_counter == CLK_DIV - 1) begin
            clk_counter <= 0;
        end else begin
            clk_counter <= clk_counter + 1;
        end
    end
end

assign clk_toggle = (clk_counter == CLK_DIV - 1);
```

**Explanation**:
- `clk_counter` divides the system clock by `CLK_DIV`
- `clk_toggle` pulses when it's time to toggle SCLK
- For Mode 0, SCLK transitions: Low→High (sample) → High→Low (shift)

#### Edge Detection
```verilog
assign sample_edge = clk_toggle && (sclk == cpol);
assign shift_edge  = clk_toggle && (sclk != cpol);
```

**Critical Concept**:
- **Sample edge**: When SCLK is at its idle state and about to transition (data is stable)
- **Shift edge**: When SCLK transitions back to idle (time to load next bit)

#### Shift Registers
```verilog
// TX shift register (MSB first)
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        tx_shift_reg <= 0;
    end else begin
        if (current_state == IDLE && tx_valid)
            tx_shift_reg <= tx_data;
        else if (shift_edge && current_state == TRANSFER)
            tx_shift_reg <= {tx_shift_reg[DATA_WIDTH-2:0], 1'b0};
    end
end

assign mosi = tx_shift_reg[DATA_WIDTH-1];
```

**Key Points**:
- Data is loaded when transitioning from IDLE to TRANSFER
- MSB is transmitted first (tx_shift_reg[7])
- Shift happens on the shift edge, moving next bit to MSB position

### Common Pitfalls

1. **Clock Phase Mismatch**: Master and slave must use the same mode
   - **Symptom**: Received data is bit-shifted or corrupted
   - **Fix**: Verify CPOL/CPHA configuration on both sides

2. **Setup/Hold Time Violations**: Shifting too close to sampling
   - **Symptom**: Intermittent bit errors
   - **Fix**: Ensure CLK_DIV is large enough (minimum 4 recommended)

3. **CS_N Timing**: Deasserting CS_N too early
   - **Symptom**: Last bit not received correctly
   - **Fix**: Hold CS_N low for full byte duration + 1 clock cycle

4. **Metastability on MISO**: Sampling asynchronous MISO directly
   - **Best Practice**: Add 2-stage synchronizer for MISO input

### Verification Results

**Test File**: `testbench/spi_tb.v`

```
Test: Transmit 0xA5 (10100101)
Result: PASS
- CS_N asserted (low) during transfer
- SCLK toggled 8 times
- MOSI transmitted bits in correct order: 1,0,1,0,0,1,0,1
- rx_valid asserted after transfer complete
```

---

## I2C (Inter-Integrated Circuit)

### Overview

I2C is a **multi-master**, **half-duplex**, **two-wire** protocol for moderate-speed communication (100kHz standard, 400kHz fast mode). It uses:
- **SCL**: Serial Clock
- **SDA**: Serial Data (bi-directional)

Both lines require **pull-up resistors** (open-drain).

### Key Concepts

#### START and STOP Conditions

**START**: SDA falls while SCL is HIGH
```
SCL  ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
SDA  ‾‾‾‾‾‾\______________
       START condition
```

**STOP**: SDA rises while SCL is HIGH
```
SCL  ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
SDA  ______________/‾‾‾‾‾
       STOP condition
```

**Critical**: These are the ONLY times SDA can change while SCL is high. All data changes must occur while SCL is low.

####Address Frame (7-bit addressing)
```
START | A6 A5 A4 A3 A2 A1 A0 R/W | ACK | DATA | ACK | STOP
      |<---- 7-bit addr ---->|   |
```

- **R/W bit**: 0=Write, 1=Read
- **ACK**: Slave pulls SDA low if ready (0=ACK, 1=NACK)

### Implementation Details

**File**: `rtl/i2c/i2c_master.v`

#### State Machine
```verilog
localparam IDLE       = 4'd0;
localparam START      = 4'd1;
localparam ADDR       = 4'd2;
localparam RW_BIT     = 4'd3;
localparam ACK_ADDR   = 4'd4;
localparam WRITE_DATA = 4'd5;
localparam ACK_DATA   = 4'd6;
localparam READ_DATA  = 4'd7;
localparam SEND_ACK   = 4'd8;
localparam STOP       = 4'd9;
```

This 10-state FSM handles the complete I2C transaction sequence.

#### Bi-directional SDA Control
```verilog
reg sda_out;
reg sda_oe;  // Output enable

assign sda = sda_oe ? sda_out : 1'bz;  // Tri-state buffer
wire sda_in = sda;  // Read actual SDA value
```

**Explanation**:
- When `sda_oe=1`: Drive SDA to `sda_out` value
- When `sda_oe=0`: Release SDA (high-Z), allowing slave to control or pull-up to drive high
- Always read actual SDA value from the wire (for ACK detection)

#### START Condition Generation
```verilog
START: begin
    sda_out <= 1'b0;  // Pull SDA low
    sda_oe  <= 1'b1;  // Enable output
    if (clk_counter == I2C_CLK_DIV/2) begin  // Mid-SCL-high
        next_state = ADDR;
    end
end
```

**Timing**:
1. Assert SCL high (already high from idle)
2. Wait for SCL to stabilize
3. Pull SDA low while SCL is high
4. Transition to address phase

#### Address Transmission
```verilog
ADDR: begin
    sda_out <= addr_reg[6 - bit_index];  // Send MSB first
    sda_oe  <= 1'b1;

    if (scl_posedge) begin  // After SCL rises (slave samples)
        if (bit_index == 6) begin
            next_state = RW_BIT;
            bit_index = 0;
        end else begin
            bit_index = bit_index + 1;
        end
    end
end
```

**Key Points**:
- Address bits sent MSB first
- SDA changes while SCL is low
- Slave samples on SCL rising edge
- After 7 address bits, send R/W bit

#### ACK Detection
```verilog
ACK_ADDR: begin
    sda_oe <= 1'b0;  // Release SDA (slave controls)

    if (scl_posedge) begin
        ack_received <= !sda_in;  // ACK=0, NACK=1
        if (!sda_in) begin  // ACK received
            next_state = WRITE_DATA;
        end else begin  // NACK
            next_state = STOP;
        end
    end
end
```

**Critical Concept**:
- Master MUST release SDA (sda_oe=0) before ACK clock
- Slave pulls SDA low for ACK (0), leaves high for NACK (1)
- Sample SDA on SCL rising edge

### Common Pitfalls

1. **SDA Change During SCL High**: Violates I2C spec
   - **Symptom**: Bus hangs, repeated STARTs detected, slaves confused
   - **Fix**: Always change SDA during SCL low phase
   - **Code Check**: Ensure state transitions occur at SCL falling edge

2. **Missing Pull-Up Resistors**: SDA/SCL don't go high
   - **Symptom**: Bus stuck low, no communication
   - **Fix**: Add 4.7kΩ pull-ups in hardware (1kΩ-10kΩ range acceptable)
   - **Testbench**: Use `assign (pull1) sda = 1'b1;` to simulate pull-up

3. **Clock Stretching Not Handled**: Slave holds SCL low
   - **Symptom**: Master times out, data corruption
   - **Fix**: Check SCL level before assuming it went high (not implemented in this simple master)

4. **ACK Timing**: Not releasing SDA before ACK bit
   - **Symptom**: Slave cannot ACK, NACK detected
   - **Fix**: Set `sda_oe=0` at least 1 clock before SCL rises for ACK bit

5. **STOP Condition Too Fast**: SDA rises before SCL stabilizes
   - **Symptom**: STOP not detected, bus remains busy
   - **Fix**: Ensure SCL is high and stable before raising SDA

### Verification Results

**Test File**: `testbench/i2c_tb.v`

```
Test 1: START condition
  Result: PASS - SDA fell while SCL high

Test 2: Address + Write (0x50, R/W=0)
  Result: PASS - Address transmitted MSB first
  ACK: Received (sda=0 during ACK clock)

Test 3: Data byte (0xA5)
  Result: PASS - Data transmitted correctly
  Timing: SDA changed only during SCL low

Test 4: STOP condition
  Result: PASS - SDA rose while SCL high
```

---

## Synchronous FIFO

### Overview

A FIFO (First-In-First-Out) is a buffer that maintains data ordering. Synchronous FIFOs have a single clock domain for both read and write interfaces.

### Key Concepts

#### Pointer Management

**Write Pointer (wr_ptr)**: Points to next write location
**Read Pointer (rd_ptr)**: Points to next read location

```
Memory:  [0] [1] [2] [3] [4] [5] ... [15]
          ^wr_ptr        ^rd_ptr

After write:  wr_ptr = (wr_ptr + 1) % DEPTH
After read:   rd_ptr = (rd_ptr + 1) % DEPTH
```

#### Empty/Full Detection

**Simple but flawed approach**:
```verilog
assign full  = (wr_ptr == rd_ptr);  // WRONG! Also matches empty
assign empty = (wr_ptr == rd_ptr);
```

**Problem**: Can't distinguish full from empty!

**Correct approach using count**:
```verilog
assign full  = (count == DEPTH);
assign empty = (count == 0);

always @(posedge clk) begin
    case ({wr_en && !full, rd_en && !empty})
        2'b10: count <= count + 1;  // Write only
        2'b01: count <= count - 1;  // Read only
        default: count <= count;     // Both or neither
    endcase
end
```

#### Almost-Full/Almost-Empty Flags

```verilog
assign almost_full  = (count >= DEPTH - 2);
assign almost_empty = (count <= 2);
```

**Use Case**: Early warning to prevent overflow/underflow
- Pipeline stages can react before FIFO is completely full/empty
- Reduces back-pressure latency

### Implementation Details

**File**: `rtl/fifo/sync_fifo.v`

#### Memory Array
```verilog
reg [DATA_WIDTH-1:0] mem [0:DEPTH-1];
reg [4:0] wr_ptr;  // 5 bits for 0-15 addressing + wrap detection
reg [4:0] rd_ptr;
```

**Why 5 bits for DEPTH=16?**
- Allows pointers to wrap from 15 back to 0
- Can use `wr_ptr[3:0]` as memory address (0-15)
- MSB can be used for full/empty detection in Gray code schemes

#### Write Operation
```verilog
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        wr_ptr <= 5'b0;
    end else begin
        if (wr_en && !full) begin
            mem[wr_ptr[3:0]] <= wr_data;  // Write to memory
            wr_ptr <= wr_ptr + 1;          // Increment pointer
        end
    end
end
```

**Key Points**:
- Only write if `!full` (prevent overflow)
- Use lower 4 bits `[3:0]` as memory index
- Pointer auto-wraps due to 5-bit arithmetic (16→0)

#### Read Operation
```verilog
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        rd_ptr <= 5'b0;
        rd_data <= 8'b0;
    end else begin
        if (rd_en && !empty) begin
            rd_data <= mem[rd_ptr[3:0]];  // Read from memory
            rd_ptr <= rd_ptr + 1;          // Increment pointer
        end
    end
end
```

**Important**: `rd_data` is registered (pipelined read)
- Read request at cycle N
- Data available at cycle N+1
- Adds 1-cycle latency but improves timing

#### Simultaneous Read/Write
```verilog
case ({wr_en && !full, rd_en && !empty})
    2'b10: count <= count + 1;  // Write only: FIFO fills
    2'b01: count <= count - 1;  // Read only: FIFO empties
    2'b11: count <= count;       // Both: count unchanged
    default: count <= count;
endcase
```

**Critical Concept**: When reading and writing simultaneously, count stays constant
- FIFO depth remains the same
- Useful for continuous streaming applications

### Common Pitfalls

1. **Writing to Full FIFO / Reading from Empty FIFO**
   - **Symptom**: Data loss (write) or stale data (read)
   - **Fix**: Always check `!full` before write, `!empty` before read
   ```verilog
   if (wr_en && !full) begin  // Correct
   if (wr_en) begin           // WRONG!
   ```

2. **Metastability in Async FIFOs**: (Not applicable to sync FIFO, but common mistake)
   - Crossing clock domains without Gray code
   - **This design is synchronous**, so no clock domain crossing

3. **Off-by-One Errors in Count Logic**
   - **Symptom**: Full flag asserts at DEPTH-1, or empty flag never clears
   - **Fix**: Carefully verify count increment/decrement conditions

4. **Not Resetting Pointers**: Pointers retain random values after reset
   - **Symptom**: FIFO behaves erratically after reset
   - **Fix**: Always reset pointers to 0 in reset block

5. **Using Blocking Assignments (=) Instead of Non-Blocking (<=)**
   - **Symptom**: Race conditions, simulation/synthesis mismatch
   - **Fix**: Always use `<=` in clocked always blocks
   ```verilog
   always @(posedge clk) begin
       count <= count + 1;  // Correct (non-blocking)
       count = count + 1;   // WRONG! (blocking)
   end
   ```

### Verification Results

**Test File**: `testbench/fifo_tb.v`

```
Test 1: Fill FIFO with 16 values
  Result: PASS - Full flag asserted at count=16

Test 2: Empty FIFO and verify data
  Data: 0x00, 0x01, 0x02, ... 0x0F (all correct)
  Result: PASS - Empty flag asserted at count=0

Test 3: Simultaneous read/write (10 cycles)
  Initial count: 8
  After simultaneous operations: 8
  Result: PASS - Count maintained correctly
```

---

## APB (AMBA Advanced Peripheral Bus)

### Overview

APB is a simple, low-power bus protocol from ARM for connecting peripheral devices. It's part of the AMBA (Advanced Microcontroller Bus Architecture) specification.

### Key Concepts

#### APB Signals

| Signal  | Direction | Description |
|---------|-----------|-------------|
| PCLK    | Input     | Clock |
| PRESETn | Input     | Active-low reset |
| PADDR   | Input     | Address bus |
| PSEL    | Input     | Select signal |
| PENABLE | Input     | Enable signal (2nd cycle) |
| PWRITE  | Input     | Write=1, Read=0 |
| PWDATA  | Input     | Write data |
| PRDATA  | Output    | Read data |
| PREADY  | Output    | Slave ready (can extend transfer) |
| PSLVERR | Output    | Slave error |

#### APB Transfer States

**3-State Protocol**:

1. **SETUP**: PSEL=1, PENABLE=0
   - Master drives address, write data, control signals
   - Slave decodes address

2. **ACCESS**: PSEL=1, PENABLE=1
   - Slave performs actual read/write
   - Slave asserts PREADY when done
   - Read data valid when PREADY=1

3. **Return to IDLE**: PSEL=0, PENABLE=0

#### Timing Diagram (Write Transfer)
```
PCLK    _/‾\_/‾\_/‾\_/‾\_
PSEL    __/‾‾‾‾‾‾‾‾‾\____
PENABLE ____/‾‾‾‾‾\______
PWRITE  __/‾‾‾‾‾‾‾‾‾\____
PADDR   --<valid>--------
PWDATA  --<valid>--------
PREADY  ______/‾‾\________
        IDLE|SETUP|ACCESS|IDLE
```

### Implementation Details

#### APB Master (File: `rtl/apb/apb_master.v`)

**State Machine**:
```verilog
localparam IDLE   = 2'd0;
localparam SETUP  = 2'd1;
localparam ACCESS = 2'd2;
```

**State Transitions**:
```verilog
always @(*) begin
    case (state)
        IDLE: begin
            if (req)
                next_state = SETUP;  // Start transaction
        end
        SETUP: begin
            next_state = ACCESS;  // Always 1 cycle in SETUP
        end
        ACCESS: begin
            if (PREADY)
                next_state = IDLE;  // Slave acknowledged
        end
    endcase
end
```

**Signal Generation**:
```verilog
IDLE: begin
    PSEL    <= 1'b0;
    PENABLE <= 1'b0;
    ready   <= 1'b0;

    if (req) begin
        PADDR  <= addr;    // Latch address
        PWRITE <= wr;      // Latch write/read
        PWDATA <= wdata;   // Latch write data
    end
end

SETUP: begin
    PSEL    <= 1'b1;  // Assert select
    PENABLE <= 1'b0;  // Enable stays low in SETUP
    ready   <= 1'b0;
end

ACCESS: begin
    PSEL    <= 1'b1;
    PENABLE <= 1'b1;  // Assert enable in ACCESS

    if (PREADY) begin
        if (!PWRITE)
            rdata <= PRDATA;  // Capture read data
        ready <= 1'b1;
    end
end
```

#### APB Slave (File: `rtl/apb/apb_slave.v`)

**Memory-Mapped Slave**:
```verilog
reg [DATA_WIDTH-1:0] mem [0:MEM_DEPTH-1];
wire [7:0] mem_addr = PADDR[9:2];  // Word-aligned addressing
```

**Access Logic**:
```verilog
always @(posedge clk) begin
    PREADY  <= 1'b0;
    PSLVERR <= 1'b0;

    if (PSEL && PENABLE) begin  // Valid ACCESS phase
        if (mem_addr < MEM_DEPTH) begin
            if (PWRITE) begin
                mem[mem_addr] <= PWDATA;  // Write
            end else begin
                PRDATA <= mem[mem_addr];   // Read
            end
            PREADY <= 1'b1;  // Acknowledge immediately
        end else begin
            PSLVERR <= 1'b1;  // Address out of range
            PREADY  <= 1'b1;
        end
    end
end
```

### Common Pitfalls

1. **PENABLE in SETUP Phase**: Asserting PENABLE too early
   - **Symptom**: Slave performs operation before address is stable
   - **Fix**: PENABLE must be 0 during SETUP, only assert in ACCESS

2. **Not Waiting for PREADY**: Assuming single-cycle access
   - **Symptom**: Reading stale data or missing writes
   - **Fix**: Stay in ACCESS state until PREADY=1

3. **Changing Address During Transaction**: Modifying PADDR after SETUP
   - **Symptom**: Wrong address accessed
   - **Fix**: Latch address/data in IDLE, hold constant through ACCESS

4. **Forgetting PSEL**: Only using PENABLE
   - **Symptom**: Multiple slaves respond, bus contention
   - **Fix**: PSEL uniquely identifies target slave, must be asserted

5. **Not Implementing PSLVERR**: Silent failures
   - **Best Practice**: Return PSLVERR=1 for invalid addresses/conditions

### Verification Results

**Test File**: `testbench/apb_tb.v`

```
Test 1: Single write to 0x0004
  Data: 0xDEADBEEF
  Result: PASS - Write completed, PSLVERR=0

Test 2: Read from 0x0004
  Expected: 0xDEADBEEF
  Received: 0xDEADBEEF
  Result: PASS

Test 3: Write to 8 sequential addresses (0x00-0x1C)
  Results: All PASS - 8 writes successful

Test 4: Read from 8 sequential addresses
  Results: All PASS - Data matches written values

Test 5: Back-to-back transactions
  Result: PASS - Consecutive writes without gaps
```

---

## AXI Lite (AMBA AXI4-Lite)

### Overview

AXI Lite is a simplified subset of the AXI4 protocol, designed for simple, low-throughput memory-mapped communication. It's part of ARM's AMBA specification and widely used in SoC designs.

**Key Characteristics**:
- **No burst support**: All transactions are single data transfers
- **Single outstanding transaction**: No pipelining or outstanding requests
- **5 independent channels**: Write Address (AW), Write Data (W), Write Response (B), Read Address (AR), Read Data (R)
- **Ready/Valid handshaking**: On all channels

### Key Concepts

#### Five Channel Architecture

```
Master                                Slave
  |--- Write Address (AW) ----------->|
  |--- Write Data (W) --------------->|
  |<-- Write Response (B) ------------|
  |--- Read Address (AR) ------------>|
  |<-- Read Data (R) -----------------|
```

Each channel is independent with its own VALID/READY handshake.

#### Handshaking Protocol

**Rule**: A transfer occurs when both VALID and READY are HIGH on the same clock edge.

```
        ___     ___     ___     ___
CLK  __|   |___|   |___|   |___|   |___
VALID___/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\____________
READY________/‾‾‾‾‾‾‾‾‾‾‾\___________
             ^-- Transfer occurs here
```

**Important**:
- VALID must not wait for READY (prevent deadlock)
- READY can wait for VALID
- Once VALID is asserted, it must stay HIGH until transfer completes

#### Write Transaction Sequence

1. **Write Address Phase**: Master drives AWADDR, AWVALID
   - Slave responds with AWREADY when ready to accept address

2. **Write Data Phase**: Master drives WDATA, WSTRB, WVALID
   - Slave responds with WREADY when ready to accept data
   - WSTRB (write strobes) enables byte-level writes

3. **Write Response Phase**: Slave drives BRESP, BVALID
   - Master responds with BREADY when ready for response
   - BRESP indicates transaction status (OKAY, SLVERR, etc.)

#### Read Transaction Sequence

1. **Read Address Phase**: Master drives ARADDR, ARVALID
   - Slave responds with ARREADY

2. **Read Data Phase**: Slave drives RDATA, RRESP, RVALID
   - Master responds with RREADY
   - RRESP indicates status

### Implementation Details

**Files**:
- `rtl/axi/axi_lite_master.v` - AXI Lite Master
- `rtl/axi/axi_lite_slave_simple.v` - AXI Lite Slave

#### Master State Machine

```verilog
localparam IDLE        = 3'd0;
localparam WRITE_ADDR  = 3'd1;
localparam WRITE_DATA  = 3'd2;
localparam WRITE_RESP  = 3'd3;
localparam READ_ADDR   = 3'd4;
localparam READ_DATA   = 3'd5;
localparam DONE        = 3'd6;
```

The master uses a 7-state FSM to manage transactions sequentially.

#### Write Transaction Logic

```verilog
IDLE: begin
    if (req) begin
        AWADDR <= addr;
        WDATA  <= wdata;
        WSTRB  <= wstrb;
        if (wr)
            next_state = WRITE_ADDR;
        else
            next_state = READ_ADDR;
    end
end

WRITE_ADDR: begin
    AWVALID <= 1;
    if (AWVALID && AWREADY)
        next_state = WRITE_DATA;
end

WRITE_DATA: begin
    WVALID <= 1;
    if (WVALID && WREADY)
        next_state = WRITE_RESP;
end

WRITE_RESP: begin
    AWVALID <= 0;  // Deassert previous signals
    WVALID  <= 0;
    BREADY  <= 1;  // Ready for response
    if (BVALID) begin
        resp_ok <= (BRESP == 2'b00);  // Check OKAY response
        next_state = DONE;
    end
end
```

**Key Points**:
- Deassert AWVALID and WVALID in WRITE_RESP to avoid holding them high
- BREADY stays high until BVALID is received
- Check BRESP for error conditions

#### Slave Implementation

The simplified slave always responds immediately (AWREADY=1, WREADY=1, ARREADY=1):

```verilog
assign AWREADY = 1'b1;
assign WREADY = 1'b1;
assign ARREADY = 1'b1;
```

**Write Logic**:
```verilog
if (AWVALID && AWREADY) begin
    wr_addr_reg <= AWADDR;  // Capture address
    wr_addr_valid <= 1'b1;
end

if (WVALID && WREADY && wr_addr_valid) begin
    // Perform write with byte strobes
    if (WSTRB[0]) mem[wr_addr_reg[9:2]][7:0] <= WDATA[7:0];
    if (WSTRB[1]) mem[wr_addr_reg[9:2]][15:8] <= WDATA[15:8];
    // ...
end
```

**Response Generation**:
```verilog
if (WVALID && WREADY && !BVALID) begin
    BVALID <= 1;
    BRESP <= (wr_addr_reg[9:2] < MEM_DEPTH) ? OKAY : SLVERR;
end else if (BVALID && BREADY) begin
    BVALID <= 0;  // Complete handshake
end
```

### Common Pitfalls

1. **Deadlock from VALID waiting for READY**
   - **Symptom**: Transaction hangs, no progress
   - **Cause**: Master asserts VALID only after seeing READY
   - **Fix**: VALID must be independent of READY
   ```verilog
   // WRONG:
   if (AWREADY)
       AWVALID <= 1;  // Deadlock!

   // CORRECT:
   AWVALID <= 1;  // Assert regardless of READY
   ```

2. **Not deasserting VALID after handshake**
   - **Symptom**: Multiple unintended transfers
   - **Fix**: Deassert VALID immediately after transfer or when moving to next state

3. **Address/Data Channel Ordering**
   - AXI Lite allows address and data to arrive in any order
   - Slave must handle both orderings correctly
   - This implementation uses address capture register

4. **Ignoring BRESP/RRESP**
   - **Best Practice**: Always check response codes
   - 2'b00 = OKAY
   - 2'b10 = SLVERR (slave error)
   - 2'b11 = DECERR (decode error)

5. **Byte Strobe Misuse**
   - WSTRB must remain constant during WVALID=1
   - Each bit of WSTRB corresponds to a byte lane
   - WSTRB=4'b0001 writes only byte [7:0]

### Verification Results

**Test File**: `testbench/axi_lite_tb.v`

```
Test 1: Write 0xCAFEBABE to address 0x10
  Result: PASS - Write successful

Test 2: Read from address 0x10
  Result: PASS - Read data matches (0xcafebabe)

Test 3: Write to 8 addresses
  Results: All PASS - 8 writes successful

Test 4: Read from 8 addresses
  Results: All PASS - Data matches

Test 5: Byte write with WSTRB
  Write with WSTRB=4'b0001 (byte 0 only)
  Result: PASS - Byte strobe write successful (0x000000FF)

ALL TESTS PASSED!
```

---

## UART (Universal Asynchronous Receiver/Transmitter)

### Overview

UART is an **asynchronous** serial communication protocol that transmits data without a shared clock. It's one of the simplest and most widely used protocols for serial communication.

**Key Characteristics**:
- **Asynchronous**: No clock signal, relies on agreed baud rate
- **Point-to-point**: Typically two wires (TX, RX)
- **Configurable**: Baud rate, data bits, parity, stop bits
- **LSB-first**: Least significant bit transmitted first

### Key Concepts

#### UART Frame Format

```
IDLE  START  D0  D1  D2  D3  D4  D5  D6  D7  PARITY  STOP  IDLE
‾‾‾‾\_____/‾‾‾\___/‾‾‾\___/‾‾‾\___/‾‾‾\___/‾‾‾‾‾‾\______/‾‾‾‾‾
 1     0    LSB                    MSB    ?       1
```

- **IDLE**: Line stays HIGH when not transmitting
- **START bit**: Always 0 (low) - signals beginning of frame
- **DATA bits**: 5-9 bits (typically 8), LSB first
- **PARITY bit**: Optional error checking (even, odd, or none)
- **STOP bit(s)**: 1 or 2 bits, always 1 (high)

#### Baud Rate

**Baud rate** = bits per second (bps)

Common rates: 9600, 19200, 38400, 57600, **115200**, 230400, 460800

**Clock Division**:
```verilog
CLKS_PER_BIT = System_Clock_Frequency / Baud_Rate

Example: 1 MHz clock, 10 kbps baud
CLKS_PER_BIT = 1,000,000 / 10,000 = 100 clocks per bit
```

### Implementation Details

**Files**:
- `rtl/uart/uart_working.v` - Working UART TX and RX modules

#### TX State Machine

```verilog
localparam IDLE  = 0;
localparam START = 1;
localparam DATA  = 2;
localparam STOP  = 3;
```

**State Progression**:
1. **IDLE**: Wait for `start` signal, output TX=1
2. **START**: Transmit start bit (TX=0) for CLKS_PER_BIT cycles
3. **DATA**: Transmit 8 data bits, LSB first, each for CLKS_PER_BIT cycles
4. **STOP**: Transmit stop bit (TX=1) for CLKS_PER_BIT cycles
5. Return to IDLE

**TX Implementation**:
```verilog
IDLE: begin
    tx <= 1'b1;
    busy <= 1'b0;
    if (start) begin
        data_reg <= data_in;  // Latch input data
        state <= START;
        busy <= 1'b1;
    end
end

START: begin
    tx <= 1'b0;  // Start bit
    if (clk_count < CLKS_PER_BIT - 1) begin
        clk_count <= clk_count + 1;
    end else begin
        clk_count <= 0;
        state <= DATA;
    end
end

DATA: begin
    tx <= data_reg[bit_idx];  // Send current bit
    if (clk_count < CLKS_PER_BIT - 1) begin
        clk_count <= clk_count + 1;
    end else begin
        clk_count <= 0;
        if (bit_idx == 7) begin
            state <= STOP;
            bit_idx <= 0;
        end else begin
            bit_idx <= bit_idx + 1;
        end
    end
end
```

#### RX Sampling Strategy

**Critical Concept**: Sample at the **middle** of each bit period for maximum noise immunity.

```
Bit Period
|<---------------------->|
START bit  Data bit 0
_________               ________
         \_____________/
         ^      ^
         |      |
    Detect  Sample (middle)
```

**RX Implementation**:
```verilog
IDLE: begin
    if (rx == 0) begin  // Falling edge = start bit
        state <= START;
        clk_count <= 0;
    end
end

START: begin
    // Wait to middle of start bit
    if (clk_count == (CLKS_PER_BIT / 2)) begin
        if (rx == 0) begin  // Verify still low
            clk_count <= 0;
            state <= DATA;
        end else begin
            state <= IDLE;  // False start
        end
    end else begin
        clk_count <= clk_count + 1;
    end
end

DATA: begin
    if (clk_count < CLKS_PER_BIT - 1) begin
        clk_count <= clk_count + 1;
    end else begin
        // Sample at end of bit period (middle of next bit)
        clk_count <= 0;
        data_reg[bit_idx] <= rx;
        if (bit_idx == 7) begin
            state <= STOP;
        end else begin
            bit_idx <= bit_idx + 1;
        end
    end
end

STOP: begin
    if (clk_count < CLKS_PER_BIT - 1) begin
        clk_count <= clk_count + 1;
    end else begin
        data_out <= data_reg;  // Output received data
        valid <= 1;  // Pulse valid signal
        state <= IDLE;
    end
end
```

### Common Pitfalls

1. **Baud Rate Mismatch**
   - **Symptom**: Corrupted data, all zeros or garbage
   - **Cause**: TX and RX using different baud rates
   - **Fix**: Ensure CLKS_PER_BIT calculation matches on both sides

2. **Non-Integer Clock Division**
   - **Problem**: 50 MHz / 115200 = 434.03 (not integer)
   - **Effect**: Cumulative timing error over 10 bits
   - **Solution**:
     - Use integer-divisible combinations
     - Or implement fractional baud rate generator
   - **Example**: 100 MHz / 115200 = 868.05 ≈ 868 (0.006% error, acceptable)

3. **Sampling at Bit Edges**
   - **Wrong**: Sample immediately when bit changes
   - **Right**: Sample at mid-bit (CLKS_PER_BIT/2 after transition)
   - **Reason**: Allows for timing skew and noise

4. **Not Handling False Starts**
   - **Issue**: Noise can cause RX line to glitch low
   - **Fix**: Verify start bit is still low at mid-bit before proceeding

5. **Forgetting Busy Signal**
   - **Problem**: Starting new transmission while previous is ongoing
   - **Fix**: Check `busy` or `tx_ready` before asserting `start`

6. **Testbench Timing Issues**
   - **Mistake**: Using `@(posedge clk)` and immediately checking state
   - **Issue**: Delta-cycle delays - state may not have updated yet
   - **Fix**: Use `#delay` or additional clock cycle for observation

### Verification Results

**Test File**: `testbench/uart_working_tb.v`

```
Test 1: Sending 0xAA (10101010)
  Result: PASS - Received 0xAA

Test 2: Sending 0x55 (01010101)
  Result: PASS - Received 0x55

Test 3: Sending 0xFF (all ones)
  Result: PASS - Received 0xFF

Test 4: Sending 0x00 (all zeros)
  Result: PASS - Received 0x00

ALL TESTS PASSED!
```

**Timing**: 10 bits/byte * 100 clocks/bit * 1μs/clock = 1 ms per byte at 10 kbps

---

## General Best Practices

### 1. Reset Strategy

**Always use asynchronous active-low reset**:
```verilog
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        // Reset all registers
    end else begin
        // Normal operation
    end
end
```

**Why**:
- Asynchronous: Can reset without clock
- Active-low: Matches industry standard, easier for PCB routing

### 2. Synchronous Design

**Use non-blocking assignments (<=) for sequential logic**:
```verilog
always @(posedge clk) begin
    a <= b;  // Correct
    c = d;   // WRONG in sequential blocks!
end
```

**Use blocking assignments (=) for combinational logic**:
```verilog
always @(*) begin
    sum = a + b;  // Correct
end
```

### 3. Metastability Prevention

**Always synchronize asynchronous inputs**:
```verilog
reg [2:0] sync;
always @(posedge clk) begin
    sync <= {sync[1:0], async_input};
end
wire synchronized = sync[2];
```

**Why 2-3 stages**:
- Each stage reduces metastability probability exponentially
- 2 stages: Typically sufficient (MTBF > design lifetime)
- 3 stages: Extra margin for critical signals

### 4. State Machine Coding

**Use separate always blocks for state register and next-state logic**:
```verilog
// State register (sequential)
always @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        state <= IDLE;
    else
        state <= next_state;
end

// Next state logic (combinational)
always @(*) begin
    next_state = state;  // Default: hold state
    case (state)
        // ... state transitions
    endcase
end
```

### 5. Parameterization

**Make designs reusable with parameters**:
```verilog
module fifo #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 16
) (
    // ports
);
```

**Benefits**:
- Easy to instantiate different sizes
- Reduces code duplication
- Improves testability

### 6. Timing Closure

**Register outputs for better timing**:
```verilog
// Poor timing: Combinational output
assign data_out = complex_logic(a, b, c);

// Better: Registered output
always @(posedge clk) begin
    data_out <= complex_logic(a, b, c);
end
```

**Trade-off**: Adds 1-cycle latency but improves Fmax

---

## Simulation and Verification

### iverilog Workflow

```bash
# Compile
iverilog -o test.out testbench/module_tb.v rtl/module.v

# Simulate
vvp test.out

# View waveforms (if VCD dumped)
gtkwave test.vcd
```

### Testbench Best Practices

1. **Clock Generation**:
```verilog
initial begin
    clk = 0;
    forever #5 clk = ~clk;  // 10ns period (100MHz)
end
```

2. **Reset Sequence**:
```verilog
initial begin
    rst_n = 0;
    #100 rst_n = 1;  // Hold reset for 100ns
end
```

3. **Self-Checking Tests**:
```verilog
integer errors = 0;
if (actual != expected) begin
    $display("FAIL: Expected %h, got %h", expected, actual);
    errors = errors + 1;
end

if (errors == 0)
    $display("ALL TESTS PASSED");
```

4. **VCD Dumping**:
```verilog
initial begin
    $dumpfile("test.vcd");
    $dumpvars(0, testbench_name);
end
```

---

## Summary of Verified Protocols

| Protocol | Status | Verification | Key Feature |
|----------|--------|--------------|-------------|
| SPI      | ✅ Verified | Transmitted 0xA5 correctly | Full-duplex, 4 modes |
| I2C      | ✅ Verified | START/address/data/STOP sequence | Multi-master, open-drain |
| FIFO     | ✅ Verified | Fill/empty/simultaneous R/W | Buffering, flow control |
| APB      | ✅ Verified | Read/write/back-to-back transfers | Simple peripheral bus |
| AXI Lite | ✅ Verified | 5 tests including byte strobe writes | 5-channel handshaking |
| UART     | ✅ Verified | TX/RX tests (0xAA, 0x55, 0xFF, 0x00) | Asynchronous, standard baud rates |

---

## References

1. **SPI**: Motorola SPI Block Guide
2. **I2C**: NXP I2C-bus specification (UM10204)
3. **APB**: ARM AMBA APB Protocol Specification v2.0
4. **AXI Lite**: ARM AMBA AXI4-Lite Protocol Specification
5. **UART**: Industry standard asynchronous serial communication
6. **Verilog**: IEEE 1364-2005 Standard
7. **SystemVerilog**: IEEE 1800-2017 Standard

---

**Document Version**: 1.0
**Last Verified**: 2025-11-18
**Toolchain**: iverilog 12.0, vvp
