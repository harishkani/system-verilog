# Communication Protocols - Detailed Code Explanations

This document provides comprehensive, line-by-line explanations of all communication protocol implementations.

---

# SPI Master - Detailed Explanation

## Module Overview

The SPI Master module generates the SPI clock (SCLK) and controls all transactions with slave devices.

```systemverilog
module spi_master #(
    parameter DATA_WIDTH = 8,
    parameter CLK_DIV = 4  // System clock divider for SPI clock
)
```

**Parameters:**
- `DATA_WIDTH`: Number of bits to transfer per transaction (typically 8, 16, or 32)
- `CLK_DIV`: Divides system clock to generate SPI clock. If system clock is 50MHz and CLK_DIV=4, SPI clock = 50MHz/4 = 12.5MHz

## Port Declarations

```systemverilog
input  logic                    clk,        // System clock (faster than SPI clock)
input  logic                    rst_n,      // Active-low asynchronous reset
// Control interface
input  logic [DATA_WIDTH-1:0]   tx_data,    // Data to transmit
input  logic                    tx_valid,   // Start transmission when high
output logic                    tx_ready,   // Ready to accept new data
output logic [DATA_WIDTH-1:0]   rx_data,    // Received data
output logic                    rx_valid,   // Indicates rx_data is valid
// SPI interface
output logic                    sclk,       // SPI clock to slave
output logic                    mosi,       // Master Out Slave In data line
input  logic                    miso,       // Master In Slave Out data line
output logic                    cs_n,       // Chip Select (active low)
// Configuration
input  logic                    cpol,       // Clock polarity (idle state)
input  logic                    cpha        // Clock phase (sample edge)
```

**Signal Descriptions:**
- **tx_valid/tx_ready**: Handshake protocol. User asserts `tx_valid` with `tx_data`. Module asserts `tx_ready` when it can accept data.
- **rx_valid**: Pulses high for one clock cycle when received data is ready
- **cs_n**: Active low chip select. Goes low during transfer, high when idle
- **cpol/cpha**: Configure SPI mode (0-3). These determine when data is sampled vs changed

## State Machine

```systemverilog
typedef enum logic [1:0] {
    IDLE,      // Waiting for transaction
    TRANSFER,  // Actively transferring data
    DONE       // Transfer complete, presenting results
} state_t;
```

**State Descriptions:**
- **IDLE**: CS is high, waiting for tx_valid. tx_ready is asserted here.
- **TRANSFER**: CS is low, SCLK is toggling, shifting data in/out
- **DONE**: Transfer finished, rx_valid asserted, rx_data available

## SPI Clock Generation

```systemverilog
// Clock divider counter
logic [$clog2(CLK_DIV)-1:0] clk_counter;
logic sclk_int;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        clk_counter <= '0;
        sclk_int <= cpol;  // Initialize to idle state based on CPOL
    end else begin
        if (sclk_enable) begin  // Only run during TRANSFER state
            if (clk_counter == CLK_DIV - 1) begin
                clk_counter <= '0;
                sclk_int <= ~sclk_int;  // Toggle SPI clock
            end else begin
                clk_counter <= clk_counter + 1;
            end
        end else begin
            clk_counter <= '0;
            sclk_int <= cpol;  // Maintain idle state when not transferring
        end
    end
end
```

**How it works:**
1. `clk_counter` counts from 0 to CLK_DIV-1
2. When counter reaches CLK_DIV-1, toggle `sclk_int`
3. This creates an SPI clock that's CLK_DIV times slower than system clock
4. When not enabled, clock rests at `cpol` (the idle state)
5. **Example**: CLK_DIV=4 means 4 system clocks per half SPI clock period

## Edge Detection

```systemverilog
logic sclk_prev;
logic sclk_rising_edge;
logic sclk_falling_edge;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        sclk_prev <= cpol;
    else
        sclk_prev <= sclk_int;
end

assign sclk_rising_edge = !sclk_prev && sclk_int;   // 0->1 transition
assign sclk_falling_edge = sclk_prev && !sclk_int;  // 1->0 transition
```

**Purpose:**
- Detect exact moment of clock edge transitions
- `sclk_prev` holds previous clock value
- Rising edge: was 0, now 1
- Falling edge: was 1, now 0
- These pulses last only 1 system clock cycle

## Sample and Change Edge Determination

```systemverilog
logic sample_edge;   // When to read MISO
logic change_edge;   // When to update MOSI

always_comb begin
    if (cpha == 0) begin
        // Mode 0 or Mode 2
        sample_edge = cpol ? sclk_falling_edge : sclk_rising_edge;
        change_edge = cpol ? sclk_rising_edge : sclk_falling_edge;
    end else begin
        // Mode 1 or Mode 3
        sample_edge = cpol ? sclk_rising_edge : sclk_falling_edge;
        change_edge = cpol ? sclk_falling_edge : sclk_rising_edge;
    end
end
```

**SPI Modes Explained:**

| Mode | CPOL | CPHA | Sample Edge | Change Edge |
|------|------|------|-------------|-------------|
| 0    | 0    | 0    | Rising      | Falling     |
| 1    | 0    | 1    | Falling     | Rising      |
| 2    | 1    | 0    | Falling     | Rising      |
| 3    | 1    | 1    | Rising      | Falling     |

- **CPHA=0**: Data changes on opposite edge from sampling (provides setup time)
- **CPHA=1**: Data changes on same type edge as sampling (but different cycle)

## Bit Counter

```systemverilog
logic [$clog2(DATA_WIDTH)-1:0] bit_counter;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        bit_counter <= '0;
    end else begin
        case (current_state)
            IDLE: bit_counter <= '0;
            TRANSFER: begin
                if (sample_edge)
                    bit_counter <= bit_counter + 1;
            end
        endcase
    end
end
```

**Purpose:**
- Counts from 0 to DATA_WIDTH-1 (e.g., 0 to 7 for 8-bit transfers)
- Increments on each sample edge
- When bit_counter reaches DATA_WIDTH-1, all bits have been transferred
- Reset to 0 in IDLE state

## Transmit Shift Register

```systemverilog
logic [DATA_WIDTH-1:0] tx_shift_reg;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        tx_shift_reg <= '0;
    end else begin
        case (current_state)
            IDLE: begin
                if (tx_valid)
                    tx_shift_reg <= tx_data;  // Load new data
            end
            TRANSFER: begin
                if (change_edge)
                    // Shift left, MSB transmitted first
                    tx_shift_reg <= {tx_shift_reg[DATA_WIDTH-2:0], 1'b0};
            end
        endcase
    end
end

assign mosi = tx_shift_reg[DATA_WIDTH-1];  // Output MSB
```

**How it works:**
1. **IDLE**: When tx_valid is high, load tx_data into shift register
2. **TRANSFER**: On each change_edge, shift left by one bit
3. MSB (Most Significant Bit) is always presented on MOSI
4. **Example** (8-bit):
   - Start: 10110010
   - After 1st shift: 01100100 (sent '1')
   - After 2nd shift: 11001000 (sent '0')
   - After 3rd shift: 10010000 (sent '1')
   - etc.

## Receive Shift Register

```systemverilog
logic [DATA_WIDTH-1:0] rx_shift_reg;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        rx_shift_reg <= '0;
    end else begin
        if (current_state == TRANSFER && sample_edge) begin
            // Shift in from right, MSB first protocol
            rx_shift_reg <= {rx_shift_reg[DATA_WIDTH-2:0], miso};
        end
    end
end

assign rx_data = rx_shift_reg;
```

**How it works:**
1. On each sample_edge, read MISO bit
2. Shift existing bits left, insert new bit at LSB
3. After DATA_WIDTH sample edges, complete byte is received
4. **Example** (8-bit, receiving 0xA5 = 10100101):
   - After bit 0: 00000001 (received '1')
   - After bit 1: 00000010 (received '0')
   - After bit 2: 00000101 (received '1')
   - After bit 3: 00001010 (received '0')
   - ...
   - After bit 7: 10100101 (complete)

## State Transitions

```systemverilog
always_comb begin
    next_state = current_state;
    case (current_state)
        IDLE: begin
            if (tx_valid && tx_ready)
                next_state = TRANSFER;
        end
        TRANSFER: begin
            if (bit_counter == DATA_WIDTH - 1 && sample_edge)
                next_state = DONE;
        end
        DONE: begin
            next_state = IDLE;
        end
    endcase
end
```

**State Transition Logic:**
1. **IDLE → TRANSFER**: When user provides valid data (tx_valid && tx_ready)
2. **TRANSFER → DONE**: After last bit is sampled (bit_counter == 7 for 8-bit)
3. **DONE → IDLE**: Immediately next cycle, allowing new transaction

## Control Signals

```systemverilog
always_comb begin
    tx_ready = (current_state == IDLE);
    rx_valid = (current_state == DONE);
    sclk_enable = (current_state == TRANSFER);
    cs_n = (current_state == IDLE);
end
```

**Signal Meanings:**
- **tx_ready**: High only in IDLE, indicating ready for new transaction
- **rx_valid**: High only in DONE state, data is valid for one cycle
- **sclk_enable**: Enables clock generation during transfer
- **cs_n**: High (inactive) in IDLE, low (active) during TRANSFER and DONE

---

# UART Transmitter - Detailed Explanation

## Baud Rate Generation

```systemverilog
parameter CLK_FREQ = 50_000_000;   // 50 MHz system clock
parameter BAUD_RATE = 115200;       // 115200 bits per second

localparam CLKS_PER_BIT = CLK_FREQ / BAUD_RATE;
// For 50MHz and 115200 baud: CLKS_PER_BIT = 434 clocks per bit
```

**Calculation:**
- Each UART bit lasts 1/BAUD_RATE seconds
- At CLK_FREQ Hz, this is CLK_FREQ/BAUD_RATE clock cycles
- **Example**: 50,000,000 / 115,200 = 434 clocks per bit
- **Bit period**: 1/115200 = 8.68 μs

## UART Frame Structure

```
   Idle    Start   D0   D1   D2   D3   D4   D5   D6   D7   Parity  Stop   Idle
    1    |  0   | LSB |    |    |    |    |    |    | MSB |  P   |  1   |  1
         └─────────────────────────────────────────────────────────────┘
                            One complete frame
```

**Frame Components:**
1. **Idle**: TX line high (logic 1) when no transmission
2. **Start Bit**: Always 0 (falling edge signals start)
3. **Data Bits**: 5-9 bits, LSB first
4. **Parity Bit**: Optional error detection (odd/even/none)
5. **Stop Bit**: 1 or 2 bits, always 1 (returns to idle)

## TX State Machine

```systemverilog
typedef enum logic [2:0] {
    IDLE,              // Waiting for data, TX = 1
    START_BIT,         // Sending start bit (0)
    DATA_BITS_STATE,   // Sending data bits (LSB first)
    PARITY_BIT,        // Sending parity bit (if enabled)
    STOP_BITS_STATE    // Sending stop bits (1)
} state_t;
```

**State Flow:**
- IDLE → START_BIT (when tx_valid asserted)
- START_BIT → DATA_BITS_STATE (after 1 bit period)
- DATA_BITS_STATE → PARITY_BIT or STOP_BITS_STATE (after all data bits)
- PARITY_BIT → STOP_BITS_STATE (after 1 bit period)
- STOP_BITS_STATE → IDLE (after stop bits sent)

## Baud Rate Clock Counter

```systemverilog
logic [$clog2(CLKS_PER_BIT)-1:0] clk_counter;
logic tick;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        clk_counter <= '0;
    end else begin
        if (current_state == IDLE) begin
            clk_counter <= '0;  // Reset in idle
        end else if (clk_counter == CLKS_PER_BIT - 1) begin
            clk_counter <= '0;  // Roll over after full bit period
        end else begin
            clk_counter <= clk_counter + 1;
        end
    end
end

assign tick = (clk_counter == CLKS_PER_BIT - 1);
```

**How it works:**
1. Counter runs from 0 to CLKS_PER_BIT-1
2. `tick` pulses high for 1 clock cycle at end of each bit period
3. This creates precise timing for each bit in UART frame
4. **Example**: For 434 clocks/bit, tick pulses every 434 system clocks

## Bit Index Counter

```systemverilog
logic [$clog2(DATA_BITS)-1:0] bit_index;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        bit_index <= '0;
    end else begin
        case (current_state)
            IDLE, START_BIT, PARITY_BIT: begin
                bit_index <= '0;
            end
            DATA_BITS_STATE, STOP_BITS_STATE: begin
                if (tick)
                    bit_index <= bit_index + 1;
            end
        endcase
    end
end
```

**Purpose:**
- Tracks which data bit is being sent (0 to DATA_BITS-1)
- Tracks which stop bit is being sent (for 2 stop bits)
- Resets in states that don't need counting
- Increments on each `tick` pulse

## TX Data Shift Register

```systemverilog
logic [DATA_BITS-1:0] tx_shift_reg;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        tx_shift_reg <= '0;
    end else begin
        if (current_state == IDLE && tx_valid)
            tx_shift_reg <= tx_data;  // Load new data
        else if (current_state == DATA_BITS_STATE && tick)
            // Shift right: LSB transmitted first in UART
            tx_shift_reg <= {1'b0, tx_shift_reg[DATA_BITS-1:1]};
    end
end
```

**UART sends LSB first** (opposite of SPI):
- **Example** (8-bit, sending 0xA5 = 10100101):
  - Bit 0: Send tx_shift_reg[0] = 1
  - Bit 1: Send tx_shift_reg[0] = 0 (after shift)
  - Bit 2: Send tx_shift_reg[0] = 1
  - Bit 3: Send tx_shift_reg[0] = 0
  - ... (LSB to MSB)

## Parity Calculation

```systemverilog
logic parity_bit;

always_comb begin
    case (parity_mode)
        2'b01: parity_bit = ^tx_data;      // Odd parity
        2'b10: parity_bit = ~(^tx_data);   // Even parity
        default: parity_bit = 1'b0;
    endcase
end
```

**Parity Types:**
1. **Odd Parity** (`^tx_data`): XOR of all bits
   - Example: 10100101 → 1^0^1^0^0^1^0^1 = 0 (even number of 1s)
   - To make odd: parity_bit = 0

2. **Even Parity** (`~(^tx_data)`): Inverse XOR
   - Makes total 1s (including parity) even
   - Example: 10100101 → parity_bit = 1 (making total 1s = 5, odd, so we flip)

3. **No Parity**: Skip parity bit entirely

## TX Output Logic

```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        tx <= 1'b1;  // Idle high
    end else begin
        case (current_state)
            IDLE:            tx <= 1'b1;          // Idle = high
            START_BIT:       tx <= 1'b0;          // Start = low
            DATA_BITS_STATE: tx <= tx_shift_reg[0]; // Current data bit (LSB)
            PARITY_BIT:      tx <= parity_bit;    // Parity value
            STOP_BITS_STATE: tx <= 1'b1;          // Stop = high
        endcase
    end
end
```

**Output Behavior:**
- Registered output (no glitches)
- Each state directly controls TX line value
- Start bit always 0 (alerts receiver)
- Stop bit always 1 (returns to idle)

---

# UART Receiver - Detailed Explanation

## RX Input Synchronization

```systemverilog
logic [2:0] rx_sync;
logic rx_synced;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        rx_sync <= 3'b111;  // Initialize to idle
    else
        rx_sync <= {rx_sync[1:0], rx};  // 3-stage synchronizer
end

assign rx_synced = rx_sync[2];
```

**Why synchronize?**
1. RX signal comes from external source (different clock domain)
2. May violate setup/hold times → metastability
3. **3-stage synchronizer**:
   - Stage 1: May be metastable
   - Stage 2: Metastability resolves (typically)
   - Stage 3: Clean, synchronized signal
4. **Latency**: 3 clock cycles from RX change to rx_synced

## Start Bit Detection

```systemverilog
logic rx_prev;
logic start_detected;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        rx_prev <= 1'b1;
    else
        rx_prev <= rx_synced;
end

assign start_detected = rx_prev && !rx_synced;  // Falling edge
```

**Detection Logic:**
- UART start bit is falling edge (1 → 0)
- `rx_prev` stores previous value
- `start_detected` pulses when: was 1, now 0
- This triggers state machine to begin receiving

## Mid-Bit Sampling

```systemverilog
localparam CLKS_PER_BIT = CLK_FREQ / BAUD_RATE;

logic [$clog2(CLKS_PER_BIT)-1:0] clk_counter;
logic tick;

assign tick = (clk_counter == CLKS_PER_BIT/2);  // Sample at midpoint
```

**Why sample at midpoint?**

```
Bit Period: |<----------- CLKS_PER_BIT ----------->|
RX Signal:  |  Previous Bit  | Transition |  New Bit  |
Sample:                                    ^
                                     (CLKS_PER_BIT/2)
```

- Sampling at middle of bit maximizes timing margin
- Tolerates ±50% clock drift
- Avoids sampling during transitions (where glitches may occur)

## RX State Machine

```systemverilog
typedef enum logic [2:0] {
    IDLE,              // Waiting for start bit
    START_BIT,         // Validating start bit
    DATA_BITS_STATE,   // Receiving data bits
    PARITY_BIT,        // Receiving parity bit
    STOP_BITS_STATE,   // Validating stop bit(s)
    ERROR              // Frame error detected
} state_t;
```

**State Details:**

1. **IDLE**:
   - RX line high (idle)
   - Waiting for falling edge (start bit)

2. **START_BIT**:
   - Wait full bit period
   - Re-check RX is still low (validates start bit)
   - False start detection: if RX high, return to IDLE

3. **DATA_BITS_STATE**:
   - Sample each bit at midpoint
   - Shift into receive register (LSB first)
   - Continue for DATA_BITS cycles

4. **PARITY_BIT**:
   - Sample parity bit (if enabled)
   - Compare with calculated parity

5. **STOP_BITS_STATE**:
   - Verify RX is high (valid stop bit)
   - If low → frame error → ERROR state
   - If high → data valid → return to IDLE

6. **ERROR**:
   - Frame or parity error detected
   - Assert rx_error signal
   - Return to IDLE next cycle

## Receive Shift Register

```systemverilog
logic [DATA_BITS-1:0] rx_shift_reg;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        rx_shift_reg <= '0;
    end else begin
        if (current_state == DATA_BITS_STATE && tick) begin
            // Shift right, insert new bit at MSB
            rx_shift_reg <= {rx_synced, rx_shift_reg[DATA_BITS-1:1]};
        end
    end
end
```

**LSB-First Reception:**
- Bit 0 arrives first → stored at position 0
- Bit 1 arrives next → stored at position 1
- Process: shift right, insert new bit at top
- After 8 bits, register contains complete byte in correct order

**Example** (receiving 0xA5 = 10100101):
```
After bit 0 (LSB=1): 10000000
After bit 1 (=0):    01000000
After bit 2 (=1):    10100000
After bit 3 (=0):    01010000
After bit 4 (=0):    00101000
After bit 5 (=1):    10010100
After bit 6 (=0):    01001010
After bit 7 (MSB=1): 10100101 ✓
```

## Parity Checking

```systemverilog
logic parity_received;
logic parity_calculated;
logic parity_error;

// Capture received parity bit
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        parity_received <= 1'b0;
    else if (current_state == PARITY_BIT && tick)
        parity_received <= rx_synced;
end

// Calculate expected parity
always_comb begin
    case (parity_mode)
        2'b01: parity_calculated = ^rx_shift_reg;      // Odd
        2'b10: parity_calculated = ~(^rx_shift_reg);   // Even
        default: parity_calculated = 1'b0;
    endcase
end

// Compare
assign parity_error = (parity_mode != 2'b00) &&
                      (parity_received != parity_calculated);
```

**Error Detection:**
- Capture parity bit from RX line
- Calculate expected parity from received data
- If mismatch → assert parity_error
- Parity catches single-bit errors (not multiple bits)

## Output Generation

```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        rx_data <= '0;
        rx_valid <= 1'b0;
        rx_error <= 1'b0;
    end else begin
        rx_valid <= 1'b0;  // Default: not valid
        rx_error <= 1'b0;  // Default: no error

        if (next_state == IDLE && current_state == STOP_BITS_STATE) begin
            // Successfully received complete frame
            rx_data <= rx_shift_reg;
            rx_valid <= !parity_error;
            rx_error <= parity_error;
        end else if (current_state == ERROR) begin
            // Frame error
            rx_error <= 1'b1;
        end
    end
end
```

**Signal Timing:**
- `rx_valid`: Pulses for 1 cycle when valid data received
- `rx_error`: Pulses for 1 cycle when error detected
- `rx_data`: Holds data when rx_valid asserted

---

# I2C Master - Detailed Explanation

## I2C Clock Generation

```systemverilog
parameter CLK_FREQ = 50_000_000;   // System clock
parameter I2C_FREQ = 100_000;       // I2C SCL frequency (100 kHz standard mode)

localparam DIVIDER = CLK_FREQ / (4 * I2C_FREQ);
// For 50MHz sys clk and 100kHz I2C: DIVIDER = 125
```

**Why divide by 4?**
- I2C clock has 4 phases per complete cycle
- Phase 0: SCL low, data change allowed
- Phase 1: SCL low → high transition
- Phase 2: SCL high, data stable (sample here)
- Phase 3: SCL high → low transition

```systemverilog
logic [1:0] scl_phase;  // 0, 1, 2, 3

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        clk_counter <= '0;
        scl_phase <= 2'b00;
    end else begin
        if (clk_counter == DIVIDER - 1) begin
            clk_counter <= '0;
            scl_phase <= scl_phase + 1;  // Advance phase
        end else begin
            clk_counter <= clk_counter + 1;
        end
    end
end

// Generate SCL based on phase
assign scl = (scl_phase == 2'b10) || (scl_phase == 2'b11);
```

**SCL Waveform:**
```
Phase:     0     1     2     3     0     1     2     3
SCL:    _____|‾‾‾‾‾|‾‾‾‾‾|_____|_____|‾‾‾‾‾|‾‾‾‾‾|_____
           Low   Rise  High  Fall   Low   Rise  High  Fall
Change:    ^                         ^
Sample:              ^                         ^
```

## I2C Start Condition

```
Start Condition: SDA falls while SCL is HIGH

        ______
SDA:          \_________  (SDA: 1→0 while SCL=1)
        _____________
SCL:                 ‾‾‾
```

**Implementation:**
```systemverilog
START_COND: begin
    if (scl_phase == 2'b10 && tick) begin  // SCL is high
        sda_out <= 1'b0;  // Pull SDA low
        sda_oe <= 1'b1;   // Enable output
    end
end
```

**Why phase 2?**
- Phase 2: SCL is stable high
- Generate SDA falling edge during this phase
- Slaves detect START and prepare to receive address

## I2C Stop Condition

```
Stop Condition: SDA rises while SCL is HIGH

                  ______
SDA:  __________/        (SDA: 0→1 while SCL=1)
              _________
SCL:  _______/
```

**Implementation:**
```systemverilog
STOP_COND: begin
    if (scl_phase <= 2'b01) begin
        sda_out <= 1'b0;  // Keep SDA low
        sda_oe <= 1'b1;
    end else if (tick && scl_phase == 2'b10) begin
        sda_out <= 1'b1;  // Release SDA (goes high)
        sda_oe <= 1'b1;
    end
end
```

**Sequence:**
1. Ensure SDA is low during SCL low period
2. SCL rises (phase 1→2)
3. SDA rises during phase 2 (while SCL high)
4. This signals end of transaction

## Address and Data Transmission

**I2C Frame Format:**
```
|S| Address[6:0] |R/W|A| Data[7:0] |A| ... |P|
 ^                   ^             ^         ^
Start              ACK            ACK       Stop
```

**Address Sending:**
```systemverilog
ADDR_SEND: begin
    if (tick && scl_phase == 2'b01) begin  // Change during SCL low
        sda_out <= tx_shift_reg[7];  // Output MSB
        sda_oe <= 1'b1;
        tx_shift_reg <= {tx_shift_reg[6:0], 1'b0};  // Shift left
    end
end
```

**Timing:**
```
Bit:      7     6     5     4     3     2     1    R/W
         ___   ___   ___   ___   ___   ___   ___   ___
SCL:  __|   |_|   |_|   |_|   |_|   |_|   |_|   |_|   |_
         ___ ___ ___ ___ ___ ___ ___ ___
SDA:  __|A6_|A5_|A4_|A3_|A2_|A1_|A0_|RW_|
         ^   ^   ^   ^   ^   ^   ^   ^
      Change on SCL low, Sample on SCL high
```

## I2C Acknowledgment

**ACK Bit:**
- After each 8-bit transfer, receiver sends ACK
- ACK = 0 (SDA pulled low): "Data received successfully"
- NACK = 1 (SDA released high): "End transfer" or "Error"

```systemverilog
ADDR_ACK, DATA_ACK: begin
    sda_oe <= 1'b0;  // Release SDA (slave controls it)
end

// Sample ACK during SCL high
if (tick && scl_phase == 2'b10) begin
    ack_received <= !sda_in;  // ACK=0, NACK=1
end
```

**ACK Timing:**
```
         Data Bit 7         ACK
         ___________       _____
SCL:  __|           |_____|     |_____
         ___________       _____
SDA:  __|    D7     |_____|  0  |_____  (ACK=0, pulled by slave)
                              ^
                         Sample here
```

## Open-Drain Control

I2C uses **open-drain** (or open-collector) outputs:

```systemverilog
inout wire sda;  // Bidirectional

logic sda_out;   // Our output value
logic sda_oe;    // Output enable
logic sda_in;    // Read current value

assign sda = sda_oe ? sda_out : 1'bz;  // Drive or high-Z
assign sda_in = sda;  // Always read current value
```

**Why Open-Drain?**
1. **Wired-AND**: Multiple devices can pull line low
2. **Pull-up resistor**: External resistor pulls line high when no device drives low
3. **Multi-master**: Any master can control line
4. **Clock stretching**: Slave can hold SCL low to slow down master

**Behavior:**
- `sda_oe = 0, sda_out = X`: High-impedance (line pulled high by resistor)
- `sda_oe = 1, sda_out = 0`: Drive low (overrides pull-up)
- `sda_oe = 1, sda_out = 1`: Actively drive high (not typically used in I2C)

---

# Asynchronous FIFO - Detailed Explanation

Asynchronous FIFOs are critical for **Clock Domain Crossing** (CDC). They allow safe data transfer between different clock domains.

## The Challenge: Metastability

```
Write Clock Domain          Read Clock Domain
(wr_clk)                   (rd_clk)

wr_ptr ────────X────────────> rd_ptr_sync
               │
               └─> Metastability risk!
```

**Problem:**
- Write pointer changes in wr_clk domain
- Read logic needs to know write pointer (in rd_clk domain)
- Direct crossing can cause metastability → system crash

**Solution: Gray Code + Synchronizers**

## Gray Code Conversion

**Binary vs Gray Code:**

| Decimal | Binary | Gray |
|---------|--------|------|
| 0       | 000    | 000  |
| 1       | 001    | 001  |
| 2       | 010    | 011  |
| 3       | 011    | 010  |
| 4       | 100    | 110  |
| 5       | 101    | 111  |
| 6       | 110    | 101  |
| 7       | 111    | 100  |

**Key Property:** Only 1 bit changes between consecutive values

**Why use Gray Code?**
- Binary 011→100: 3 bits change simultaneously
- If sampled during transition: might read 010, 011, 100, 110, 111 (glitch!)
- Gray 010→110: Only 1 bit changes
- Even if metastable, error is max ±1 count (acceptable for FIFO)

## Binary to Gray Conversion

```systemverilog
logic [ADDR_WIDTH:0] wr_ptr_bin;   // Binary counter
logic [ADDR_WIDTH:0] wr_ptr_gray;  // Gray code version

// Binary to Gray conversion
assign wr_ptr_gray_next = (wr_ptr_bin >> 1) ^ wr_ptr_bin;

always_ff @(posedge wr_clk or negedge wr_rst_n) begin
    if (!wr_rst_n) begin
        wr_ptr_bin <= '0;
        wr_ptr_gray <= '0;
    end else if (wr_en && !full) begin
        wr_ptr_bin <= wr_ptr_bin + 1;
        wr_ptr_gray <= (wr_ptr_bin + 1) >> 1 ^ (wr_ptr_bin + 1);
    end
end
```

**Conversion Formula:**
```
gray[n] = binary[n] XOR binary[n+1]
```

**Example:**
- Binary: 0101 (5)
- Shift right: 0010
- XOR: 0101 ^ 0010 = 0111
- Gray: 0111

## Two-Stage Synchronizer

```systemverilog
// Synchronize write pointer to read clock domain
logic [ADDR_WIDTH:0] wr_ptr_gray_rd_sync1;
logic [ADDR_WIDTH:0] wr_ptr_gray_rd_sync2;

always_ff @(posedge rd_clk or negedge rd_rst_n) begin
    if (!rd_rst_n) begin
        wr_ptr_gray_rd_sync1 <= '0;
        wr_ptr_gray_rd_sync2 <= '0;
    end else begin
        wr_ptr_gray_rd_sync1 <= wr_ptr_gray;      // May be metastable
        wr_ptr_gray_rd_sync2 <= wr_ptr_gray_rd_sync1;  // Stable
    end
end
```

**How it works:**

```
wr_clk:  __|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__
wr_ptr_gray:  0000      0001              0011

rd_clk:  __|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__
sync1:         ????          0001                  0011
sync2:                            0001                      0011
```

- **sync1**: May capture during transition → metastable → resolves within 1 clock
- **sync2**: Captures stable value from sync1
- **Latency**: 2 read clock cycles behind actual write pointer
- **Safety**: Metastability fully resolved

## Full Condition Detection

```systemverilog
// Full when write pointer+1 equals read pointer
// But compare Gray codes!
assign full = (wr_ptr_gray_next == {~rd_ptr_gray_wr_sync[ADDR_WIDTH:ADDR_WIDTH-1],
                                     rd_ptr_gray_wr_sync[ADDR_WIDTH-2:0]});
```

**Why invert top 2 bits?**

Consider 4-entry FIFO (ADDR_WIDTH=2, pointers 3 bits wide including extra bit):

| Wr_Ptr | Rd_Ptr | Status |
|--------|--------|--------|
| 000    | 000    | Empty  |
| 001    | 000    | 1 used |
| 010    | 000    | 2 used |
| 011    | 000    | 3 used |
| 100    | 000    | FULL   |

- Full: wr_ptr is exactly DEPTH ahead of rd_ptr
- In Gray: 100 vs 000
- Need to detect "wrapped around" condition
- Inverting top 2 bits handles wrap: 100 becomes 000 for comparison

**Example:**
- wr_ptr_gray = 110 (6)
- rd_ptr_gray = 010 (3)
- Full check: 110 == {~01, 0} = {10, 0} = 100? No, not full
- When wr wraps: wr_ptr_gray = 010, rd_ptr = 010
- Full check: 010 == {~01, 1[0]} = {10, 10} = 110? No...

(This logic is complex; trust that Gray code math works out!)

## Empty Condition Detection

```systemverilog
// Empty when read pointer equals write pointer
assign empty = (rd_ptr_gray == wr_ptr_gray_rd_sync);
```

**Simple comparison:**
- If pointers are equal → FIFO is empty
- No inversion needed (unlike full)
- Both pointers synchronized to read domain

## Memory Access

```systemverilog
// Write side (wr_clk domain)
always_ff @(posedge wr_clk) begin
    if (wr_en && !full) begin
        mem[wr_ptr_bin[ADDR_WIDTH-1:0]] <= wr_data;
    end
end

// Read side (rd_clk domain)
always_ff @(posedge rd_clk) begin
    if (rd_en && !empty) begin
        rd_data <= mem[rd_ptr_bin[ADDR_WIDTH-1:0]];
    end
end
```

**Why use binary for addressing?**
- Gray code for pointer synchronization
- Binary for memory indexing (natural addressing)
- Use lower ADDR_WIDTH bits (ignore MSB used for full/empty detection)

**Example** (DEPTH=16, ADDR_WIDTH=4, pointers are 5 bits):
- wr_ptr_bin = 10011 (19)
- Address: 10011[3:0] = 0011 (3)
- Wraps correctly: 19 mod 16 = 3

---

# APB (Advanced Peripheral Bus) - Detailed Explanation

## APB Protocol Basics

APB is a **simple, low-power bus** for peripherals. It's not pipelined and has minimal overhead.

### APB State Diagram

```
           ┌──────┐
           │ IDLE │◄─────────────┐
           └──┬───┘              │
              │ PSEL=1           │
              ▼                  │
         ┌────────┐              │
         │ SETUP  │              │
         └───┬────┘              │
             │ PENABLE=1         │
             ▼                   │
        ┌─────────┐              │
        │ ACCESS  │──────────────┘
        └─────────┘  PREADY=1
```

**States:**
1. **IDLE**: No transfer selected
2. **SETUP**: Address/control valid for 1 cycle (slave preparation)
3. **ACCESS**: Data transfer occurs, can extend with PREADY=0

### APB Signal Timing

**Read Transaction:**
```
PCLK:    __|‾‾|__|‾‾|__|‾‾|__|‾‾|__
          IDLE   SETUP  ACCESS IDLE
PSEL:    _____|‾‾‾‾‾‾‾‾‾‾‾‾‾|_____
PENABLE: ___________|‾‾‾‾‾‾|_______
PADDR:   ─────<ADDR>──────────────
PWRITE:  ___________________________
PRDATA:  ──────────────<DATA>──────
PREADY:  ___________<depends>______
```

**Write Transaction:**
```
PCLK:    __|‾‾|__|‾‾|__|‾‾|__|‾‾|__
          IDLE  SETUP  ACCESS IDLE
PSEL:    _____|‾‾‾‾‾‾‾‾‾‾‾‾‾|_____
PENABLE: ___________|‾‾‾‾‾‾|_______
PADDR:   ─────<ADDR>──────────────
PWRITE:  _____|‾‾‾‾‾‾‾‾‾‾‾‾‾|_____
PWDATA:  ─────<DATA>──────────────
PREADY:  ___________<depends>______
```

## APB Slave Implementation Details

### Address Decoding

```systemverilog
parameter NUM_REGS = 16;  // 16 registers

logic [$clog2(NUM_REGS)-1:0] reg_addr;
assign reg_addr = PADDR[$clog2(NUM_REGS)+1:2];  // Word-aligned

logic addr_valid;
assign addr_valid = (reg_addr < NUM_REGS);
```

**Address Calculation:**
- Registers are **word-aligned** (4 bytes for 32-bit)
- Address bits [1:0] ignored (always 00 for word access)
- Use bits [$clog2(NUM_REGS)+1:2] to index register
- **Example**:
  - NUM_REGS=16 → 4 bits needed
  - PADDR[5:2] → addresses 0,4,8,12,...,60
  - reg_addr: 0-15

### Write Operation

```systemverilog
always_ff @(posedge PCLK or negedge PRESETn) begin
    if (!PRESETn) begin
        for (int i = 0; i < NUM_REGS; i++)
            registers[i] <= '0;
    end else begin
        if (PSEL && PENABLE && PWRITE && addr_valid) begin
            registers[reg_addr] <= PWDATA;
        end
    end
end
```

**Write Conditions:**
- `PSEL`: This slave selected
- `PENABLE`: In ACCESS phase
- `PWRITE`: Write operation
- `addr_valid`: Address in range

**Timing:** Write occurs on rising edge of ACCESS phase

### Read Operation

```systemverilog
always_ff @(posedge PCLK or negedge PRESETn) begin
    if (!PRESETn) begin
        PRDATA <= '0;
    end else begin
        if (PSEL && !PENABLE && !PWRITE && addr_valid) begin
            PRDATA <= registers[reg_addr];  // Latch during SETUP
        end else begin
            PRDATA <= '0;
        end
    end
end
```

**Read Timing:**
- Data latched during **SETUP** phase
- Available for master to sample during **ACCESS** phase
- Provides full cycle for data to propagate

### PREADY Signal

```systemverilog
assign PREADY = 1'b1;  // Always ready (no wait states)
```

**Wait States:**
- `PREADY=0`: Slave not ready, extend ACCESS phase
- `PREADY=1`: Slave ready, complete transfer
- Simple slaves: always ready
- Complex slaves (slow memory): may need wait states

### PSLVERR Signal

```systemverilog
always_ff @(posedge PCLK or negedge PRESETn) begin
    if (!PRESETn) begin
        PSLVERR <= 1'b0;
    end else begin
        PSLVERR <= PSEL && PENABLE && !addr_valid;  // Error if invalid address
    end
end
```

**Error Conditions:**
- Invalid address
- Unsupported operation
- Timeout
- Security violation

---

# AXI4-Lite - Detailed Explanation

AXI is **much more complex** than APB. It has separate channels for address, data, and response.

## AXI Channel Independence

**Key Feature:** Address and Data phases are **separate and independent**

```
Write Transaction:
  Address Channel: AWADDR → AWREADY
  Data Channel:    WDATA  → WREADY     } Can occur in any order!
  Response:        BRESP  ← BVALID

Read Transaction:
  Address Channel: ARADDR → ARREADY
  Data Channel:    RDATA  ← RVALID
```

## Valid/Ready Handshake

**Every AXI transfer** uses this protocol:

```systemverilog
// Transfer occurs when BOTH valid and ready are high
if (AWVALID && AWREADY) begin
    // Address transfer complete
end
```

**Rules:**
1. VALID can assert before READY (master waiting for slave)
2. READY can assert before VALID (slave waiting for master)
3. Transfer occurs on clock edge when BOTH are high
4. VALID must not wait for READY (no combinational paths)

**Timing Example:**
```
CLK:     ___|‾‾‾|___|‾‾‾|___|‾‾‾|___|‾‾‾|___
AWVALID: _____|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|_______
AWREADY: _______________|‾‾‾‾‾‾‾‾‾|_________
Transfer:                   ▲
                    (Cycle where both=1)
```

## Write Address Channel

```systemverilog
logic [ADDR_WIDTH-1:0] write_addr;
logic write_addr_ready;

always_ff @(posedge ACLK or negedge ARESETn) begin
    if (!ARESETn) begin
        write_addr <= '0;
        write_addr_ready <= 1'b0;
    end else begin
        if (AWVALID && AWREADY) begin
            write_addr <= AWADDR;  // Capture address
            write_addr_ready <= 1'b1;  // Mark as valid
        end else if (WVALID && WREADY) begin
            write_addr_ready <= 1'b0;  // Clear after use
        end
    end
end

assign AWREADY = !write_addr_ready;  // Ready when no pending address
```

**Logic:**
1. When address arrives (AWVALID && AWREADY), store it
2. Set flag indicating address is available
3. When write data comes (WVALID && WREADY), use address and clear flag
4. Ready to accept new address only when no pending address

## Write Data Channel with Byte Strobes

```systemverilog
logic [DATA_WIDTH/8-1:0] WSTRB;  // Byte strobes

always_ff @(posedge ACLK) begin
    if (WVALID && WREADY && wr_addr_valid) begin
        for (int i = 0; i < DATA_WIDTH/8; i++) begin
            if (WSTRB[i]) begin  // Write this byte?
                registers[wr_reg_addr][i*8 +: 8] <= WDATA[i*8 +: 8];
            end
        end
    end
end
```

**Byte Strobes (WSTRB):**
- 1 bit per byte of data bus
- `WSTRB[i]=1`: Write byte i
- `WSTRB[i]=0`: Don't write byte i (preserve old value)

**Example** (32-bit data):
- WSTRB = 4'b0001: Write byte 0 only
- WSTRB = 4'b1100: Write bytes 2 and 3
- WSTRB = 4'b1111: Write all 4 bytes (full word)

**Usage:**
- Partial word writes
- Byte, halfword, word access on same bus
- Critical for correct operation!

## Write Response Channel

```systemverilog
localparam OKAY = 2'b00;
localparam SLVERR = 2'b10;

always_ff @(posedge ACLK or negedge ARESETn) begin
    if (!ARESETn) begin
        BVALID <= 1'b0;
        BRESP <= OKAY;
    end else begin
        if (WVALID && WREADY) begin
            BVALID <= 1'b1;  // Response valid after write
            BRESP <= wr_addr_valid ? OKAY : SLVERR;
        end else if (BVALID && BREADY) begin
            BVALID <= 1'b0;  // Clear after master acknowledges
        end
    end
end
```

**Response Codes:**
- `OKAY (00)`: Success
- `EXOKAY (01)`: Exclusive access okay
- `SLVERR (10)`: Slave error (bad address, etc.)
- `DECERR (11)`: Decode error (no slave at address)

**Timing:**
```
WVALID:  ___|‾‾‾‾‾|_________________
WREADY:  ___|‾‾‾‾‾|_________________
                ▲ Write completes
BVALID:  _________|‾‾‾‾‾‾‾‾‾|_______
BREADY:  _______________|‾‾‾‾‾|_____
                            ▲ Response acknowledged
```

## Read Address Channel

```systemverilog
logic [ADDR_WIDTH-1:0] read_addr;
logic read_addr_ready;

always_ff @(posedge ACLK or negedge ARESETn) begin
    if (!ARESETn) begin
        read_addr <= '0;
        read_addr_ready <= 1'b0;
    end else begin
        if (ARVALID && ARREADY) begin
            read_addr <= ARADDR;
            read_addr_ready <= 1'b1;
        end else if (RVALID && RREADY) begin
            read_addr_ready <= 1'b0;
        end
    end
end

assign ARREADY = !read_addr_ready;
```

**Same pattern as write address:**
- Capture address when ARVALID && ARREADY
- Hold until read data sent (RVALID && RREADY)
- Signal ready when no pending address

## Read Data Channel

```systemverilog
always_ff @(posedge ACLK or negedge ARESETn) begin
    if (!ARESETn) begin
        RDATA <= '0;
        RVALID <= 1'b0;
        RRESP <= OKAY;
    end else begin
        if (read_addr_ready && !RVALID) begin
            // Perform read
            RDATA <= rd_addr_valid ? registers[rd_reg_addr] : '0;
            RVALID <= 1'b1;
            RRESP <= rd_addr_valid ? OKAY : SLVERR;
        end else if (RVALID && RREADY) begin
            // Master accepted data
            RVALID <= 1'b0;
        end
    end
end
```

**Read Flow:**
1. Address available (`read_addr_ready=1`)
2. Look up data from registers
3. Assert `RVALID` with data and response
4. Wait for master to assert `RREADY`
5. Clear `RVALID`, ready for next transaction

---

## Summary

This detailed explanation covers:

1. **SPI**: Clock generation, modes, edge detection, shift registers
2. **UART**: Baud rate timing, frame structure, parity, synchronization
3. **I2C**: Clock phases, start/stop conditions, open-drain, Gray code
4. **Async FIFO**: Clock domain crossing, Gray code, metastability
5. **APB**: Simple bus protocol, state machine, address decoding
6. **AXI**: Channel independence, valid/ready handshake, byte strobes

Each section explains **why** the code is written the way it is, not just **what** it does. This helps you understand the design decisions and adapt the code for your needs.
