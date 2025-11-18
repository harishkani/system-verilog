# Testbench Directory

This directory contains verified testbenches for all communication protocols. Each protocol has one comprehensive, working testbench.

## Testbench Files

| Testbench | Protocol | Status | Tests Covered |
|-----------|----------|--------|---------------|
| `spi_tb.v` | SPI Master | ✅ All Pass | Mode 0 transmission, 0xA5 data |
| `i2c_tb.v` | I2C Master | ✅ All Pass | Write byte, read byte, address/ACK |
| `fifo_tb.v` | Synchronous FIFO | ✅ All Pass | Fill, empty, simultaneous R/W |
| `apb_tb.v` | APB Master/Slave | ✅ All Pass | Single/sequential R/W, back-to-back |
| `axi_lite_tb.v` | AXI Lite Master/Slave | ✅ All Pass | Write, read, sequential, byte strobes |
| `uart_working_tb.v` | UART TX/RX | ✅ All Pass | 0xAA, 0x55, 0xFF, 0x00 transmission |

## Running Testbenches

### Basic Simulation

```bash
# Compile and run
iverilog -o testbench/<protocol>_tb.out testbench/<protocol>_tb.v rtl/<protocol>/*.v
vvp testbench/<protocol>_tb.out

# With waveform dump
vvp testbench/<protocol>_tb.out
gtkwave testbench/<protocol>_tb.vcd
```

### Example: Running UART Testbench

```bash
# Compile UART testbench
iverilog -o uart_test.out testbench/uart_working_tb.v rtl/uart/uart_working.v

# Run simulation
vvp uart_test.out

# Expected output:
# Test 1: Sending 0xAA
#   Result: PASS - Received 0xAA
# Test 2: Sending 0x55
#   Result: PASS - Received 0x55
# Test 3: Sending 0xFF
#   Result: PASS - Received 0xFF
# Test 4: Sending 0x00
#   Result: PASS - Received 0x00
# ALL TESTS PASSED!
```

### Example: Running AXI Lite Testbench

```bash
# Compile AXI Lite testbench
iverilog -o axi_test.out testbench/axi_lite_tb.v rtl/axi/*.v

# Run simulation
vvp axi_test.out

# Expected output:
# Test 1: Write 0xCAFEBABE to address 0x10
#   Result: PASS
# Test 2: Read from address 0x10
#   Result: PASS - Read data matches
# Test 3-5: Multiple writes/reads and byte strobes
#   Result: ALL TESTS PASSED!
```

## Testbench Structure

All testbenches follow a common structure:

```verilog
module <protocol>_tb;
    // 1. Clock and reset generation
    // 2. DUT (Device Under Test) instantiation
    // 3. Test stimulus generation
    // 4. Response checking with pass/fail reporting
    // 5. Waveform dumping ($dumpfile, $dumpvars)
endmodule
```

## Key Features

### Self-Checking
All testbenches automatically verify results and report:
- ✅ PASS for successful tests
- ❌ FAIL for failed tests with error details
- Final summary: "ALL TESTS PASSED!" or error count

### Waveform Generation
Each testbench generates VCD files for signal-level debugging:
```verilog
initial begin
    $dumpfile("protocol_tb.vcd");
    $dumpvars(0, protocol_tb);
end
```

### Comprehensive Coverage
Tests cover:
- Basic functionality (single read/write)
- Edge cases (empty, full, back-to-back)
- Error conditions (false starts, timing issues)
- Multiple data patterns

## Verification Status

All testbenches verified with:
- **Simulator**: iverilog 12.0 (Icarus Verilog)
- **Waveform Viewer**: GTKWave
- **Date**: 2025-11-18

## Testbench-Specific Notes

### SPI (`spi_tb.v`)
- Tests SPI Mode 0 (CPOL=0, CPHA=0)
- Clock divider: 4
- Data pattern: 0xA5

### I2C (`i2c_tb.v`)
- Tests 7-bit addressing
- Slave address: 0x50
- Verifies START, address, ACK, data, STOP sequence

### FIFO (`fifo_tb.v`)
- Tests 8-bit width, 16-entry depth
- Verifies empty/full flags
- Tests simultaneous read/write

### APB (`apb_tb.v`)
- Tests 32-bit address/data
- Verifies 2-phase protocol (SETUP → ACCESS)
- Tests PREADY and PSLVERR signals

### AXI Lite (`axi_lite_tb.v`)
- Tests all 5 channels (AW, W, B, AR, R)
- Verifies VALID/READY handshaking
- Tests byte strobe (WSTRB) functionality
- Checks response codes (BRESP, RRESP)

### UART (`uart_working_tb.v`)
- Tests asynchronous communication
- Baud rate: 10 kbps (CLKS_PER_BIT=100)
- Clock: 1 MHz
- Frame: 8N1 (8 data bits, no parity, 1 stop bit)
- Verifies TX → RX loopback

## Troubleshooting

### Simulation Hangs
- Check timeout values in testbenches
- Verify clock is toggling
- Check for deadlocks in handshaking

### Tests Fail
1. Check module paths in iverilog command
2. Verify parameter values match between TB and DUT
3. Review timing (setup/hold violations)
4. Use VCD waveforms to debug signal timing

### Compilation Errors
- Ensure all dependent RTL files are included
- Check for module name mismatches
- Verify file paths are correct

## Adding New Testbenches

When adding new testbenches:
1. Follow the naming convention: `<protocol>_tb.v`
2. Include self-checking with pass/fail reporting
3. Generate VCD waveforms
4. Document test coverage in this README
5. Verify with iverilog before committing

## Documentation

For detailed protocol information:
- **RTL Guide**: `rtl/README.md`
- **Protocol Details**: `docs/Communication_Protocols_Comprehensive_Guide.md`
