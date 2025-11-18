# RTL Directory Structure

This directory contains verified SystemVerilog/Verilog implementations of communication protocols organized by protocol type.

## Directory Organization

```
rtl/
├── spi/          - Serial Peripheral Interface
├── i2c/          - Inter-Integrated Circuit
├── uart/         - Universal Asynchronous Receiver/Transmitter
├── fifo/         - Synchronous FIFO Buffer
├── apb/          - AMBA Advanced Peripheral Bus
└── axi/          - AMBA AXI4-Lite
```

## Protocol Implementations

### SPI (Serial Peripheral Interface)
**Location**: `rtl/spi/`
- `spi_master.v` - SPI master controller with 4-mode support
- `spi_top.v` - Top-level wrapper for easy integration
- **Status**: ✅ Verified with iverilog
- **Test**: `testbench/spi_master_tb.v`

### I2C (Inter-Integrated Circuit)
**Location**: `rtl/i2c/`
- `i2c_master.v` - I2C master with START/STOP generation
- `i2c_top.v` - Top-level wrapper with bidirectional I/O
- **Status**: ✅ Verified with iverilog
- **Test**: `testbench/i2c_master_tb.v`

### UART (Universal Asynchronous Receiver/Transmitter)
**Location**: `rtl/uart/`
- `uart_tx_working.v` - Verified transmitter module
- `uart_rx_working.v` - Verified receiver with mid-bit sampling
- `uart_top.v` - Top-level full-duplex wrapper
- `uart_tx.v` - Older parametric TX (has timing issues)
- `uart_rx.v` - Older parametric RX (has timing issues)
- `uart_working.v` - Combined TX/RX (use separate files instead)
- `uart_simple.v` - Simplified version
- **Status**: ✅ Verified with iverilog
- **Test**: `testbench/uart_working_tb.v`
- **Recommendation**: Use `uart_tx_working.v` and `uart_rx_working.v` or `uart_top.v`

### FIFO (First-In-First-Out Buffer)
**Location**: `rtl/fifo/`
- `sync_fifo.v` - Synchronous FIFO with parameterizable depth/width
- `fifo_top.v` - Top-level wrapper
- **Status**: ✅ Verified with iverilog
- **Test**: `testbench/fifo_tb.v`

### APB (AMBA Advanced Peripheral Bus)
**Location**: `rtl/apb/`
- `apb_master.v` - APB master with 2-phase protocol
- `apb_slave.v` - APB slave with memory interface
- `apb_top.v` - Top-level master-slave system
- **Status**: ✅ Verified with iverilog
- **Test**: `testbench/apb_tb.v`

### AXI Lite (AMBA AXI4-Lite)
**Location**: `rtl/axi/`
- `axi_lite_master.v` - 7-state FSM master with 5-channel protocol
- `axi_lite_slave_simple.v` - Simplified slave (recommended)
- `axi_lite_slave.v` - Full slave implementation
- `axi_lite_top.v` - Top-level master-slave system
- **Status**: ✅ Verified with iverilog
- **Test**: `testbench/axi_lite_tb.v`

## File Naming Convention

- `*_master.v` - Master/controller modules
- `*_slave.v` - Slave/peripheral modules
- `*_top.v` - Top-level wrappers connecting masters and slaves
- `*_working.v` - Verified working implementations (UART specific)

## Usage Guide

### Quick Start with Top-Level Modules

Each protocol has a `*_top.v` file that provides a simple, ready-to-use interface:

**Example: Using UART**
```verilog
uart_top #(
    .CLKS_PER_BIT(100)  // 1 MHz / 10 kbps
) u_uart (
    .clk(clk),
    .rst_n(rst_n),
    .tx_data(tx_byte),
    .tx_start(tx_go),
    .tx_busy(tx_busy),
    .rx_data(rx_byte),
    .rx_valid(rx_ready),
    .uart_rx(uart_rx_pin),
    .uart_tx(uart_tx_pin)
);
```

**Example: Using AXI Lite**
```verilog
axi_lite_top #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .MEM_DEPTH(256)
) u_axi (
    .clk(clk),
    .rst_n(rst_n),
    .req(do_transaction),
    .wr(is_write),
    .addr(address),
    .wdata(write_data),
    .wstrb(byte_enables),
    .ready(transaction_done),
    .resp_ok(no_errors),
    .rdata(read_data)
);
```

### Advanced: Using Individual Modules

For more control, instantiate individual master/slave modules directly. See testbenches for detailed examples.

## Verification Status

All protocols have been verified using:
- **Simulator**: iverilog 12.0
- **Waveform Viewer**: GTKWave
- **Documentation**: See `docs/Communication_Protocols_Comprehensive_Guide.md`

| Protocol | Files | Tests Passed | Key Features |
|----------|-------|--------------|--------------|
| SPI | 2 | ✅ All | Full-duplex, 4 modes |
| I2C | 2 | ✅ All | Multi-master, bidirectional |
| UART | 3 | ✅ All | Asynchronous, mid-bit sampling |
| FIFO | 2 | ✅ All | Simultaneous R/W, flow control |
| APB | 3 | ✅ All | Simple 2-phase, AMBA compliant |
| AXI Lite | 4 | ✅ All | 5-channel, byte strobes |

## Common Parameters

### Clock Division Parameters
- `CLK_DIV` - Clock divider ratio
- `CLKS_PER_BIT` - System clocks per bit period

### Data Parameters
- `DATA_WIDTH` - Data bus width (typically 8 or 32 bits)
- `ADDR_WIDTH` - Address bus width (typically 32 bits)
- `DEPTH` - Memory/FIFO depth

### Protocol-Specific
- `CPOL/CPHA` - SPI clock polarity/phase
- `BAUD_RATE` - UART bits per second
- `MEM_DEPTH` - Memory size for slaves

## Best Practices

1. **Reset**: All modules use asynchronous active-low reset (`rst_n`)
2. **Handshaking**: Follow ready/valid protocols carefully
3. **Timing**: Use proper clock division for desired communication speeds
4. **Testing**: Run provided testbenches before integration
5. **Top-level**: Start with `*_top.v` wrappers for easier integration

## Documentation

For detailed protocol explanations, timing diagrams, and common pitfalls:
- **Main Guide**: `docs/Communication_Protocols_Comprehensive_Guide.md`
- **Testbenches**: `testbench/` directory

## Issues and Debugging

If you encounter issues:
1. Check testbench simulations first
2. Review timing parameters (CLK_DIV, CLKS_PER_BIT)
3. Verify ready/valid handshaking
4. Consult the comprehensive guide for common pitfalls
5. Use VCD waveform dumps for signal-level debugging

## Version Information

- **Last Updated**: 2025-11-18
- **Verification Tool**: iverilog 12.0
- **Standard**: IEEE 1364-2005 (Verilog), IEEE 1800-2017 (SystemVerilog)
