# SystemVerilog Functions and Tasks - Comprehensive Guide

This repository contains comprehensive documentation on SystemVerilog functions and tasks, from beginner to advanced levels.

## Available Formats

1. **Markdown**: `SystemVerilog_Functions_and_Tasks.md`
   - Easy to read in any text editor or on GitHub
   - Contains all examples and explanations

2. **LaTeX/PDF**: `SystemVerilog_Functions_and_Tasks.tex`
   - Professional typeset document
   - Includes syntax-highlighted code examples
   - Ready for printing or academic use

## Compiling the LaTeX Document

To compile the LaTeX document to PDF:

### Method 1: Using pdflatex (Recommended)
```bash
pdflatex SystemVerilog_Functions_and_Tasks.tex
pdflatex SystemVerilog_Functions_and_Tasks.tex  # Run twice for TOC
```

### Method 2: Using latexmk (Automated)
```bash
latexmk -pdf SystemVerilog_Functions_and_Tasks.tex
```

### Method 3: Using XeLaTeX
```bash
xelatex SystemVerilog_Functions_and_Tasks.tex
xelatex SystemVerilog_Functions_and_Tasks.tex  # Run twice for TOC
```

### Required LaTeX Packages

The following LaTeX packages are required (usually included in TeX distributions):
- inputenc
- fontenc
- geometry
- listings
- xcolor
- hyperref
- graphicx
- fancyhdr
- tocloft
- titlesec
- enumitem
- float
- booktabs
- array
- longtable

These are typically included in standard TeX distributions like:
- **TeX Live** (Linux/Mac)
- **MiKTeX** (Windows)
- **MacTeX** (macOS)

## Document Contents

### Beginner Level
- Basic functions and tasks
- Parameter passing modes (input, output, inout)
- Void functions
- Tasks with timing control
- Simple practical examples

### Intermediate Level
- Default arguments
- Output and reference (ref) parameters
- Automatic vs static storage
- Reentrant tasks
- Class methods
- Functions returning complex types

### Advanced Level
- Virtual functions and polymorphism
- Pure virtual functions (abstract classes)
- Function chaining and fluent interfaces
- Parameterized functions
- Fork-join parallelism
- Extern declarations
- Recursive functions with memoization
- DPI (C/C++ integration)
- Constraint and coverage functions
- Protocol driver implementations

### Additional Sections
- Best practices for writing functions and tasks
- Common pitfalls and how to avoid them
- Performance optimization tips
- When to use functions vs tasks

## Features

- **30+ Complete Examples**: All examples are runnable SystemVerilog code
- **Comprehensive Coverage**: From basic syntax to advanced OOP concepts
- **Practical Focus**: Real-world patterns and use cases
- **Professional Quality**: Publication-ready LaTeX formatting

## Usage

### For Learning
Start with the beginner section and progress through intermediate to advanced topics. Each section builds on previous concepts.

### As Reference
Use the table of contents to jump to specific topics. The markdown version is great for quick reference, while the PDF is better for in-depth study.

### For Teaching
The document can be used as course material or supplementary reading for HDL or verification courses.

## License

This documentation is provided for educational purposes.

## Contributing

Suggestions and improvements are welcome! Please submit issues or pull requests.

## Additional Resources

- IEEE 1800-2017 SystemVerilog Standard
- *SystemVerilog for Verification* (3rd Edition) by Chris Spear
- *Writing Testbenches using SystemVerilog* by Janick Bergeron

---

**Document Version**: 1.0
**Last Updated**: 2025
