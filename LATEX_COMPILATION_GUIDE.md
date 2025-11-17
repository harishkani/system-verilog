# LaTeX Compilation Guide for SystemVerilog Functions and Tasks

## Available Files

### 1. SystemVerilog_Full_Content_Fixed.tex ⭐ **RECOMMENDED - COMPLETE VERSION**
**Best for:** Everyone - works on ALL LaTeX compilers

**Features:**
- ✅ **2419 lines** of comprehensive content
- ✅ **20+ exercises** with detailed solutions
- ✅ Complete UART transmitter example
- ✅ Complete AXI4-Lite master driver
- ✅ Polymorphism, virtual functions, DPI examples
- ✅ All quizzes with answers
- ✅ Advanced topics: memoization, fork-join, extern
- ✅ Best practices and debugging
- ✅ Uses only basic LaTeX packages
- ✅ **Guaranteed to compile** on all online platforms

**Packages required:**
- inputenc, fontenc, geometry
- listings, xcolor, hyperref
- fancyhdr, titlesec, enumitem
- float, booktabs, array, longtable, multicol

### 2. SystemVerilog_Functions_Tasks_Simple.tex
**Best for:** Quick reference (reduced content)

**Features:**
- Shorter version with basic examples
- Only 767 lines
- Good for quick reference
- Smaller PDF size

### 3. SystemVerilog_Functions_Tasks_Complete.tex
**Best for:** Full LaTeX installations with advanced packages (TeXLive, MikTeX)

**Features:**
- Beautiful colored boxes using tcolorbox
- TikZ diagrams and flowcharts
- pgfplots for graphs
- Professional appearance

**Additional packages required:**
- tcolorbox
- tikz, pgfplots
- amsmath, amssymb

### 4. SystemVerilog_Functions_and_Tasks.tex
**Original:** Basic version in the repository

## How to Compile

### Using Overleaf (Recommended for beginners)
1. Go to https://www.overleaf.com/
2. Create a new project
3. Upload `SystemVerilog_Full_Content_Fixed.tex` ⭐
4. Click "Recompile"
5. Download the PDF

### Using Command Line (if you have LaTeX installed)
```bash
pdflatex SystemVerilog_Full_Content_Fixed.tex
pdflatex SystemVerilog_Full_Content_Fixed.tex  # Run twice for TOC
```

### Using Online LaTeX Editors
- **Overleaf**: https://www.overleaf.com/ (FREE)
- **Papeeria**: https://papeeria.com/ (FREE)
- **LaTeX Base**: https://latexbase.com/ (FREE)

## Common Errors and Solutions

### Error: "tcolorbox.sty not found"
**Solution:** Use `SystemVerilog_Full_Content_Fixed.tex` ⭐ (recommended) or `SystemVerilog_Functions_Tasks_Simple.tex`

### Error: "tikz.sty not found"
**Solution:** Use `SystemVerilog_Full_Content_Fixed.tex` ⭐ (recommended) or `SystemVerilog_Functions_Tasks_Simple.tex`

### Error: "pgfplots.sty not found"
**Solution:** Use `SystemVerilog_Full_Content_Fixed.tex` ⭐ (recommended) or `SystemVerilog_Functions_Tasks_Simple.tex`

### Error: Package conflicts
**Solution:** Make sure you're using a recent LaTeX distribution (TeXLive 2020+)

## Installing Full LaTeX Distribution

### Ubuntu/Debian
```bash
sudo apt-get update
sudo apt-get install texlive-latex-base texlive-latex-extra texlive-fonts-recommended
```

### macOS
```bash
brew install --cask mactex
```

### Windows
Download and install MikTeX from: https://miktex.org/download

## Quick Start for Non-LaTeX Users

**Don't want to install anything?**
1. Go to https://www.overleaf.com/
2. Create a free account
3. Upload `SystemVerilog_Full_Content_Fixed.tex` ⭐
4. Click "Recompile"
5. Your PDF is ready with ALL content!

## File Comparison

| Feature | Full Content Fixed ⭐ | Simple | Complete |
|---------|---------------------|--------|----------|
| Lines of code | 2419 | 767 | 1356 |
| All exercises (20+) | ✓ | Partial | ✓ |
| All solutions | ✓ | Partial | ✓ |
| UART example | ✓ | ✗ | ✓ |
| AXI4-Lite example | ✓ | ✗ | ✓ |
| Advanced topics | ✓ | ✗ | ✓ |
| Colored boxes | Basic | Basic | Professional |
| Diagrams | Text | Text | TikZ graphics |
| Works on all compilers | ✓ | ✓ | ✗ |
| Package requirements | Minimal | Minimal | Extensive |
| Compile time | Medium | Fast | Slower |
| **RECOMMENDED** | **YES** | No | No |

## Troubleshooting

If you encounter compilation errors:
1. Try `SystemVerilog_Functions_Tasks_Simple.tex` first
2. Make sure all lines end properly (no truncated lines)
3. Check that special characters are escaped (%, $, &, #, etc.)
4. Run pdflatex twice to generate table of contents

## Support

For LaTeX help:
- https://www.latex-project.org/help/documentation/
- https://tex.stackexchange.com/

For SystemVerilog content questions:
- Refer to IEEE 1800-2017 standard
