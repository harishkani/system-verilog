# LaTeX Compilation Guide for SystemVerilog Functions and Tasks

## Available Files

### 1. SystemVerilog_Functions_Tasks_Simple.tex (RECOMMENDED)
**Best for:** Online LaTeX compilers (Overleaf, ShareLaTeX, etc.)

**Features:**
- Uses only basic LaTeX packages available in all distributions
- Simpler colored boxes without tcolorbox
- No TikZ diagrams (uses text-based descriptions instead)
- **Guaranteed to compile** on most online platforms

**Packages required:**
- inputenc, fontenc, geometry
- listings, xcolor, hyperref
- fancyhdr, titlesec, enumitem
- float, booktabs, array

### 2. SystemVerilog_Functions_Tasks_Complete.tex
**Best for:** Full LaTeX installations (TeXLive, MikTeX)

**Features:**
- Beautiful colored boxes using tcolorbox
- TikZ diagrams and flowcharts
- pgfplots for graphs
- Professional appearance

**Additional packages required:**
- tcolorbox
- tikz, pgfplots
- amsmath, amssymb
- multicol

### 3. SystemVerilog_Functions_and_Tasks.tex
**Original:** Basic version in the repository

## How to Compile

### Using Overleaf (Recommended for beginners)
1. Go to https://www.overleaf.com/
2. Create a new project
3. Upload `SystemVerilog_Functions_Tasks_Simple.tex`
4. Click "Recompile"
5. Download the PDF

### Using Command Line (if you have LaTeX installed)
```bash
pdflatex SystemVerilog_Functions_Tasks_Simple.tex
pdflatex SystemVerilog_Functions_Tasks_Simple.tex  # Run twice for TOC
```

### Using Online LaTeX Editors
- **Overleaf**: https://www.overleaf.com/ (FREE)
- **Papeeria**: https://papeeria.com/ (FREE)
- **LaTeX Base**: https://latexbase.com/ (FREE)

## Common Errors and Solutions

### Error: "tcolorbox.sty not found"
**Solution:** Use `SystemVerilog_Functions_Tasks_Simple.tex` instead

### Error: "tikz.sty not found"
**Solution:** Use `SystemVerilog_Functions_Tasks_Simple.tex` instead

### Error: "pgfplots.sty not found"
**Solution:** Use `SystemVerilog_Functions_Tasks_Simple.tex` instead

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
3. Upload `SystemVerilog_Functions_Tasks_Simple.tex`
4. Click "Recompile"
5. Your PDF is ready!

## File Comparison

| Feature | Simple | Complete |
|---------|--------|----------|
| Basic content | ✓ | ✓ |
| Code examples | ✓ | ✓ |
| Exercises | ✓ | ✓ |
| Solutions | ✓ | ✓ |
| Colored boxes | Basic | Professional |
| Diagrams | Text | TikZ graphics |
| Tables | ✓ | ✓ |
| Compile time | Fast | Slower |
| Package requirements | Minimal | Extensive |

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
