# LaTeX Compilation Guide

This guide helps you compile the SystemVerilog documentation to PDF.

## Quick Start

### Method 1: Using the Compilation Script (Recommended)
```bash
./compile_guide.sh
```

This script will:
- Check if pdflatex is installed
- Compile the document twice (for table of contents)
- Report any errors with helpful messages
- Show the output PDF location

### Method 2: Using Make
```bash
# Compile complete learning guide
make complete

# Compile basic version
make basic

# Compile both
make

# Clean auxiliary files
make clean
```

### Method 3: Manual Compilation
```bash
# For the Complete Learning Guide
pdflatex SystemVerilog_Functions_Tasks_Complete_Guide.tex
pdflatex SystemVerilog_Functions_Tasks_Complete_Guide.tex  # Run twice for TOC

# For the Basic Version
pdflatex SystemVerilog_Functions_and_Tasks.tex
pdflatex SystemVerilog_Functions_and_Tasks.tex  # Run twice for TOC
```

## Installing LaTeX

### Ubuntu/Debian
```bash
# Minimal installation (faster, ~500MB)
sudo apt-get update
sudo apt-get install texlive texlive-latex-extra texlive-pictures

# Full installation (recommended, ~5GB - includes everything)
sudo apt-get install texlive-full
```

### macOS
```bash
# Using Homebrew
brew install --cask mactex

# Or download from: https://www.tug.org/mactex/
```

### Windows
1. Download MiKTeX from: https://miktex.org/download
2. Run the installer
3. MiKTeX will automatically download missing packages when needed

### Arch Linux
```bash
sudo pacman -S texlive-most texlive-pictures
```

### Fedora/RHEL
```bash
sudo dnf install texlive-scheme-full
```

## Required Packages

The Complete Learning Guide requires these LaTeX packages:

### Core Packages (usually pre-installed)
- inputenc, fontenc
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

### Additional Packages
- **tikz** - For diagrams (essential)
- **pgfplots** - For plots
- **amsmath, amssymb** - For mathematical symbols
- **tcolorbox** - For colored boxes (exercises, solutions, tips)
- **multicol** - For multi-column layout

All these are included in `texlive-full` (Linux) or MacTeX/MiKTeX.

## Recent Fixes for Online Compilers

**Version 2.1 Update**: The document has been updated to fix compilation issues on online LaTeX compilers:

✅ **Fixed Issues:**
- Added `upquote` package for proper apostrophe handling in code
- Replaced Unicode arrow symbols (→) with `$\rightarrow$`
- Replaced degree symbols (°) with `$^\circ$`
- Replaced multiplication symbols (×) with `$\times$`
- Enhanced listings configuration for better code display

The document now compiles successfully on:
- ✅ Overleaf
- ✅ ShareLaTeX
- ✅ Papeeria
- ✅ Local LaTeX installations
- ✅ TeX Live
- ✅ MiKTeX

## Troubleshooting

### Issue: "pdflatex: command not found"
**Solution**: LaTeX is not installed. Follow the installation instructions above.

### Issue: "! LaTeX Error: File `tikz.sty' not found"
**Solution**: Missing TikZ package.
```bash
# Ubuntu/Debian
sudo apt-get install texlive-pictures

# Or install full distribution
sudo apt-get install texlive-full
```

### Issue: "! LaTeX Error: File `tcolorbox.sty' not found"
**Solution**: Missing tcolorbox package.
```bash
# Ubuntu/Debian
sudo apt-get install texlive-latex-extra
```

### Issue: Compilation stops with errors
**Solution**:
1. Check the `.log` file for specific error messages
2. Make sure you're running pdflatex **twice** (for table of contents)
3. Try cleaning auxiliary files: `make clean` or `rm *.aux *.toc *.out`

### Issue: "Undefined control sequence" errors
**Solution**: This usually means a missing package. Check the `.log` file to see which package is missing.

### Issue: PDF is created but diagrams are missing
**Solution**:
- TikZ libraries might be missing
- Install full TeX distribution: `sudo apt-get install texlive-full`

### Issue: Out of memory errors
**Solution**:
- Close other applications
- Compile one document at a time
- Increase TeX memory limits (advanced)

### Issue: Still getting errors after fixes
**Solution**:
1. Make sure you have the latest version from the repository
2. Clear all auxiliary files: `make clean` or `rm *.aux *.toc *.out *.log`
3. Try compiling twice: `pdflatex file.tex && pdflatex file.tex`
4. Check you have the `upquote` package: `tlmgr install upquote` (if using TeX Live)
5. If using Overleaf, make sure compiler is set to "pdfLaTeX" not "LaTeX"

## Verifying Successful Compilation

After compilation, you should see:
```
SystemVerilog_Functions_Tasks_Complete_Guide.pdf
```

Check the file:
```bash
# Linux
ls -lh SystemVerilog_Functions_Tasks_Complete_Guide.pdf

# Should show something like: ~2-3MB for complete guide
```

View the PDF:
```bash
# Linux
xdg-open SystemVerilog_Functions_Tasks_Complete_Guide.pdf

# macOS
open SystemVerilog_Functions_Tasks_Complete_Guide.pdf

# Windows
start SystemVerilog_Functions_Tasks_Complete_Guide.pdf
```

## Understanding the Build Process

LaTeX compilation happens in two passes:

### First Pass
- Processes all content
- Creates table of contents data (`.toc` file)
- Creates cross-reference data
- May show "undefined references" warnings (normal)

### Second Pass
- Includes table of contents
- Resolves all cross-references
- Produces final PDF
- Should have no warnings

## File Extensions Explained

After compilation, you'll see several files:

- `.tex` - Source LaTeX file (input)
- `.pdf` - Compiled PDF (output) ← **This is what you want!**
- `.aux` - Auxiliary file (can be deleted)
- `.log` - Compilation log (useful for debugging)
- `.toc` - Table of contents data (can be deleted)
- `.out` - Hyperlink data (can be deleted)

You can safely delete `.aux`, `.toc`, `.out` files after successful compilation:
```bash
make clean
# or
rm *.aux *.toc *.out *.log
```

## Advanced Compilation Options

### Using XeLaTeX (for advanced fonts)
```bash
xelatex SystemVerilog_Functions_Tasks_Complete_Guide.tex
xelatex SystemVerilog_Functions_Tasks_Complete_Guide.tex
```

### Using LuaLaTeX (for Lua scripting)
```bash
lualatex SystemVerilog_Functions_Tasks_Complete_Guide.tex
lualatex SystemVerilog_Functions_Tasks_Complete_Guide.tex
```

### Silent compilation (no output)
```bash
pdflatex -interaction=batchmode SystemVerilog_Functions_Tasks_Complete_Guide.tex
```

### Stop on error (interactive)
```bash
pdflatex -interaction=errorstopmode SystemVerilog_Functions_Tasks_Complete_Guide.tex
```

## Online Compilation (No Installation Required)

If you can't or don't want to install LaTeX locally:

### Overleaf
1. Go to: https://www.overleaf.com
2. Create free account
3. New Project → Upload Project
4. Upload the `.tex` file
5. Click "Recompile"
6. Download PDF

### ShareLaTeX / Papeeria
Similar online LaTeX editors with free tiers.

**Note**: Upload all `.tex` files and ensure the online editor has the required packages enabled.

## Tips for Faster Compilation

1. **Use draft mode** (for editing):
   ```latex
   \documentclass[draft]{article}
   ```
   This skips image generation for faster compilation.

2. **Compile only specific sections**:
   Comment out sections you're not currently editing.

3. **Use latexmk** (handles multiple passes automatically):
   ```bash
   latexmk -pdf SystemVerilog_Functions_Tasks_Complete_Guide.tex
   ```

## Need Help?

If you encounter issues not covered here:

1. Check the `.log` file for specific errors
2. Search the error message online (LaTeX errors are well-documented)
3. Try the TeX StackExchange: https://tex.stackexchange.com/
4. Ensure you have the latest version of your TeX distribution

## Minimal Working Example

To test if your LaTeX installation works:

```bash
# Create test file
cat > test.tex << 'EOF'
\documentclass{article}
\usepackage{tikz}
\begin{document}
Hello, LaTeX!
\begin{tikzpicture}
  \draw (0,0) -- (1,1);
\end{tikzpicture}
\end{document}
EOF

# Compile
pdflatex test.tex

# If this works, your installation is good!
```

## Success Checklist

- [ ] LaTeX installed
- [ ] pdflatex command available
- [ ] Required packages installed
- [ ] Compilation runs without errors
- [ ] PDF file created
- [ ] PDF opens and displays correctly
- [ ] Table of contents shows up
- [ ] Diagrams and images display
- [ ] Colored boxes appear
- [ ] Code listings are syntax highlighted

If all items are checked, you're ready to go!
