#!/bin/bash

# Script to compile the SystemVerilog Complete Learning Guide
# This handles the compilation process and checks for errors

echo "========================================="
echo "Compiling SystemVerilog Complete Guide"
echo "========================================="

FILE="SystemVerilog_Functions_Tasks_Complete_Guide"

# Check if pdflatex is available
if ! command -v pdflatex &> /dev/null; then
    echo "ERROR: pdflatex not found!"
    echo ""
    echo "Please install a LaTeX distribution:"
    echo "  - Ubuntu/Debian: sudo apt-get install texlive-full"
    echo "  - MacOS: brew install --cask mactex"
    echo "  - Windows: Install MiKTeX from miktex.org"
    exit 1
fi

# Clean up previous compilation files
echo "Cleaning previous build files..."
rm -f ${FILE}.aux ${FILE}.log ${FILE}.out ${FILE}.toc ${FILE}.pdf

# First compilation
echo ""
echo "Running first pass..."
pdflatex -interaction=nonstopmode ${FILE}.tex > /dev/null 2>&1
if [ $? -ne 0 ]; then
    echo "ERROR: First pass failed!"
    echo "Check ${FILE}.log for details"
    tail -50 ${FILE}.log
    exit 1
fi

# Second compilation (for TOC and references)
echo "Running second pass (for table of contents)..."
pdflatex -interaction=nonstopmode ${FILE}.tex > /dev/null 2>&1
if [ $? -ne 0 ]; then
    echo "ERROR: Second pass failed!"
    echo "Check ${FILE}.log for details"
    tail -50 ${FILE}.log
    exit 1
fi

# Check if PDF was created
if [ -f "${FILE}.pdf" ]; then
    echo ""
    echo "========================================="
    echo "SUCCESS! PDF created successfully"
    echo "========================================="
    echo "Output file: ${FILE}.pdf"
    echo "Size: $(ls -lh ${FILE}.pdf | awk '{print $5}')"
    echo ""
    echo "To view the PDF:"
    echo "  Linux: xdg-open ${FILE}.pdf"
    echo "  MacOS: open ${FILE}.pdf"
    echo "  Windows: start ${FILE}.pdf"
else
    echo "ERROR: PDF file was not created!"
    exit 1
fi

# Clean up auxiliary files (optional)
read -p "Clean up auxiliary files? (y/n) " -n 1 -r
echo
if [[ $REPLY =~ ^[Yy]$ ]]; then
    rm -f ${FILE}.aux ${FILE}.log ${FILE}.out ${FILE}.toc
    echo "Cleaned up auxiliary files"
fi
