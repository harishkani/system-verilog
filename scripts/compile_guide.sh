#!/bin/bash

# Script to compile SystemVerilog LaTeX documentation
# This handles the compilation process and checks for errors

echo "========================================="
echo "SystemVerilog Documentation Compiler"
echo "========================================="

# Directory setup
LATEX_DIR="latex"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"

# Available documents
COMPREHENSIVE="SystemVerilog_Complete_Comprehensive_Guide"
ADVANCED="SystemVerilog_Advanced_Sections_21_30"

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

# Function to compile a document
compile_doc() {
    local FILE=$1
    local NAME=$2

    echo ""
    echo "Compiling ${NAME}..."
    echo "-----------------------------------------"

    # Change to latex directory
    cd "${REPO_ROOT}/${LATEX_DIR}" || exit 1

    # Clean up previous compilation files
    echo "Cleaning previous build files..."
    rm -f ${FILE}.aux ${FILE}.log ${FILE}.out ${FILE}.toc ${FILE}.pdf ${FILE}.lof ${FILE}.lot

    # First compilation
    echo "Running first pass..."
    pdflatex -interaction=nonstopmode ${FILE}.tex > /dev/null 2>&1
    if [ $? -ne 0 ]; then
        echo "ERROR: First pass failed!"
        echo "Check ${LATEX_DIR}/${FILE}.log for details"
        tail -50 ${FILE}.log
        return 1
    fi

    # Second compilation (for TOC and references)
    echo "Running second pass (for table of contents)..."
    pdflatex -interaction=nonstopmode ${FILE}.tex > /dev/null 2>&1
    if [ $? -ne 0 ]; then
        echo "ERROR: Second pass failed!"
        echo "Check ${LATEX_DIR}/${FILE}.log for details"
        tail -50 ${FILE}.log
        return 1
    fi

    # Check if PDF was created
    if [ -f "${FILE}.pdf" ]; then
        echo "SUCCESS! PDF created: ${LATEX_DIR}/${FILE}.pdf"
        echo "Size: $(ls -lh ${FILE}.pdf | awk '{print $5}')"
        return 0
    else
        echo "ERROR: PDF file was not created!"
        return 1
    fi
}

# Show menu if no arguments
if [ $# -eq 0 ]; then
    echo ""
    echo "Available documents:"
    echo "  1) Comprehensive Guide (all sections 1-30)"
    echo "  2) Advanced Sections (sections 21-30)"
    echo "  3) All documents"
    echo ""
    read -p "Select document to compile (1-3): " choice

    case $choice in
        1) compile_doc "$COMPREHENSIVE" "Comprehensive Guide" ;;
        2) compile_doc "$ADVANCED" "Advanced Sections" ;;
        3)
            compile_doc "$COMPREHENSIVE" "Comprehensive Guide"
            compile_doc "$ADVANCED" "Advanced Sections"
            ;;
        *) echo "Invalid choice"; exit 1 ;;
    esac
else
    # Handle command line arguments
    case $1 in
        comprehensive|1) compile_doc "$COMPREHENSIVE" "Comprehensive Guide" ;;
        advanced|2) compile_doc "$ADVANCED" "Advanced Sections" ;;
        all|3)
            compile_doc "$COMPREHENSIVE" "Comprehensive Guide"
            compile_doc "$ADVANCED" "Advanced Sections"
            ;;
        *)
            echo "Usage: $0 [comprehensive|advanced|all]"
            exit 1
            ;;
    esac
fi

# Return to original directory
cd "${REPO_ROOT}"

echo ""
echo "========================================="
echo "Compilation complete!"
echo "========================================="
echo ""
echo "PDF files are in: ${LATEX_DIR}/"
echo ""
echo "To view PDFs:"
echo "  Linux: xdg-open ${LATEX_DIR}/<filename>.pdf"
echo "  MacOS: open ${LATEX_DIR}/<filename>.pdf"
echo "  Windows: start ${LATEX_DIR}/<filename>.pdf"
echo ""

# Optional cleanup
read -p "Clean up auxiliary files? (y/n) " -n 1 -r
echo
if [[ $REPLY =~ ^[Yy]$ ]]; then
    cd "${REPO_ROOT}/${LATEX_DIR}"
    rm -f *.aux *.log *.out *.toc *.lof *.lot
    echo "Cleaned up auxiliary files"
fi
