# Makefile for compiling SystemVerilog documentation

# Files
COMPLETE_GUIDE = SystemVerilog_Functions_Tasks_Complete_Guide
BASIC_VERSION = SystemVerilog_Functions_and_Tasks

# Default target
all: complete basic

# Compile complete learning guide
complete: $(COMPLETE_GUIDE).pdf

# Compile basic version
basic: $(BASIC_VERSION).pdf

# Pattern rule for PDF compilation
%.pdf: %.tex
	@echo "Compiling $<..."
	@pdflatex -interaction=nonstopmode $< > /dev/null
	@pdflatex -interaction=nonstopmode $< > /dev/null
	@echo "Created $@"

# Clean auxiliary files
clean:
	@echo "Cleaning auxiliary files..."
	@rm -f *.aux *.log *.out *.toc *.lof *.lot
	@echo "Done"

# Clean everything including PDFs
distclean: clean
	@echo "Removing PDFs..."
	@rm -f *.pdf
	@echo "Done"

# Show help
help:
	@echo "Available targets:"
	@echo "  make           - Compile both documents"
	@echo "  make complete  - Compile complete learning guide"
	@echo "  make basic     - Compile basic version"
	@echo "  make clean     - Remove auxiliary files"
	@echo "  make distclean - Remove all generated files"
	@echo "  make help      - Show this help"

.PHONY: all complete basic clean distclean help
