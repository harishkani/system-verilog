# Makefile for compiling SystemVerilog documentation

# Directories
LATEX_DIR = latex
OUTPUT_DIR = $(LATEX_DIR)

# Files
COMPREHENSIVE_GUIDE = SystemVerilog_Complete_Comprehensive_Guide
ADVANCED_SECTIONS = SystemVerilog_Advanced_Sections_21_30

# Default target
all: comprehensive advanced

# Compile comprehensive guide
comprehensive: $(OUTPUT_DIR)/$(COMPREHENSIVE_GUIDE).pdf

# Compile advanced sections
advanced: $(OUTPUT_DIR)/$(ADVANCED_SECTIONS).pdf

# Pattern rule for PDF compilation
$(OUTPUT_DIR)/%.pdf: $(LATEX_DIR)/%.tex
	@echo "Compiling $<..."
	@cd $(LATEX_DIR) && pdflatex -interaction=nonstopmode $(notdir $<) > /dev/null
	@cd $(LATEX_DIR) && pdflatex -interaction=nonstopmode $(notdir $<) > /dev/null
	@echo "Created $@"

# Clean auxiliary files
clean:
	@echo "Cleaning auxiliary files..."
	@rm -f $(LATEX_DIR)/*.aux $(LATEX_DIR)/*.log $(LATEX_DIR)/*.out $(LATEX_DIR)/*.toc $(LATEX_DIR)/*.lof $(LATEX_DIR)/*.lot
	@echo "Done"

# Clean everything including PDFs
distclean: clean
	@echo "Removing PDFs..."
	@rm -f $(LATEX_DIR)/*.pdf
	@echo "Done"

# Show help
help:
	@echo "Available targets:"
	@echo "  make                - Compile all documents"
	@echo "  make comprehensive  - Compile comprehensive SystemVerilog guide"
	@echo "  make advanced       - Compile advanced sections (21-30)"
	@echo "  make clean          - Remove auxiliary files"
	@echo "  make distclean      - Remove all generated files"
	@echo "  make help           - Show this help"

.PHONY: all comprehensive advanced clean distclean help
