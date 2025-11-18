#!/usr/bin/env python3
"""
Analyze verification results and categorize failures
"""

import json
import re
from collections import defaultdict

def categorize_error(stderr):
    """Categorize error messages"""
    if not stderr:
        return "unknown"

    # iverilog limitations (not actual code errors)
    iverilog_limitations = {
        "inside\" expressions not supported": "iverilog_limitation_inside",
        "Constraint declarations not supported": "iverilog_limitation_constraint",
        "Covergroup declarations are not supported": "iverilog_limitation_covergroup",
        "Unpacked structs not supported": "iverilog_limitation_unpacked_struct",
        "randomize() not supported": "iverilog_limitation_randomize",
        "break statements not supported": "iverilog_limitation_break",
        "Overriding the default variable lifetime": "iverilog_limitation_lifetime",
        "Class declarations are not supported": "iverilog_limitation_class",
        "Virtual methods are not supported": "iverilog_limitation_virtual",
        "uvm_macros.svh not found": "iverilog_limitation_uvm",
        "queue expressions are not supported": "iverilog_limitation_queue",
        "associative array indexing not supported": "iverilog_limitation_assoc_array",
        "dynamic array": "iverilog_limitation_dynamic_array",
        "string method": "iverilog_limitation_string_methods",
        "foreach statements are not supported": "iverilog_limitation_foreach",
    }

    for pattern, category in iverilog_limitations.items():
        if pattern in stderr:
            return category

    # Actual errors
    if "syntax error" in stderr:
        # Check if it's due to unsupported features
        if "++" in stderr or "--" in stderr or "Syntax in assignment statement l-value" in stderr:
            return "syntax_increment_operator"
        if "Invalid module item" in stderr or "Invalid class item" in stderr:
            return "syntax_invalid_item"
        return "syntax_error"

    if "Unknown module type" in stderr:
        return "missing_dependency"

    if "This assignment requires an explicit cast" in stderr:
        return "type_mismatch"

    return "other_error"

def main():
    with open("verification_report.json", "r") as f:
        results = json.load(f)

    # Categorize results
    categories = defaultdict(list)
    successful = []

    for r in results:
        if r.get('status') == 'skipped':
            categories['skipped'].append(r)
        elif r.get('compile_success'):
            successful.append(r)
        else:
            category = categorize_error(r.get('compile_stderr', ''))
            categories[category].append(r)

    # Print analysis
    print("=" * 80)
    print("VERIFICATION RESULTS ANALYSIS")
    print("=" * 80)
    print(f"\nTotal Code Blocks: {len(results)}")
    print(f"Successfully Compiled: {len(successful)} ({len(successful)/len(results)*100:.1f}%)")
    print(f"Failed: {sum(len(v) for k, v in categories.items() if k != 'skipped')}")
    print(f"Skipped (incomplete): {len(categories['skipped'])}")

    print("\n" + "=" * 80)
    print("FAILURE BREAKDOWN BY CATEGORY")
    print("=" * 80)

    # Sort categories by count
    sorted_cats = sorted(
        [(k, v) for k, v in categories.items() if k != 'skipped'],
        key=lambda x: len(x[1]),
        reverse=True
    )

    iverilog_limit_count = 0
    actual_error_count = 0

    for category, items in sorted_cats:
        count = len(items)
        is_limitation = category.startswith('iverilog_limitation_')

        if is_limitation:
            iverilog_limit_count += count
            marker = "⚠️  IVERILOG LIMITATION"
        else:
            actual_error_count += count
            marker = "❌ ACTUAL ERROR"

        print(f"\n{marker}")
        print(f"Category: {category}")
        print(f"Count: {count}")

        # Show examples
        if count <= 3:
            for item in items:
                print(f"  - {item['source_file']} Block {item['block_index']}")
        else:
            for item in items[:3]:
                print(f"  - {item['source_file']} Block {item['block_index']}")
            print(f"  ... and {count - 3} more")

    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print(f"✓ Successfully Compiled: {len(successful)}")
    print(f"⚠️  Failed due to iverilog limitations: {iverilog_limit_count}")
    print(f"❌ Failed due to actual code issues: {actual_error_count}")
    print(f"⊘  Skipped (incomplete modules): {len(categories['skipped'])}")

    total_valid_attempts = len(successful) + iverilog_limit_count + actual_error_count
    if total_valid_attempts > 0:
        print(f"\nCode Quality Score (excl. iverilog limitations):")
        print(f"  {len(successful)}/{len(successful) + actual_error_count} = {len(successful)/(len(successful) + actual_error_count)*100:.1f}%")

    # Generate detailed report
    with open("verification_analysis.md", "w") as f:
        f.write("# Verification Analysis Report\n\n")
        f.write("## Executive Summary\n\n")
        f.write(f"- **Total code blocks**: {len(results)}\n")
        f.write(f"- **Successfully compiled**: {len(successful)} ✓\n")
        f.write(f"- **Failed (iverilog limitations)**: {iverilog_limit_count} ⚠️\n")
        f.write(f"- **Failed (actual errors)**: {actual_error_count} ❌\n")
        f.write(f"- **Skipped (incomplete)**: {len(categories['skipped'])}\n\n")

        f.write("## Key Findings\n\n")
        f.write("### iverilog Limitations\n\n")
        f.write("The following advanced SystemVerilog features are NOT supported by iverilog 12.0:\n\n")

        for category, items in sorted_cats:
            if category.startswith('iverilog_limitation_'):
                feature = category.replace('iverilog_limitation_', '').replace('_', ' ').title()
                f.write(f"- **{feature}**: {len(items)} instances\n")

        f.write("\n### Actual Code Issues\n\n")
        f.write("These failures indicate potential code problems:\n\n")

        for category, items in sorted_cats:
            if not category.startswith('iverilog_limitation_'):
                f.write(f"- **{category}**: {len(items)} instances\n")

        f.write("\n## Recommendations\n\n")
        f.write("1. **iverilog limitations** - These are expected and not code errors. Consider:\n")
        f.write("   - Using a commercial simulator (VCS, Questa, Xcelium) for full SystemVerilog support\n")
        f.write("   - Using Verilator for better SystemVerilog support (still has limitations)\n")
        f.write("   - Marking these examples as \"Advanced\" features\n\n")

        f.write("2. **Syntax errors** - Review and fix:\n")
        f.write("   - Increment/decrement operators (++/--) usage\n")
        f.write("   - Array indexing and slicing syntax\n")
        f.write("   - Missing semicolons or malformed statements\n\n")

        f.write("3. **Missing dependencies** - Some modules reference undefined modules\n")
        f.write("   - Add the required module definitions\n")
        f.write("   - Or mark these as partial examples\n\n")

    print("\nDetailed analysis saved to: verification_analysis.md")

    # Create list of files to fix
    print("\n" + "=" * 80)
    print("FILES REQUIRING FIXES (Actual Errors)")
    print("=" * 80)

    files_to_fix = {}
    for category, items in sorted_cats:
        if not category.startswith('iverilog_limitation_') and category != 'skipped':
            for item in items:
                key = f"{item['source_file']}:{item['block_index']}"
                files_to_fix[key] = {
                    'category': category,
                    'error': item.get('compile_stderr', '')[:200],
                    'filename': item.get('filename', ''),
                }

    for idx, (key, info) in enumerate(sorted(files_to_fix.items())[:10], 1):
        print(f"\n{idx}. {key}")
        print(f"   Category: {info['category']}")
        print(f"   File: {info['filename']}.sv")
        print(f"   Error: {info['error']}")

    if len(files_to_fix) > 10:
        print(f"\n... and {len(files_to_fix) - 10} more files to fix")

    return len(files_to_fix)

if __name__ == "__main__":
    errors = main()
    print(f"\nTotal actual errors to fix: {errors}")
