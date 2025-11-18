#!/usr/bin/env python3
"""
Extract SystemVerilog code from LaTeX files and verify with iverilog
"""

import re
import os
import subprocess
import json
from pathlib import Path
from typing import List, Dict, Tuple

class CodeExtractor:
    def __init__(self, output_dir="extracted_code"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(exist_ok=True)
        self.results = []

    def extract_code_blocks(self, tex_file: str) -> List[Dict]:
        """Extract all lstlisting code blocks from a LaTeX file"""
        with open(tex_file, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()

        # Pattern to match \begin{lstlisting}...\end{lstlisting}
        pattern = r'\\begin\{lstlisting\}(?:\[.*?\])?\s*\n(.*?)\\end\{lstlisting\}'
        matches = re.findall(pattern, content, re.DOTALL)

        code_blocks = []
        for idx, code in enumerate(matches):
            # Clean up the code
            code = code.strip()
            if code and ('module' in code or 'program' in code or 'interface' in code):
                code_blocks.append({
                    'file': tex_file,
                    'index': idx,
                    'code': code,
                    'has_testbench': 'initial' in code or '$display' in code or '$monitor' in code
                })

        return code_blocks

    def is_complete_module(self, code: str) -> bool:
        """Check if code contains a complete module/program definition"""
        has_module = 'module' in code or 'program' in code
        has_endmodule = 'endmodule' in code or 'endprogram' in code
        return has_module and has_endmodule

    def compile_code(self, code: str, filename: str) -> Tuple[bool, str, str]:
        """Compile SystemVerilog code with iverilog"""
        sv_file = self.output_dir / f"{filename}.sv"
        out_file = self.output_dir / f"{filename}.vvp"

        # Write code to file
        with open(sv_file, 'w') as f:
            f.write(code)

        # Try to compile with iverilog
        # Use -g2012 for SystemVerilog support
        cmd = ['iverilog', '-g2012', '-o', str(out_file), str(sv_file)]

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=30
            )

            success = result.returncode == 0
            return success, result.stdout, result.stderr

        except subprocess.TimeoutExpired:
            return False, "", "Compilation timeout"
        except Exception as e:
            return False, "", str(e)

    def run_testbench(self, filename: str) -> Tuple[bool, str, str]:
        """Run compiled testbench with vvp"""
        vvp_file = self.output_dir / f"{filename}.vvp"

        if not vvp_file.exists():
            return False, "", "VVP file not found"

        try:
            result = subprocess.run(
                ['vvp', str(vvp_file)],
                capture_output=True,
                text=True,
                timeout=10
            )

            return True, result.stdout, result.stderr

        except subprocess.TimeoutExpired:
            return False, "", "Execution timeout"
        except Exception as e:
            return False, "", str(e)

    def verify_all_files(self, tex_files: List[str]):
        """Extract and verify all code from LaTeX files"""
        total_blocks = 0
        compiled_success = 0
        compiled_failed = 0

        for tex_file in tex_files:
            print(f"\n{'='*80}")
            print(f"Processing: {tex_file}")
            print(f"{'='*80}")

            code_blocks = self.extract_code_blocks(tex_file)
            print(f"Found {len(code_blocks)} code blocks")

            for block in code_blocks:
                total_blocks += 1
                idx = block['index']
                code = block['code']

                if not self.is_complete_module(code):
                    print(f"\n[SKIP] Block {idx}: Not a complete module")
                    self.results.append({
                        'source_file': tex_file,
                        'block_index': idx,
                        'status': 'skipped',
                        'reason': 'incomplete_module',
                        'code_preview': code[:100]
                    })
                    continue

                filename = f"{Path(tex_file).stem}_block_{idx}"
                print(f"\n[TEST] Block {idx}: {filename}")
                print(f"  Has testbench: {block['has_testbench']}")

                # Compile
                success, stdout, stderr = self.compile_code(code, filename)

                result = {
                    'source_file': tex_file,
                    'block_index': idx,
                    'filename': filename,
                    'has_testbench': block['has_testbench'],
                    'compile_success': success,
                    'compile_stdout': stdout,
                    'compile_stderr': stderr,
                    'code_preview': code[:200]
                }

                if success:
                    compiled_success += 1
                    print(f"  ✓ Compilation PASSED")

                    # If it has testbench, try to run it
                    if block['has_testbench']:
                        run_success, run_stdout, run_stderr = self.run_testbench(filename)
                        result['run_success'] = run_success
                        result['run_stdout'] = run_stdout
                        result['run_stderr'] = run_stderr

                        if run_success:
                            print(f"  ✓ Execution PASSED")
                            if run_stdout:
                                print(f"  Output: {run_stdout[:200]}")
                        else:
                            print(f"  ✗ Execution FAILED: {run_stderr[:200]}")
                else:
                    compiled_failed += 1
                    print(f"  ✗ Compilation FAILED")
                    if stderr:
                        print(f"  Error: {stderr[:300]}")

                self.results.append(result)

        return total_blocks, compiled_success, compiled_failed

    def generate_report(self, output_file="verification_report.md"):
        """Generate a detailed markdown report"""
        report = []
        report.append("# SystemVerilog Code Verification Report\n")
        report.append(f"Generated: {Path.cwd()}\n")
        report.append(f"Tool: Icarus Verilog (iverilog) 12.0\n\n")

        # Summary
        total = len(self.results)
        passed = sum(1 for r in self.results if r.get('compile_success', False))
        failed = sum(1 for r in self.results if r.get('compile_success') == False and r.get('status') != 'skipped')
        skipped = sum(1 for r in self.results if r.get('status') == 'skipped')

        report.append("## Summary\n")
        report.append(f"- **Total code blocks**: {total}\n")
        report.append(f"- **Compilation passed**: {passed} ✓\n")
        report.append(f"- **Compilation failed**: {failed} ✗\n")
        report.append(f"- **Skipped (incomplete)**: {skipped}\n\n")

        # Failed compilations
        if failed > 0:
            report.append("## Failed Compilations\n\n")
            for r in self.results:
                if r.get('compile_success') == False and r.get('status') != 'skipped':
                    report.append(f"### {r['source_file']} - Block {r['block_index']}\n")
                    report.append(f"**File**: `{r.get('filename', 'N/A')}.sv`\n\n")
                    report.append(f"**Error**:\n```\n{r.get('compile_stderr', 'Unknown error')}\n```\n\n")
                    report.append(f"**Code Preview**:\n```systemverilog\n{r['code_preview']}\n```\n\n")

        # Successful compilations
        report.append("## Successful Compilations\n\n")
        for r in self.results:
            if r.get('compile_success') == True:
                report.append(f"- ✓ {r['source_file']} - Block {r['block_index']} (`{r['filename']}.sv`)")
                if r.get('has_testbench') and r.get('run_success'):
                    report.append(" - Testbench executed successfully")
                report.append("\n")

        # Skipped
        if skipped > 0:
            report.append("\n## Skipped (Incomplete Modules)\n\n")
            for r in self.results:
                if r.get('status') == 'skipped':
                    report.append(f"- {r['source_file']} - Block {r['block_index']}: {r.get('reason', 'unknown')}\n")

        # Write report
        report_content = ''.join(report)
        with open(output_file, 'w') as f:
            f.write(report_content)

        # Also save JSON for programmatic access
        with open(output_file.replace('.md', '.json'), 'w') as f:
            json.dump(self.results, f, indent=2)

        return report_content

def main():
    # Find all .tex files
    tex_files = [
        'Complete_SystemVerilog_Guide.tex',
        'SystemVerilog_Advanced_Sections_21_30.tex',
        'SystemVerilog_Complete_Comprehensive_Guide.tex',
        'SystemVerilog_Full_Content_Fixed.tex',
        'SystemVerilog_Functions_Tasks_Complete.tex',
        'SystemVerilog_Functions_Tasks_Complete_Guide.tex',
        'SystemVerilog_Functions_Tasks_Simple.tex',
        'SystemVerilog_Functions_and_Tasks.tex'
    ]

    # Filter to only existing files
    tex_files = [f for f in tex_files if os.path.exists(f)]

    print(f"Found {len(tex_files)} LaTeX files to process")

    extractor = CodeExtractor()
    total, success, failed = extractor.verify_all_files(tex_files)

    print(f"\n\n{'='*80}")
    print("FINAL SUMMARY")
    print(f"{'='*80}")
    print(f"Total code blocks processed: {total}")
    print(f"Successfully compiled: {success}")
    print(f"Failed compilation: {failed}")
    print(f"Success rate: {(success/total*100) if total > 0 else 0:.1f}%")

    # Generate report
    report = extractor.generate_report("verification_report.md")
    print(f"\nDetailed report saved to: verification_report.md")
    print(f"JSON results saved to: verification_report.json")

    return success, failed

if __name__ == "__main__":
    success, failed = main()
    exit(0 if failed == 0 else 1)
