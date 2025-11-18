#!/usr/bin/env python3
"""
Prepare SystemVerilog code for verification on EDA Playground
Generates properly formatted files and creates an HTML guide for batch testing
"""

import re
import os
import json
from pathlib import Path
from typing import List, Dict

class EDAPlaygroundPrep:
    def __init__(self, output_dir="eda_playground_tests"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(exist_ok=True)
        self.test_cases = []

    def extract_code_blocks(self, tex_file: str) -> List[Dict]:
        """Extract all lstlisting code blocks from a LaTeX file"""
        with open(tex_file, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()

        # Pattern to match \begin{lstlisting}...\end{lstlisting}
        pattern = r'\\begin\{lstlisting\}(?:\[.*?\])?\s*\n(.*?)\\end\{lstlisting\}'
        matches = re.findall(pattern, content, re.DOTALL)

        code_blocks = []
        for idx, code in enumerate(matches):
            code = code.strip()
            if code and ('module' in code or 'program' in code or 'interface' in code):
                # Check if it's a complete module
                has_module = 'module' in code or 'program' in code
                has_endmodule = 'endmodule' in code or 'endprogram' in code
                is_complete = has_module and has_endmodule

                code_blocks.append({
                    'file': tex_file,
                    'index': idx,
                    'code': code,
                    'is_complete': is_complete,
                    'has_testbench': 'initial' in code or '$display' in code or '$monitor' in code
                })

        return code_blocks

    def categorize_code(self, code: str) -> Dict[str, bool]:
        """Categorize code by features used"""
        features = {
            'basic_rtl': False,
            'oop': False,
            'constraint': False,
            'uvm': False,
            'assertion': False,
            'coverage': False,
            'interface': False,
            'dynamic_array': False,
            'queue': False,
            'associative_array': False,
        }

        # Basic RTL
        if any(kw in code for kw in ['always_ff', 'always_comb', 'assign', 'module']):
            features['basic_rtl'] = True

        # OOP features
        if any(kw in code for kw in ['class ', 'extends', 'virtual ', 'new(']):
            features['oop'] = True

        # Constraints
        if any(kw in code for kw in ['constraint ', 'randomize', 'rand ', 'randc ']):
            features['constraint'] = True

        # UVM
        if 'uvm_' in code or 'UVM' in code:
            features['uvm'] = True

        # Assertions
        if any(kw in code for kw in ['assert ', 'assume ', 'cover ', 'property ', 'sequence ']):
            features['assertion'] = True

        # Coverage
        if 'covergroup' in code or 'coverpoint' in code:
            features['coverage'] = True

        # Interface
        if 'interface ' in code:
            features['interface'] = True

        # Dynamic arrays
        if 'new[' in code or '= new' in code:
            features['dynamic_array'] = True

        # Queues
        if '[$]' in code:
            features['queue'] = True

        # Associative arrays
        if '[*]' in code or '[string]' in code or '[int]' in code:
            features['associative_array'] = True

        return features

    def get_recommended_simulator(self, features: Dict[str, bool]) -> str:
        """Recommend best simulator based on features"""
        if features['uvm']:
            return "Questa (UVM support)"
        elif features['oop'] or features['constraint']:
            return "VCS or Questa (Full SystemVerilog)"
        elif features['coverage'] or features['assertion']:
            return "VCS or Questa (Verification features)"
        elif features['dynamic_array'] or features['queue']:
            return "VCS, Questa, or Xcelium"
        else:
            return "Icarus Verilog (open source) or any"

    def create_eda_playground_file(self, code_block: Dict, file_id: int) -> str:
        """Create a properly formatted file for EDA Playground"""
        code = code_block['code']
        features = self.categorize_code(code)
        simulator = self.get_recommended_simulator(features)

        # Create header comment
        header = f"""// EDA Playground Test Case #{file_id}
// Source: {code_block['file']} - Block {code_block['index']}
// Recommended Simulator: {simulator}
// Features: {', '.join([k for k, v in features.items() if v])}
//
// To run on EDA Playground:
// 1. Go to https://www.edaplayground.com
// 2. Select Language: SystemVerilog/Verilog
// 3. Select Testbench: SystemVerilog/Verilog
// 4. Select Tools & Simulators: {simulator}
// 5. Paste this code
// 6. Click "Run"

"""

        full_code = header + code

        # Save to file
        filename = f"test_{file_id:03d}_{Path(code_block['file']).stem}_block_{code_block['index']}.sv"
        filepath = self.output_dir / filename

        with open(filepath, 'w') as f:
            f.write(full_code)

        return filename

    def generate_html_guide(self, test_cases: List[Dict]):
        """Generate an interactive HTML guide for testing on EDA Playground"""
        html = """<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>EDA Playground Verification Guide</title>
    <style>
        body {
            font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
            max-width: 1400px;
            margin: 0 auto;
            padding: 20px;
            background-color: #f5f5f5;
        }
        h1 {
            color: #2c3e50;
            border-bottom: 3px solid #3498db;
            padding-bottom: 10px;
        }
        .summary {
            background: white;
            padding: 20px;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
            margin-bottom: 20px;
        }
        .stats {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
            gap: 15px;
            margin: 20px 0;
        }
        .stat-card {
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            padding: 20px;
            border-radius: 8px;
            text-align: center;
        }
        .stat-number {
            font-size: 2.5em;
            font-weight: bold;
        }
        .stat-label {
            font-size: 0.9em;
            margin-top: 5px;
        }
        .test-grid {
            display: grid;
            grid-template-columns: repeat(auto-fill, minmax(350px, 1fr));
            gap: 20px;
            margin-top: 20px;
        }
        .test-card {
            background: white;
            border-radius: 8px;
            padding: 20px;
            box-shadow: 0 2px 8px rgba(0,0,0,0.1);
            transition: transform 0.2s, box-shadow 0.2s;
        }
        .test-card:hover {
            transform: translateY(-2px);
            box-shadow: 0 4px 12px rgba(0,0,0,0.2);
        }
        .test-header {
            font-size: 1.1em;
            font-weight: bold;
            color: #2c3e50;
            margin-bottom: 10px;
        }
        .test-info {
            font-size: 0.9em;
            color: #7f8c8d;
            margin: 5px 0;
        }
        .simulator-badge {
            display: inline-block;
            background: #3498db;
            color: white;
            padding: 4px 12px;
            border-radius: 12px;
            font-size: 0.85em;
            margin: 5px 5px 5px 0;
        }
        .feature-badge {
            display: inline-block;
            background: #2ecc71;
            color: white;
            padding: 3px 10px;
            border-radius: 10px;
            font-size: 0.75em;
            margin: 3px 3px 3px 0;
        }
        .btn {
            display: inline-block;
            background: #3498db;
            color: white;
            padding: 10px 20px;
            border-radius: 5px;
            text-decoration: none;
            margin-top: 10px;
            transition: background 0.3s;
        }
        .btn:hover {
            background: #2980b9;
        }
        .btn-copy {
            background: #27ae60;
            font-size: 0.9em;
            padding: 8px 16px;
            cursor: pointer;
            border: none;
        }
        .btn-copy:hover {
            background: #229954;
        }
        .code-preview {
            background: #f8f9fa;
            border: 1px solid #dee2e6;
            border-radius: 4px;
            padding: 10px;
            margin: 10px 0;
            font-family: 'Courier New', monospace;
            font-size: 0.85em;
            max-height: 150px;
            overflow-y: auto;
        }
        .filter-section {
            background: white;
            padding: 15px;
            border-radius: 8px;
            margin-bottom: 20px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }
        .filter-btn {
            background: #ecf0f1;
            color: #2c3e50;
            border: 2px solid #bdc3c7;
            padding: 8px 16px;
            border-radius: 5px;
            margin: 5px;
            cursor: pointer;
            transition: all 0.3s;
        }
        .filter-btn.active {
            background: #3498db;
            color: white;
            border-color: #3498db;
        }
        .copy-notification {
            position: fixed;
            top: 20px;
            right: 20px;
            background: #27ae60;
            color: white;
            padding: 15px 25px;
            border-radius: 5px;
            box-shadow: 0 4px 12px rgba(0,0,0,0.3);
            display: none;
            z-index: 1000;
        }
    </style>
</head>
<body>
    <h1>🚀 EDA Playground Verification Guide</h1>

    <div class="summary">
        <h2>Overview</h2>
        <p>This guide helps you verify SystemVerilog code examples using EDA Playground, an online simulator platform that supports multiple tools including commercial simulators.</p>

        <div class="stats">
            <div class="stat-card">
                <div class="stat-number">__TOTAL_TESTS__</div>
                <div class="stat-label">Total Test Cases</div>
            </div>
            <div class="stat-card" style="background: linear-gradient(135deg, #f093fb 0%, #f5576c 100%);">
                <div class="stat-number">__BASIC_RTL__</div>
                <div class="stat-label">Basic RTL Tests</div>
            </div>
            <div class="stat-card" style="background: linear-gradient(135deg, #4facfe 0%, #00f2fe 100%);">
                <div class="stat-number">__ADVANCED__</div>
                <div class="stat-label">Advanced Features</div>
            </div>
            <div class="stat-card" style="background: linear-gradient(135deg, #43e97b 0%, #38f9d7 100%);">
                <div class="stat-number">__WITH_TB__</div>
                <div class="stat-label">With Testbenches</div>
            </div>
        </div>

        <h3>Quick Start</h3>
        <ol>
            <li>Click on any test case below</li>
            <li>Click "Copy Code" button</li>
            <li>Go to <a href="https://www.edaplayground.com" target="_blank">EDA Playground</a></li>
            <li>Select the recommended simulator from the dropdown</li>
            <li>Paste the code into the editor</li>
            <li>Click "Run" button</li>
            <li>Check the output in the console</li>
        </ol>
    </div>

    <div class="filter-section">
        <h3>Filter Tests:</h3>
        <button class="filter-btn active" onclick="filterTests('all')">All Tests</button>
        <button class="filter-btn" onclick="filterTests('basic_rtl')">Basic RTL</button>
        <button class="filter-btn" onclick="filterTests('oop')">OOP</button>
        <button class="filter-btn" onclick="filterTests('constraint')">Constraints</button>
        <button class="filter-btn" onclick="filterTests('uvm')">UVM</button>
        <button class="filter-btn" onclick="filterTests('has_testbench')">Has Testbench</button>
    </div>

    <div class="test-grid" id="testGrid">
__TEST_CARDS__
    </div>

    <div class="copy-notification" id="copyNotification">
        ✓ Code copied to clipboard!
    </div>

    <script>
        function copyCode(testId) {
            const codeElement = document.getElementById('code-' + testId);
            const code = codeElement.getAttribute('data-code');

            navigator.clipboard.writeText(code).then(function() {
                const notification = document.getElementById('copyNotification');
                notification.style.display = 'block';
                setTimeout(function() {
                    notification.style.display = 'none';
                }, 2000);
            });
        }

        function filterTests(filter) {
            const cards = document.querySelectorAll('.test-card');
            const buttons = document.querySelectorAll('.filter-btn');

            buttons.forEach(btn => btn.classList.remove('active'));
            event.target.classList.add('active');

            cards.forEach(card => {
                if (filter === 'all') {
                    card.style.display = 'block';
                } else if (filter === 'has_testbench') {
                    card.style.display = card.classList.contains('has-testbench') ? 'block' : 'none';
                } else {
                    card.style.display = card.classList.contains(filter) ? 'block' : 'none';
                }
            });
        }

        function openInEDA(filename) {
            // Note: EDA Playground doesn't support direct URL parameters for code
            // So we just open the site and user pastes the code
            window.open('https://www.edaplayground.com', '_blank');
        }
    </script>
</body>
</html>
"""

        # Generate test cards
        cards_html = ""
        basic_rtl_count = 0
        advanced_count = 0
        with_tb_count = 0

        for idx, test in enumerate(test_cases):
            features = test['features']
            feature_classes = ' '.join([k for k, v in features.items() if v])
            if test['has_testbench']:
                feature_classes += ' has-testbench'

            if features['basic_rtl']:
                basic_rtl_count += 1
            if features['oop'] or features['constraint'] or features['uvm']:
                advanced_count += 1
            if test['has_testbench']:
                with_tb_count += 1

            feature_badges = ''.join([
                f'<span class="feature-badge">{k.replace("_", " ").title()}</span>'
                for k, v in features.items() if v
            ])

            # Read the actual code
            with open(self.output_dir / test['filename'], 'r') as f:
                code_content = f.read()

            # Code preview (first 5 lines)
            code_lines = code_content.split('\n')
            preview_lines = [line for line in code_lines if not line.strip().startswith('//')][:5]
            preview = '<br>'.join(preview_lines[:5])

            card = f"""
        <div class="test-card {feature_classes}">
            <div class="test-header">Test #{idx+1}: {test['filename']}</div>
            <div class="test-info">Source: {test['source_file']} - Block {test['block_index']}</div>
            <div style="margin: 10px 0;">
                <span class="simulator-badge">{test['simulator']}</span>
            </div>
            <div style="margin: 10px 0;">
                {feature_badges}
            </div>
            <div class="code-preview" id="code-{idx}" data-code="{code_content.replace('"', '&quot;').replace('<', '&lt;').replace('>', '&gt;')}">
                {preview}<br>...
            </div>
            <button class="btn btn-copy" onclick="copyCode({idx})">📋 Copy Code</button>
            <a href="https://www.edaplayground.com" target="_blank" class="btn">Open EDA Playground →</a>
        </div>
"""
            cards_html += card

        # Replace placeholders
        html = html.replace('__TOTAL_TESTS__', str(len(test_cases)))
        html = html.replace('__BASIC_RTL__', str(basic_rtl_count))
        html = html.replace('__ADVANCED__', str(advanced_count))
        html = html.replace('__WITH_TB__', str(with_tb_count))
        html = html.replace('__TEST_CARDS__', cards_html)

        # Save HTML file
        with open(self.output_dir / 'index.html', 'w') as f:
            f.write(html)

    def process_all_files(self, tex_files: List[str]):
        """Process all LaTeX files and create EDA Playground test cases"""
        file_id = 1

        for tex_file in tex_files:
            print(f"Processing: {tex_file}")
            code_blocks = self.extract_code_blocks(tex_file)

            for block in code_blocks:
                if not block['is_complete']:
                    continue

                features = self.categorize_code(block['code'])
                simulator = self.get_recommended_simulator(features)

                filename = self.create_eda_playground_file(block, file_id)

                self.test_cases.append({
                    'id': file_id,
                    'filename': filename,
                    'source_file': tex_file,
                    'block_index': block['index'],
                    'simulator': simulator,
                    'features': features,
                    'has_testbench': block['has_testbench']
                })

                file_id += 1

        print(f"\nCreated {len(self.test_cases)} test cases")

        # Generate HTML guide
        print("Generating HTML guide...")
        self.generate_html_guide(self.test_cases)

        # Save metadata
        with open(self.output_dir / 'test_cases.json', 'w') as f:
            json.dump(self.test_cases, f, indent=2)

        return self.test_cases


def main():
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

    print("="*80)
    print("EDA PLAYGROUND TEST PREPARATION")
    print("="*80)
    print(f"\nProcessing {len(tex_files)} LaTeX files...\n")

    prep = EDAPlaygroundPrep()
    test_cases = prep.process_all_files(tex_files)

    print("\n" + "="*80)
    print("SUMMARY")
    print("="*80)
    print(f"Total test cases created: {len(test_cases)}")
    print(f"Output directory: eda_playground_tests/")
    print(f"\nFiles created:")
    print(f"  - {len(test_cases)} .sv test files")
    print(f"  - index.html (Interactive guide)")
    print(f"  - test_cases.json (Metadata)")
    print("\n" + "="*80)
    print("NEXT STEPS")
    print("="*80)
    print("1. Open eda_playground_tests/index.html in your browser")
    print("2. Click on any test case")
    print("3. Click 'Copy Code' button")
    print("4. Go to https://www.edaplayground.com")
    print("5. Select the recommended simulator")
    print("6. Paste and run!")
    print("\nOr use the individual .sv files in eda_playground_tests/")

if __name__ == "__main__":
    main()
