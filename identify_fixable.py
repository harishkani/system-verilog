#!/usr/bin/env python3
"""Identify fixable errors from verification results"""

import json

with open('verification_report.json', 'r') as f:
    results = json.load(f)

# Find fixable errors (not iverilog limitations)
fixable = []

for r in results:
    if not r.get('compile_success') and r.get('status') != 'skipped':
        stderr = r.get('compile_stderr', '')

        # Skip iverilog limitations
        skip_patterns = [
            'constraint', 'randomize', 'inside', 'Covergroup',
            'Class declarations', 'Virtual methods', 'uvm_macros',
            'Unpacked structs', 'break statements', 'foreach',
            'Overriding the default variable lifetime', 'not supported',
            'queue expressions', 'associative array', 'dynamic array'
        ]

        is_limitation = any(p.lower() in stderr.lower() for p in skip_patterns)

        if not is_limitation:
            fixable.append({
                'file': r['source_file'],
                'block': r['block_index'],
                'filename': r.get('filename', 'unknown'),
                'error': stderr,
                'code_preview': r.get('code_preview', '')
            })

print(f'Found {len(fixable)} potentially fixable errors\n')
print('='*80)

# Group by error type
increment_errors = []
syntax_errors = []
type_errors = []
missing_deps = []
other_errors = []

for err in fixable:
    stderr = err['error']
    if 'Syntax in assignment statement l-value' in stderr or '++' in stderr or '--' in stderr:
        increment_errors.append(err)
    elif 'explicit cast' in stderr:
        type_errors.append(err)
    elif 'Unknown module type' in stderr:
        missing_deps.append(err)
    elif 'syntax error' in stderr:
        syntax_errors.append(err)
    else:
        other_errors.append(err)

print(f'Increment/decrement operator issues: {len(increment_errors)}')
print(f'Type cast issues: {len(type_errors)}')
print(f'Missing dependencies: {len(missing_deps)}')
print(f'Syntax errors: {len(syntax_errors)}')
print(f'Other errors: {len(other_errors)}')

print('\n' + '='*80)
print('SAMPLE FIXABLE ERRORS:')
print('='*80)

# Show examples from each category
if increment_errors:
    print(f'\n1. INCREMENT/DECREMENT OPERATORS ({len(increment_errors)} total)')
    for err in increment_errors[:3]:
        print(f'\n   {err["file"]} Block {err["block"]}')
        print(f'   File: {err["filename"]}.sv')

if type_errors:
    print(f'\n2. TYPE CAST ISSUES ({len(type_errors)} total)')
    for err in type_errors[:3]:
        print(f'\n   {err["file"]} Block {err["block"]}')
        print(f'   File: {err["filename"]}.sv')
        print(f'   Error: {err["error"][:200]}')

if missing_deps:
    print(f'\n3. MISSING DEPENDENCIES ({len(missing_deps)} total)')
    for err in missing_deps:
        print(f'\n   {err["file"]} Block {err["block"]}')
        print(f'   File: {err["filename"]}.sv')

if syntax_errors[:3]:
    print(f'\n4. SYNTAX ERRORS ({len(syntax_errors)} total)')
    for err in syntax_errors[:3]:
        print(f'\n   {err["file"]} Block {err["block"]}')
        print(f'   File: {err["filename"]}.sv')
        print(f'   Error: {err["error"][:200]}')
