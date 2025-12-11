# narrate-lean

A tool that converts Lean 4 proof scripts into human-readable LaTeX or Markdown documents.

## Overview

`narrate-lean` parses Lean 4 proof files, extracts proof structures, and generates natural language explanations with mathematical notation. The output is well-formatted LaTeX or Markdown, suitable for academic or educational use.

## Features

- Parse Lean 4 proof scripts
- Extract theorem statements, proofs, and definitions
- Generate LaTeX documents with mathematical notation
- Generate Markdown documents for web-based documentation
- Preserve proof structure and logic flow
- Support for custom formatting options

## Installation

```bash
uv pip install -e .
```

## Usage

### Convert Lean file to LaTeX

```bash
narrate-lean --input examples/basic_proof.lean --output output/basic_proof.tex --format latex
```

### Convert Lean file to Markdown

```bash
narrate-lean --input examples/basic_proof.lean --output output/basic_proof.md --format markdown
```

### CLI Options

- `--input`: Path to input Lean 4 file
- `--output`: Path to output file
- `--format`: Output format (latex or markdown)

## Examples

See the `examples/` directory for sample Lean 4 files and the `output/` directory for generated documentation.

## Development

### Run tests

```bash
make test
```

### Format code

```bash
make format
```

### Lint code

```bash
make lint
```

## License

MIT License