# Narrate Lean

A Python CLI tool that converts Lean 4 proof files into human-readable Markdown documents with natural language explanations.

## Features

- **Parse Lean 4 proofs**: Extracts theorem statements, definitions, hypotheses, and proof steps
- **Natural language narration**: Uses LLMs to generate clear explanations of mathematical proofs
- **LaTeX support**: Preserves mathematical notation using LaTeX syntax
- **Flexible output**: Output to file or stdout
- **Customizable**: Skip definitions or proof details as needed

## Installation

```bash
# Install dependencies
uv sync

# Or with pip
pip install -e .
```

## Configuration

Create a `.env` file with your LLM API configuration:

```bash
# For LiteLLM proxy
LITELLM_API_KEY=your-api-key
LITELLM_BASE_URL=http://your-litellm-server:4000
LLM_MODEL=gpt-4.1

# Or for direct OpenAI API
OPENAI_API_KEY=your-openai-key
LLM_MODEL=gpt-4.1
```

## Usage

### Basic Usage

Convert a Lean proof file to Markdown:

```bash
narratelean narrate input.lean -o output.md
```

Output to stdout:

```bash
narratelean narrate example.lean
```

### Options

- `-o, --output PATH`: Specify output file (default: stdout)
- `--no-definitions`: Skip narrating definitions
- `--no-proofs`: Skip detailed proof narration (only include theorem statements)
- `--explain-lean`: Include explanations of Lean tactics and syntax in the proof (default: pure math only)

### Examples

```bash
# Narrate the example proof (pure math, no Lean explanations)
uv run narratelean narrate example.lean -o example_output.md

# Include Lean tactics explanations
uv run narratelean narrate example.lean --explain-lean -o example_with_lean.md

# Skip definitions, only narrate theorems
uv run narratelean narrate example.lean --no-definitions -o output.md

# Just theorem statements, no detailed proofs
uv run narratelean narrate example.lean --no-proofs -o statements_only.md
```

## Example Files

This repository includes a complete example demonstrating the tool's capabilities:

- **[example.lean](example.lean)** - A Lean 4 proof of the Sequence Squeeze Theorem using Mathlib
- **[example_output.md](example_output.md)** - The generated human-readable mathematical proof in Markdown format

The example showcases:
- Custom definition (`seq_converges_to`) with natural language explanation
- Formal theorem statement with hypotheses and conclusion
- Step-by-step proof narrative in mathematical paper style
- Proper LaTeX notation compatible with KaTeX rendering

## Development

### Running Tests

```bash
make test
```

### Code Quality

```bash
# Format code
make format

# Lint code
make lint

# Type check
make type

# Run all checks
make all
```

## Project Structure

- `src/narratelean/parser.py` - Lean 4 file parser
- `src/narratelean/narrator.py` - LLM-based proof narration engine
- `src/narratelean/markdown.py` - Markdown document generator
- `src/narratelean/cli.py` - Command-line interface

## License

MIT
