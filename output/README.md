# Output Directory

This directory contains generated documentation from Lean 4 proof files.

Generated files (`.tex` and `.md`) are gitignored and will be created when you run the `narrate-lean` tool.

## Example Usage

To generate documentation for the example files:

```bash
# Generate Markdown
narrate-lean --input examples/basic_proof.lean --output output/basic_proof.md --format markdown

# Generate LaTeX
narrate-lean --input examples/basic_proof.lean --output output/basic_proof.tex --format latex
```
