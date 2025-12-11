# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**narratelean** is a Python-based CLI tool that converts Lean 4 proof files into human-readable Markdown documents. It uses LLMs to generate natural language explanations of theorem statements, definitions, and proof steps, preserving mathematical notation using LaTeX syntax.

## Development Commands

### Package Management
- **Install dependencies**: `uv sync` (uv is the package manager)
- **Run CLI**: `uv run narratelean --help` (calls `narratelean.cli:app`)
- **Narrate Lean file**: `uv run narratelean narrate sample.lean -o output.md`
- **With Lean explanations**: `uv run narratelean narrate sample.lean --explain-lean -o output.md`
- **Skip definitions**: `uv run narratelean narrate sample.lean --no-definitions -o output.md`
- **Skip proofs**: `uv run narratelean narrate sample.lean --no-proofs -o output.md`
- **Single test**: `uv run pytest -v -s tests/test_hello.py`

### Quality Checks
- **Format**: `make format` (uses ruff)
- **Lint**: `make lint` (uses ruff with auto-fix)
- **Type check**: `make type` (uses ty)
- **Test**: `make test` (pytest with coverage)
- **All checks**: `make all` (runs format, lint, type, test)

### Building & Publishing
- **Build wheel**: `uv build -f wheel`
- **Publish**: `make publish` (builds and publishes)

## Code Architecture

### Python Structure
- **Entry point**: [`src/narratelean/cli.py`](src/narratelean/cli.py) - Typer-based CLI with `narrate` and `version` commands
- **Parser**: [`src/narratelean/parser.py`](src/narratelean/parser.py) - Extracts theorems, definitions, and proof steps from Lean files
- **Narrator**: [`src/narratelean/narrator.py`](src/narratelean/narrator.py) - Uses LLM to generate natural language explanations
- **Markdown Generator**: [`src/narratelean/markdown.py`](src/narratelean/markdown.py) - Creates structured Markdown output with LaTeX
- **Logger setup**: [`src/narratelean/__init__.py`](src/narratelean/__init__.py) - Configures loguru with `LOGURU_LEVEL` env var
- **Tests**: [`tests/`](tests/) directory with pytest

### Dependencies
- **CLI**: typer (command-line interface)
- **Logging**: loguru (configured via `LOGURU_LEVEL` env var)
- **LLM API**: openai library (configured via `.env` with LiteLLM proxy)
- **Env management**: python-dotenv

### LLM Configuration
Project uses LiteLLM proxy for LLM API access. Configuration in `.env`:
- `LITELLM_API_KEY` - API key for LiteLLM proxy (required)
- `LITELLM_BASE_URL` - LiteLLM proxy endpoint (default: http://192.168.1.200:4000)
- `LLM_MODEL` - Model name to use (default: "gpt-4.1", set based on your LiteLLM setup)
- Alternative: `OPENAI_API_KEY` (can use direct OpenAI API instead of LiteLLM)

### Lean 4 Integration
- **Sample proof**: [`sample.lean`](sample.lean) - Demonstrates sequence squeeze theorem using Mathlib
- **Parser capabilities**: Extracts imports, definitions, theorems, hypotheses, and proof steps
- **Narration approach**: Uses LLM to convert formal Lean proofs into natural language with LaTeX notation

#### Narration Modes

The narrator supports two distinct modes controlled by the `--explain-lean` flag:

1. **Pure Mathematical Proofs (default)**:
   - Generates proofs in the style of published mathematical papers
   - No mention of Lean tactics or syntax
   - Focuses purely on mathematical reasoning
   - Structured with step headers (Step 1, Step 2, etc.)
   - Ends with ∎ or "This completes the proof."

2. **With Lean Explanations (`--explain-lean`)**:
   - Includes detailed explanations of Lean tactics
   - Shows Lean code blocks for each tactic
   - Explains what each tactic does and why
   - Useful for learning Lean while understanding proofs

#### LaTeX/KaTeX Constraints

**CRITICAL**: All LLM prompts must enforce strict KaTeX compatibility for Markdown rendering.

**Required LaTeX format**:
- **Inline math**: `$...$` (e.g., `$\epsilon > 0$`, `$|a_n - L| < \epsilon$`, `$n \geq N$`)
- **Display equations**: `$$...$$` on separate lines
- **Double braces**: All subscripts/superscripts must use double braces (e.g., `$a_{n}$`, `$\lim_{n \to \infty}$`)

**Allowed LaTeX commands** (basic only):
- `$\forall$`, `$\exists$`, `$\epsilon$`, `$\leq$`, `$\geq$`
- `$\frac{a}{b}$`, `$\lim_{n \to \infty}$`, `$\to$`

**FORBIDDEN LaTeX commands** (causes KaTeX errors):
- `\mathbb` (use plain text like "real numbers" instead of $\mathbb{R}$)
- `\displaystyle` (not needed in Markdown)
- `\qed` (use ∎ symbol or "This completes the proof." instead)

**Why these constraints?**
- KaTeX (used in Markdown renderers) supports only a subset of LaTeX
- These commands cause parse errors in Markdown preview
- All prompts in [narrator.py](src/narratelean/narrator.py) must include these rules with the "FORBIDDEN" keyword

#### Prompt Engineering Best Practices

**Evolution of approach**:
1. Initial prompts were verbose and generated too much explanation
2. Refined to concise prompts with explicit formatting requirements
3. Added "FORBIDDEN" keyword for banned LaTeX commands
4. Emphasized "mathematical paper style" for formal output
5. Limited definition explanations to 2-3 sentences max

**Key prompt elements** (see [narrator.py:88-157](src/narratelean/narrator.py)):
- Start with task description ("Write a rigorous mathematical proof for a research paper...")
- Include "CRITICAL LaTeX rules" section with explicit examples
- Use "FORBIDDEN:" prefix for prohibited commands
- Provide structured output format guidelines
- Set temperature to 0.3 for consistency
- Keep prompts concise to reduce token usage

**Testing prompts**:
- Always test output in Markdown preview to verify KaTeX rendering
- Check for forbidden LaTeX commands in generated content
- Verify mathematical correctness of narratives
- Ensure proof structure matches paper style

## Code Style

### Python Conventions (pyproject.toml)
- **Line length**: 120 characters
- **Import style**: Force single-line imports (isort)
- **Type hints**: Use built-in types only (`list[X]`, `X | None`, etc.)
- **Linter rules**: B, C, E, F, I, N, SIM, UP, W
- **Ignored**:
  - `__init__.py` files allow F401 (unused imports), F403 (wildcard imports)
  - `cli.py` allows B008 (function calls in argument defaults - Typer pattern)

## Version Management

- Uses `bumpversion` tool with git integration
- Pre-commit hooks: runs `uv lock` and stages `uv.lock` on version bump
- Current version: 0.1.0
