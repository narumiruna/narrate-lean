from pathlib import Path

import typer
from dotenv import find_dotenv
from dotenv import load_dotenv
from loguru import logger

from narratelean.markdown import MarkdownGenerator
from narratelean.narrator import ProofNarrator
from narratelean.parser import LeanParser

app = typer.Typer(help="Convert Lean 4 proof files into human-readable Markdown documents.")


@app.command()
def narrate(  # noqa: B008
    input_file: Path = typer.Argument(..., help="Path to the Lean 4 proof file", exists=True, dir_okay=False),
    output: Path | None = typer.Option(None, "-o", "--output", help="Output Markdown file (default: stdout)"),
    no_definitions: bool = typer.Option(False, "--no-definitions", help="Skip narrating definitions"),
    no_proofs: bool = typer.Option(False, "--no-proofs", help="Skip narrating proof steps (only include statements)"),
    explain_lean: bool = typer.Option(
        False, "--explain-lean", help="Include explanations of Lean tactics and syntax in the proof"
    ),
) -> None:
    """
    Convert a Lean 4 proof file into a human-readable Markdown document.

    The tool parses the Lean file, extracts theorem structures and proof steps,
    and uses an LLM to generate natural language explanations with LaTeX notation.

    Example usage:
        narratelean narrate input.lean -o output.md
        narratelean narrate sample.lean  # Output to stdout
    """

    load_dotenv(find_dotenv(), override=True)

    try:
        logger.info(f"Parsing Lean file: {input_file}")

        # Parse the Lean file
        parser = LeanParser()
        lean_file = parser.parse_file(input_file)

        logger.info(f"Found {len(lean_file.definitions)} definition(s) and {len(lean_file.theorems)} theorem(s)")

        # Initialize narrator
        narrator = ProofNarrator()

        # Narrate definitions
        definitions_narration = {}
        if not no_definitions:
            for defn in lean_file.definitions:
                logger.info(f"Narrating definition: {defn.name}")
                definitions_narration[defn.name] = narrator.narrate_definition(defn)

        # Narrate theorems
        theorems_narration = {}
        for theorem in lean_file.theorems:
            logger.info(f"Narrating theorem: {theorem.name}")
            theorem_narration = {"statement": narrator.narrate_theorem_statement(theorem)}

            if not no_proofs:
                logger.info(f"Narrating proof steps for: {theorem.name}")
                theorem_narration["proof_steps"] = narrator.narrate_proof(theorem, explain_lean_syntax=explain_lean)

            theorems_narration[theorem.name] = theorem_narration

        # Generate Markdown
        logger.info("Generating Markdown document")
        generator = MarkdownGenerator()
        markdown_content = generator.generate(
            lean_file=lean_file,
            definitions_narration=definitions_narration,
            theorems_narration=theorems_narration,
            source_file=input_file,
        )

        # Output
        if output:
            output.write_text(markdown_content, encoding="utf-8")
            logger.success(f"Markdown document saved to: {output}")
        else:
            # Write to stdout
            print(markdown_content)

    except FileNotFoundError as e:
        logger.error(f"File not found: {e}")
        raise typer.Exit(code=1) from None
    except ValueError as e:
        logger.error(f"Configuration error: {e}")
        logger.info("Make sure LITELLM_API_KEY or OPENAI_API_KEY is set in your environment")
        raise typer.Exit(code=1) from None
    except Exception as e:
        logger.exception(f"Failed to narrate Lean file: {e}")
        raise typer.Exit(code=1) from e


@app.command()
def version() -> None:
    """Show the version of narratelean."""
    from narratelean import __version__

    print(f"narratelean version {__version__}")


if __name__ == "__main__":
    app()
