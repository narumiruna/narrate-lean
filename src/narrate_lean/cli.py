from pathlib import Path

import typer
from loguru import logger

from narrate_lean.latex_generator import LaTeXGenerator
from narrate_lean.markdown_generator import MarkdownGenerator
from narrate_lean.parser import LeanParser

app = typer.Typer()


@app.command()
def main(
    input: Path = typer.Option(..., "--input", "-i", help="Path to input Lean 4 file"),
    output: Path = typer.Option(..., "--output", "-o", help="Path to output file"),
    format: str = typer.Option("markdown", "--format", "-f", help="Output format: latex or markdown"),
) -> None:
    """Convert Lean 4 proof scripts to human-readable documentation."""
    # Validate input file
    if not input.exists():
        logger.error(f"Input file does not exist: {input}")
        raise typer.Exit(1)

    if input.suffix != ".lean":
        logger.warning(f"Input file does not have .lean extension: {input}")

    # Validate format
    if format.lower() not in ["latex", "markdown"]:
        logger.error(f"Invalid format: {format}. Must be 'latex' or 'markdown'")
        raise typer.Exit(1)

    logger.info(f"Parsing Lean file: {input}")

    # Parse the Lean file
    parser = LeanParser()
    document = parser.parse_file(input)

    logger.info(f"Found {len(document.theorems)} theorems and {len(document.definitions)} definitions")

    # Create output directory if needed
    output.parent.mkdir(parents=True, exist_ok=True)

    # Generate output
    if format.lower() == "latex":
        generator = LaTeXGenerator()
        generator.generate(document, output)
        logger.info(f"Generated LaTeX document: {output}")
    else:
        generator = MarkdownGenerator()
        generator.generate(document, output)
        logger.info(f"Generated Markdown document: {output}")

    logger.success("Conversion complete!")
