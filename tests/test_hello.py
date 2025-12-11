from pathlib import Path

from narrate_lean.latex_generator import LaTeXGenerator
from narrate_lean.markdown_generator import MarkdownGenerator
from narrate_lean.parser import LeanParser


def test_parser_basic() -> None:
    """Test basic parsing of Lean files."""
    parser = LeanParser()
    # Create a minimal test case
    test_content = """theorem add_zero (n : Nat) : n + 0 = n := by
  rfl"""

    # Create a temporary file
    test_file = Path("/tmp/test_basic.lean")
    test_file.write_text(test_content)

    doc = parser.parse_file(test_file)

    assert len(doc.theorems) == 1
    assert doc.theorems[0].name == "add_zero"
    assert "n + 0 = n" in doc.theorems[0].statement


def test_markdown_generator() -> None:
    """Test Markdown generation."""
    parser = LeanParser()
    test_content = """theorem test_theorem (n : Nat) : n = n := by
  rfl"""

    test_file = Path("/tmp/test_markdown.lean")
    test_file.write_text(test_content)

    doc = parser.parse_file(test_file)
    generator = MarkdownGenerator()

    output_file = Path("/tmp/test_output.md")
    generator.generate(doc, output_file)

    assert output_file.exists()
    content = output_file.read_text()
    assert "# Lean 4 Proof Documentation" in content
    assert "test_theorem" in content


def test_latex_generator() -> None:
    """Test LaTeX generation."""
    parser = LeanParser()
    test_content = """def double (n : Nat) : Nat := n + n"""

    test_file = Path("/tmp/test_latex.lean")
    test_file.write_text(test_content)

    doc = parser.parse_file(test_file)
    generator = LaTeXGenerator()

    output_file = Path("/tmp/test_output.tex")
    generator.generate(doc, output_file)

    assert output_file.exists()
    content = output_file.read_text()
    assert r"\documentclass{article}" in content
    assert "double" in content
