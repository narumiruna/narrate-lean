import tempfile
from pathlib import Path

from narratelean.parser import LeanParser


def test_parser_basic() -> None:
    """Test basic parsing of Lean files."""
    parser = LeanParser()
    # Create a minimal test case
    test_content = """theorem add_zero (n : Nat) : n + 0 = n := by
  rfl"""

    # Create a temporary file
    with tempfile.TemporaryDirectory() as tmpdir:
        test_file = Path(tmpdir) / "test_basic.lean"
        test_file.write_text(test_content)

        lean_file = parser.parse_file(test_file)

        assert len(lean_file.theorems) == 1
        assert lean_file.theorems[0].name == "add_zero"
        assert "n + 0 = n" in lean_file.theorems[0].statement


def test_parser_with_definition() -> None:
    """Test parsing definitions."""
    parser = LeanParser()
    test_content = """def double (n : Nat) : Nat := n + n"""

    with tempfile.TemporaryDirectory() as tmpdir:
        test_file = Path(tmpdir) / "test_def.lean"
        test_file.write_text(test_content)

        lean_file = parser.parse_file(test_file)

        assert len(lean_file.definitions) == 1
        assert lean_file.definitions[0].name == "double"
        assert "Nat" in lean_file.definitions[0].type_signature
