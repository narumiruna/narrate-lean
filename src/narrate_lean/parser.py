"""Parser for Lean 4 proof files."""

import re
from dataclasses import dataclass
from pathlib import Path


@dataclass
class LeanTheorem:
    """Represents a theorem in Lean 4."""

    name: str
    statement: str
    proof: str
    line_number: int


@dataclass
class LeanDefinition:
    """Represents a definition in Lean 4."""

    name: str
    type_signature: str
    body: str
    line_number: int


@dataclass
class LeanDocument:
    """Represents a parsed Lean 4 document."""

    theorems: list[LeanTheorem]
    definitions: list[LeanDefinition]
    raw_content: str


class LeanParser:
    """Parser for Lean 4 proof files."""

    def __init__(self) -> None:
        """Initialize the parser."""
        pass

    def parse_file(self, file_path: Path) -> LeanDocument:
        """Parse a Lean 4 file and extract theorems and definitions.

        Args:
            file_path: Path to the Lean 4 file

        Returns:
            LeanDocument containing parsed theorems and definitions
        """
        content = file_path.read_text()
        theorems = self._extract_theorems(content)
        definitions = self._extract_definitions(content)

        return LeanDocument(theorems=theorems, definitions=definitions, raw_content=content)

    def _extract_theorems(self, content: str) -> list[LeanTheorem]:
        """Extract theorems from Lean content.

        Args:
            content: The Lean file content

        Returns:
            List of LeanTheorem objects
        """
        theorems = []
        lines = content.split("\n")

        # Simple pattern matching for theorem declarations
        for i, line in enumerate(lines):
            if line.strip().startswith("theorem"):
                # Extract theorem name
                theorem_match = re.match(r"theorem\s+(\w+)", line)
                if theorem_match:
                    name = theorem_match.group(1)

                    # Collect the full theorem statement and proof
                    statement_lines = [line]
                    j = i + 1
                    brace_count = line.count("{") - line.count("}")

                    while j < len(lines):
                        statement_lines.append(lines[j])
                        brace_count += lines[j].count("{") - lines[j].count("}")

                        # Check if we've reached the end of the theorem
                        if brace_count == 0 and (":=" in lines[j] or "by" in lines[j]):
                            # Continue until we find the proof end
                            k = j + 1
                            while k < len(lines) and not lines[k].strip().startswith(
                                ("theorem", "def", "end", "example")
                            ):
                                statement_lines.append(lines[k])
                                k += 1
                            break
                        j += 1

                    full_text = "\n".join(statement_lines)

                    # Split statement and proof
                    if ":=" in full_text:
                        parts = full_text.split(":=", 1)
                        statement = parts[0].replace("theorem " + name, "").strip()
                        proof = parts[1].strip() if len(parts) > 1 else ""
                    else:
                        statement = full_text.replace("theorem " + name, "").strip()
                        proof = ""

                    theorems.append(LeanTheorem(name=name, statement=statement, proof=proof, line_number=i + 1))

        return theorems

    def _extract_definitions(self, content: str) -> list[LeanDefinition]:
        """Extract definitions from Lean content.

        Args:
            content: The Lean file content

        Returns:
            List of LeanDefinition objects
        """
        definitions = []
        lines = content.split("\n")

        for i, line in enumerate(lines):
            if line.strip().startswith("def"):
                # Extract definition name
                def_match = re.match(r"def\s+(\w+)", line)
                if def_match:
                    name = def_match.group(1)

                    # Collect the full definition
                    def_lines = [line]
                    j = i + 1
                    brace_count = line.count("{") - line.count("}")

                    while j < len(lines):
                        def_lines.append(lines[j])
                        brace_count += lines[j].count("{") - lines[j].count("}")

                        if brace_count == 0 and ":=" in lines[j]:
                            k = j + 1
                            while k < len(lines) and not lines[k].strip().startswith(
                                ("theorem", "def", "end", "example")
                            ):
                                def_lines.append(lines[k])
                                k += 1
                            break
                        j += 1

                    full_text = "\n".join(def_lines)

                    # Split type signature and body
                    if ":=" in full_text:
                        parts = full_text.split(":=", 1)
                        type_sig = parts[0].replace("def " + name, "").strip()
                        body = parts[1].strip() if len(parts) > 1 else ""
                    else:
                        type_sig = full_text.replace("def " + name, "").strip()
                        body = ""

                    definitions.append(LeanDefinition(name=name, type_signature=type_sig, body=body, line_number=i + 1))

        return definitions
