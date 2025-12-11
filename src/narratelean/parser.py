"""Parser for extracting theorem structures from Lean 4 proof files."""

import re
from dataclasses import dataclass
from pathlib import Path


@dataclass
class LeanDefinition:
    """Represents a Lean definition."""

    name: str
    type_signature: str
    body: str
    start_line: int
    end_line: int


@dataclass
class LeanTheorem:
    """Represents a Lean theorem with its proof."""

    name: str
    statement: str
    hypotheses: list[str]
    proof_steps: list[str]
    start_line: int
    end_line: int


@dataclass
class LeanFile:
    """Represents a parsed Lean file."""

    imports: list[str]
    definitions: list[LeanDefinition]
    theorems: list[LeanTheorem]


class LeanParser:
    """Parser for Lean 4 proof files."""

    def parse_file(self, file_path: Path) -> LeanFile:
        """Parse a Lean file and extract its structure."""
        if not file_path.exists():
            raise FileNotFoundError(f"Lean file not found: {file_path}")

        content = file_path.read_text(encoding="utf-8")
        lines = content.split("\n")

        imports = self._extract_imports(lines)
        definitions = self._extract_definitions(lines)
        theorems = self._extract_theorems(lines)

        return LeanFile(imports=imports, definitions=definitions, theorems=theorems)

    def _extract_imports(self, lines: list[str]) -> list[str]:
        """Extract import statements."""
        imports = []
        for line in lines:
            if line.strip().startswith("import "):
                import_name = line.strip()[7:].strip()
                imports.append(import_name)
        return imports

    def _extract_definitions(self, lines: list[str]) -> list[LeanDefinition]:
        """Extract definitions from the Lean file."""
        definitions = []
        i = 0
        while i < len(lines):
            line = lines[i].strip()
            if line.startswith("def "):
                def_name, type_sig, body, end_line = self._parse_definition(lines, i)
                definitions.append(
                    LeanDefinition(
                        name=def_name,
                        type_signature=type_sig,
                        body=body,
                        start_line=i + 1,
                        end_line=end_line + 1,
                    )
                )
                i = end_line + 1
            else:
                i += 1
        return definitions

    def _parse_definition(self, lines: list[str], start: int) -> tuple[str, str, str, int]:
        """Parse a single definition."""
        # Extract definition name
        first_line = lines[start].strip()
        match = re.match(r"def\s+(\w+)", first_line)
        if not match:
            raise ValueError(f"Invalid definition at line {start + 1}")

        def_name = match.group(1)

        # Collect full definition
        def_lines = []
        i = start
        in_definition = False

        while i < len(lines):
            line = lines[i]
            stripped = line.strip()

            if i == start:
                def_lines.append(line)
                in_definition = True
                i += 1
                continue

            if in_definition:
                if stripped and not stripped.startswith("--"):
                    def_lines.append(line)

                # Check if definition ends (next definition, theorem, or empty line after :=)
                if stripped.startswith(("def ", "theorem ", "lemma ", "example ")) or (
                    not stripped and ":=" in "".join(def_lines)
                ):
                    break

                i += 1
            else:
                break

        # Split type signature and body
        full_def = "\n".join(def_lines)
        if ":=" in full_def:
            parts = full_def.split(":=", 1)
            type_sig = parts[0].strip()
            body = parts[1].strip()
        else:
            type_sig = full_def.strip()
            body = ""

        return def_name, type_sig, body, i - 1

    def _extract_theorems(self, lines: list[str]) -> list[LeanTheorem]:
        """Extract theorems from the Lean file."""
        theorems = []
        i = 0
        while i < len(lines):
            line = lines[i].strip()
            if line.startswith(("theorem ", "lemma ")):
                theorem = self._parse_theorem(lines, i)
                theorems.append(theorem)
                i = theorem.end_line
            else:
                i += 1
        return theorems

    def _parse_theorem(self, lines: list[str], start: int) -> LeanTheorem:  # noqa: C901
        """Parse a single theorem with its proof."""
        # Extract theorem name
        first_line = lines[start].strip()
        match = re.match(r"(?:theorem|lemma)\s+(\w+)", first_line)
        if not match:
            raise ValueError(f"Invalid theorem at line {start + 1}")

        theorem_name = match.group(1)

        # Collect statement and proof
        statement_lines = []
        proof_lines = []
        hypotheses = []
        in_statement = True
        i = start

        while i < len(lines):
            line = lines[i]
            stripped = line.strip()

            # Check for end of theorem
            if i > start and stripped.startswith(("theorem ", "lemma ", "def ", "example ")):
                break

            if in_statement:
                statement_lines.append(line)
                # Extract hypotheses (parameters with names starting with 'h')
                if ":" in stripped and not stripped.startswith("--"):
                    # Look for hypothesis patterns like (ha : ...)
                    hyp_matches = re.findall(r"\(([h]\w*)\s*:", stripped)
                    hypotheses.extend(hyp_matches)

                # Check if we've reached the proof
                if ":= by" in stripped or stripped.endswith(":= by"):
                    in_statement = False
            else:
                if stripped:  # Skip empty lines
                    proof_lines.append(line)

                # Check if proof might be done (empty line after proof content)
                if not stripped and proof_lines and i + 1 < len(lines):
                    # Peek ahead to see if we're really done
                    next_stripped = lines[i + 1].strip()
                    if (
                        next_stripped.startswith(("theorem ", "lemma ", "def ", "example ", "import "))
                        or not next_stripped
                    ):
                        break

            i += 1

        statement = "\n".join(statement_lines).strip()
        proof_steps = self._extract_proof_steps(proof_lines)

        return LeanTheorem(
            name=theorem_name,
            statement=statement,
            hypotheses=hypotheses,
            proof_steps=proof_steps,
            start_line=start + 1,
            end_line=i,
        )

    def _extract_proof_steps(self, proof_lines: list[str]) -> list[str]:
        """Extract individual proof steps from proof lines."""
        steps = []
        for line in proof_lines:
            stripped = line.strip()
            if stripped and not stripped.startswith("--"):
                steps.append(stripped)
        return steps
