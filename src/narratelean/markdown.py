"""Markdown generator for narrated Lean proofs."""

from pathlib import Path
from typing import Any

from narratelean.parser import LeanFile


class MarkdownGenerator:
    """Generates Markdown documents from narrated Lean proofs."""

    def __init__(self) -> None:
        """Initialize the Markdown generator."""
        self.content: list[str] = []

    def generate(
        self,
        lean_file: LeanFile,
        definitions_narration: dict[str, str],
        theorems_narration: dict[str, dict[str, Any]],
        source_file: Path,
    ) -> str:
        """Generate complete Markdown document."""
        self.content = []

        # Header
        self._add_header(source_file)

        # Imports section
        if lean_file.imports:
            self._add_imports(lean_file.imports)

        # Definitions section
        if lean_file.definitions:
            self._add_definitions(lean_file.definitions, definitions_narration)

        # Theorems section
        if lean_file.theorems:
            self._add_theorems(lean_file.theorems, theorems_narration)

        return "\n".join(self.content)

    def _add_header(self, source_file: Path) -> None:
        """Add document header."""
        self.content.extend(
            [
                f"# Narrated Lean Proof: {source_file.name}",
                "",
                f"*This document is a human-readable narration of the Lean 4 proof file `{source_file.name}`.*",
                "",
                "---",
                "",
            ]
        )

    def _add_imports(self, imports: list[str]) -> None:
        """Add imports section."""
        self.content.extend(
            [
                "## Imports",
                "",
                "This proof file imports the following libraries:",
                "",
            ]
        )

        for imp in imports:
            self.content.append(f"- `{imp}`")

        self.content.extend(["", "---", ""])

    def _add_definitions(self, definitions: list[Any], narrations: dict[str, str]) -> None:
        """Add definitions section."""
        self.content.extend(
            [
                "## Definitions",
                "",
            ]
        )

        for defn in definitions:
            self.content.extend(
                [
                    f"### {defn.name}",
                    "",
                ]
            )

            # Add narration if available
            narration = narrations.get(defn.name, "")
            if narration:
                self.content.extend(
                    [
                        narration,
                        "",
                    ]
                )
            else:
                # Fallback: show Lean code if no narration
                self.content.extend(
                    [
                        "```lean",
                        defn.type_signature,
                        defn.body,
                        "```",
                        "",
                    ]
                )

        self.content.extend(["---", ""])

    def _add_theorems(self, theorems: list[Any], narrations: dict[str, dict[str, Any]]) -> None:
        """Add theorems section."""
        self.content.extend(
            [
                "## Theorems",
                "",
            ]
        )

        for theorem in theorems:
            self._add_single_theorem(theorem, narrations.get(theorem.name, {}))

    def _add_single_theorem(self, theorem: Any, narration: dict[str, Any]) -> None:
        """Add a single theorem with its proof."""
        self.content.extend(
            [
                f"### Theorem: {theorem.name}",
                "",
            ]
        )

        # Statement section
        statement_narration = narration.get("statement", "")
        if statement_narration:
            self.content.extend(
                [
                    statement_narration,
                    "",
                ]
            )
        else:
            # Fallback: show Lean code if no narration
            self.content.extend(
                [
                    "**Lean Statement:**",
                    "",
                    "```lean",
                    theorem.statement,
                    "```",
                    "",
                ]
            )

        # Proof section
        self.content.extend(
            [
                "#### Proof",
                "",
            ]
        )

        proof_steps = narration.get("proof_steps", [])
        if proof_steps and len(proof_steps) > 0:
            # If we have narrated proof, use it
            first_step = proof_steps[0]
            explanation = first_step.get("explanation", "")

            if explanation and "Proof narration failed" not in explanation:
                # Use the LLM-generated narrative directly
                self.content.extend(
                    [
                        explanation,
                        "",
                    ]
                )
            else:
                # Fallback to showing original Lean proof
                self.content.extend(
                    [
                        "*Original Lean Proof:*",
                        "",
                        "```lean",
                    ]
                )
                self.content.extend(theorem.proof_steps)
                self.content.extend(
                    [
                        "```",
                        "",
                    ]
                )
        else:
            # Fallback: show original proof steps
            self.content.extend(
                [
                    "*Original Lean Proof:*",
                    "",
                    "```lean",
                ]
            )
            self.content.extend(theorem.proof_steps)
            self.content.extend(
                [
                    "```",
                    "",
                ]
            )

        self.content.extend(["---", ""])

    def save_to_file(self, output_path: Path) -> None:
        """Save generated Markdown to file."""
        content_str = "\n".join(self.content)
        output_path.write_text(content_str, encoding="utf-8")
