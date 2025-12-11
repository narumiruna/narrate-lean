"""Narration engine for converting Lean proofs to natural language."""

import os

from loguru import logger
from openai import OpenAI

from narratelean.parser import LeanDefinition
from narratelean.parser import LeanTheorem


class ProofNarrator:
    """Generates natural language narratives for Lean proofs using LLM."""

    def __init__(self) -> None:
        """Initialize the narrator with LLM client."""
        # Use LiteLLM or OpenAI API
        api_key = os.getenv("LITELLM_API_KEY") or os.getenv("OPENAI_API_KEY")
        base_url = os.getenv("LITELLM_BASE_URL")

        if not api_key:
            raise ValueError("No API key found. Set LITELLM_API_KEY or OPENAI_API_KEY environment variable.")

        self.client = OpenAI(api_key=api_key, base_url=base_url)
        # Default model - users should set LLM_MODEL env var for their specific setup
        self.model = os.getenv("LLM_MODEL", "gpt-4.1")

    def narrate_definition(self, definition: LeanDefinition) -> str:
        """Generate natural language explanation for a definition."""
        prompt = f"""Convert this Lean 4 definition into a clear mathematical explanation.

Definition:
{definition.type_signature}
{definition.body}

CRITICAL LaTeX formatting rules for Markdown (KaTeX):
- For inline math: $...$ (e.g., $\\epsilon > 0$, $a_n$, $n \\geq N$)
- For display equations: $$...$$ on separate lines
- Use basic LaTeX only: $\\forall$, $\\exists$, $\\epsilon$, $\\leq$, $\\geq$, etc.
- Avoid: \\mathbb, \\displaystyle, \\qed (use ∎ symbol instead)

Provide a concise explanation (2-3 sentences max) with all math in proper $...$ or $$...$$ format."""

        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                temperature=0.3,
            )
            return response.choices[0].message.content or ""
        except Exception as e:
            logger.error(f"Failed to narrate definition '{definition.name}': {e}")
            return f"*Definition {definition.name} could not be narrated.*"

    def narrate_theorem_statement(self, theorem: LeanTheorem) -> str:
        """Generate natural language explanation for a theorem statement."""
        prompt = f"""Convert this Lean 4 theorem into a formal mathematical statement.

Theorem:
{theorem.statement}

CRITICAL LaTeX formatting rules for Markdown (KaTeX):
- For inline math: $...$ (e.g., $a_n \\leq b_n$, $\\lim_{{n \\to \\infty}} a_n = L$)
- For display equations: $$...$$ on separate lines
- Use basic LaTeX: $\\forall$, $\\exists$, $\\epsilon$, $\\leq$, $\\lim$, etc.
- Avoid: \\mathbb, \\displaystyle, \\qed

Format:
**Theorem (Name):** [Brief statement]

**Given:** [List hypotheses with $...$]

**Then:** [Conclusion with $$...$$]

Keep it concise and mathematical."""

        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                temperature=0.3,
            )
            return response.choices[0].message.content or ""
        except Exception as e:
            logger.error(f"Failed to narrate theorem statement '{theorem.name}': {e}")
            return f"*Theorem statement for {theorem.name} could not be narrated.*"

    def narrate_proof(self, theorem: LeanTheorem, explain_lean_syntax: bool = False) -> list[dict[str, str]]:
        """Generate step-by-step natural language explanation for a proof."""
        # Group proof steps into logical chunks
        proof_text = "\n".join(theorem.proof_steps)

        if explain_lean_syntax:
            # Include Lean tactics explanation
            prompt = f"""You are writing a mathematical proof with explanations of Lean 4 tactics. Convert this \
Lean 4 proof into a detailed explanation that teaches both the mathematics and the Lean tactics.

Theorem: {theorem.name}
Statement:
{theorem.statement}

Lean Proof Steps:
{proof_text}

CRITICAL LaTeX formatting rules for Markdown:
- For ALL inline math, use $...$ (e.g., $\\epsilon > 0$, $|a_n - L| < \\epsilon$, $n \\geq N$)
- For display equations, use $$...$$ on separate lines
- Always escape backslashes in LaTeX (e.g., $\\forall$, $\\exists$, $\\leq$, $\\frac{{\\epsilon}}{{2}}$)
- Use double braces for subscripts/superscripts (e.g., $a_{{n}}$, $\\lim_{{n \\to \\infty}}$)
- DO NOT use $\\qed$ - use text like "This completes the proof." or the symbol ∎ instead

Write a detailed proof following these guidelines:
1. Structure into logical steps with headers (e.g., "**Step 1:**")
2. For each step, explain:
   - The Lean tactic used (in a code block)
   - What the tactic does
   - The mathematical reasoning
3. Use proper mathematical notation with $...$ for inline and $$...$$ for display equations
4. Include both the Lean syntax explanation and the mathematical content
5. End with a conclusion statement (use "This completes the proof." or ∎, NOT $\\qed$)

Format each step as:
**Step N: [Description]**

Lean tactic:
```lean
[tactic code]
```

[Explanation of what the tactic does and the mathematical reasoning]"""
        else:
            # Pure mathematical proof without Lean explanations
            prompt = f"""Write a rigorous mathematical proof for a research paper. Convert this Lean 4 proof into \
pure mathematics.

Theorem: {theorem.name}
Statement:
{theorem.statement}

Lean Proof (for reference):
{proof_text}

CRITICAL LaTeX rules for Markdown (KaTeX):
- Inline math: $...$ (e.g., $\\epsilon > 0$, $|a_n - L| < \\epsilon$, $n \\geq N$)
- Display math: $$...$$ on separate lines
- Basic LaTeX only: $\\forall$, $\\exists$, $\\leq$, $\\geq$, $\\frac{{a}}{{b}}$, $\\lim_{{n \\to \\infty}}$
- FORBIDDEN: \\mathbb, \\displaystyle, \\qed (use ∎ or "This completes the proof." instead)
- All subscripts in double braces: $a_{{n}}$, $N_{{1}}$

Guidelines:
1. Mathematical paper style - formal and concise
2. Do NOT mention Lean tactics
3. Use step headers: **Step 1:**, **Step 2:**, etc.
4. ALL math in $...$ or $$...$$
5. End with ∎ or "This completes the proof."

Write ONLY the proof as it would appear in a published mathematical paper."""

        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                temperature=0.3,
            )
            content = response.choices[0].message.content or ""

            # Return the full narrative as a single item for Markdown rendering
            return [{"step": "Proof", "lean_code": "", "explanation": content}]
        except Exception as e:
            logger.error(f"Failed to narrate proof for '{theorem.name}': {e}")
            return [{"step": "Error", "explanation": f"*Proof narration failed: {e}*"}]

    def _parse_proof_steps(self, narration: str, original_steps: list[str]) -> list[dict[str, str]]:  # noqa: C901
        """Parse LLM response into structured proof steps."""
        # Simple parsing: split by step markers
        steps = []
        lines = narration.split("\n")

        current_step = {"step": "", "lean_code": "", "explanation": ""}
        in_explanation = False

        for line in lines:
            line = line.strip()
            if not line:
                continue

            # Detect step headers
            if line.startswith("**Step") or line.startswith("Step"):
                if current_step["step"] or current_step["explanation"]:
                    steps.append(current_step.copy())
                    current_step = {"step": "", "lean_code": "", "explanation": ""}

                current_step["step"] = line.strip("*:")
                in_explanation = False
            elif "**Lean code**" in line or "Lean code:" in line:
                in_explanation = False
                # Extract code from this line if present
                if "`" in line:
                    code_part = line.split("`", 2)
                    if len(code_part) >= 2:
                        current_step["lean_code"] = code_part[1]
            elif "**Explanation**" in line or "Explanation:" in line:
                in_explanation = True
                # Extract explanation from this line if present
                expl = line.split(":", 1)
                if len(expl) > 1:
                    current_step["explanation"] = expl[1].strip()
            elif in_explanation:
                if current_step["explanation"]:
                    current_step["explanation"] += " " + line
                else:
                    current_step["explanation"] = line
            elif current_step["step"] and not current_step["explanation"]:
                # Continuation of step description
                if current_step["lean_code"]:
                    current_step["explanation"] = line
                    in_explanation = True
                else:
                    current_step["lean_code"] = line.strip("`")

        # Add last step
        if current_step["step"] or current_step["explanation"]:
            steps.append(current_step)

        # If parsing failed, create a simple structure
        if not steps:
            steps = [{"step": "Proof Explanation", "lean_code": "", "explanation": narration}]

        return steps
