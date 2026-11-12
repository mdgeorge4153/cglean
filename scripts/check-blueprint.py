#!/usr/bin/env python3
"""Check that the blueprint's claims match the library.

leanblueprint uses \\leanok in two places, with different meanings:

  in a statement  the statement is formalised: the declarations it cites with
                  \\lean{...} exist. Their proofs may still be `sorry`.
  in a proof      the proof is complete: those declarations are free of
                  `sorry`, verified with `#print axioms`.

So this checks:

  stated   every name cited by a \\leanok statement exists
  proved   every name cited by a statement whose proof is \\leanok, or by a
           \\leanok definition (which has no proof), does not depend on sorryAx
  markers  no proof is \\leanok while its statement is not

Names cited only by statements without \\leanok are not checked. Run from the
project root, after `lake build`.
"""
import re, subprocess, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
TEX = ROOT / "blueprint" / "src" / "content.tex"
OK = r"\leanok"

ENV = re.compile(
    r"\\begin\{(definition|theorem|lemma|corollary|proposition)\}(.*?)\\end\{\1\}"
    r"(\s*\\begin\{proof\}(.*?)\\end\{proof\})?",
    re.S,
)


def label(body: str) -> str:
    m = re.search(r"\\label\{([^}]+)\}", body)
    return m.group(1) if m else "(unlabelled)"


def cited(body: str) -> list[str]:
    names = []
    for m in re.finditer(r"\\lean\{([^}]+)\}", body):
        names += [n.strip() for n in m.group(1).split(",") if n.strip()]
    return names


def scan(tex: str) -> tuple[list[str], set[str], list[str]]:
    """Names cited by formalised statements, the subset whose proofs are
    complete, and any marker inconsistencies."""
    tex = re.sub(r"(?<!\\)%.*", "", tex)  # drop comments
    stated, proved, bad = [], set(), []
    for kind, body, proof, proof_body in ENV.findall(tex):
        statement_ok = OK in body
        # A definition has no proof: its \leanok means it is complete.
        proof_ok = kind == "definition" or (bool(proof) and OK in proof_body)
        if proof and OK in proof_body and not statement_ok:
            bad.append(f"{label(body)}: proof marked {OK} but its statement is not")
        if statement_ok:
            names = cited(body)
            stated += names
            if proof_ok:
                proved.update(names)
    return list(dict.fromkeys(stated)), proved, bad


def check_declarations(stated: list[str], proved: set[str]) -> list[str]:
    src = "import CGLean\n" + "".join(f"#print axioms {n}\n" for n in stated)
    probe = ROOT / ".lake" / "blueprint-decls.lean"
    probe.parent.mkdir(parents=True, exist_ok=True)
    probe.write_text(src)
    result = subprocess.run(
        ["lake", "env", "lean", str(probe)], cwd=ROOT,
        capture_output=True, text=True,
    )
    out = result.stdout
    probe.unlink(missing_ok=True)
    # Parse whole messages, not lines: Lean wraps long axiom lists.
    axioms = {
        m.group(1): m.group(2) or ""
        for m in re.finditer(
            r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",
            out, re.S,
        )
    }
    bad = []
    for name in stated:
        if name not in axioms:
            bad.append(f"{name}: no such declaration")
        elif name in proved and "sorryAx" in axioms[name]:
            bad.append(f"{name}: marked complete but depends on sorryAx")
    if bad and len(bad) == len(stated):
        # Nothing resolved: more likely a broken build than a broken blueprint.
        bad.append("lean output:\n" + out + result.stderr)
    return bad


def main() -> int:
    stated, proved, problems = scan(TEX.read_text())
    if not stated:
        problems.append(f"no \\lean{{}} references on {OK} statements")
    else:
        problems += check_declarations(stated, proved)
    if problems:
        print("blueprint does not match the library:\n")
        for p in problems:
            print("  " + p)
        return 1
    print(f"blueprint ok: {len(stated)} declarations formalised, {len(proved)} of them sorry-free")
    return 0


if __name__ == "__main__":
    sys.exit(main())
