#!/usr/bin/env python3
"""Check that the blueprint's claims match the library.

Two independent checks:

  declarations  every name cited by a statement marked \\leanok exists and is
                free of `sorry`, verified with `#print axioms` rather than by
                existence alone. Names cited only by \\notready statements are
                expected to be absent and are skipped.

  markers       no statement is marked \\leanok while the proof block that
                follows it is not, which would render as proved in the
                dependency graph without being so

Run from the project root, after `lake build`.
"""
import re, subprocess, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
TEX = ROOT / "blueprint" / "src" / "content.tex"
OK = r"\leanok"


def check_markers(tex: str) -> list[str]:
    pat = re.compile(
        r"\\begin\{(theorem|lemma|corollary|proposition)\}(.*?)\\end\{\1\}"
        r"(\s*\\begin\{proof\}(.*?)\\end\{proof\})?",
        re.S,
    )
    bad = []
    for _kind, body, proof, proof_body in pat.findall(tex):
        if OK not in body:
            continue
        label = re.search(r"\\label\{([^}]+)\}", body)
        name = label.group(1) if label else "(unlabelled)"
        if not proof:
            bad.append(f"{name}: statement marked {OK} but has no proof block")
        elif OK not in proof_body:
            bad.append(f"{name}: statement marked {OK} but its proof is not")
    return bad


def claimed_declarations(tex: str) -> list[str]:
    """Names cited by statements that claim to be formalised."""
    pat = re.compile(
        r"\\begin\{(definition|theorem|lemma|corollary|proposition)\}(.*?)\\end\{\1\}",
        re.S,
    )
    names = []
    for _kind, body in pat.findall(tex):
        if OK not in body:
            continue
        for m in re.finditer(r"\\lean\{([^}]+)\}", body):
            names += [n.strip() for n in m.group(1).split(",") if n.strip()]
    return names


def check_declarations(names: list[str]) -> list[str]:
    src = "import CGLean\n" + "".join(f"#print axioms {n}\n" for n in names)
    probe = ROOT / ".lake" / "blueprint-decls.lean"
    probe.parent.mkdir(parents=True, exist_ok=True)
    probe.write_text(src)
    out = subprocess.run(
        ["lake", "env", "lean", str(probe)], cwd=ROOT,
        capture_output=True, text=True,
    ).stdout
    probe.unlink(missing_ok=True)
    bad = []
    for line in out.splitlines():
        if "Unknown constant" in line or "unknown identifier" in line.lower():
            m = re.search(r"`([^`]+)`", line)
            bad.append(f"{m.group(1) if m else line}: no such declaration")
        elif "sorryAx" in line:
            m = re.match(r"'([^']+)'", line)
            bad.append(f"{m.group(1) if m else line}: depends on sorryAx")
    return bad


def main() -> int:
    tex = TEX.read_text()
    problems = check_markers(tex)
    names = claimed_declarations(tex)
    if not names:
        problems.append("no \\lean{} references on formalised statements; is the blueprint built?")
    else:
        problems += check_declarations(names)
    if problems:
        print("blueprint does not match the library:\n")
        for p in problems:
            print("  " + p)
        return 1
    print(f"blueprint ok: {len(names)} declarations, markers consistent")
    return 0


if __name__ == "__main__":
    sys.exit(main())
