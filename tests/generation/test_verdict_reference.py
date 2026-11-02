"""Verdict reference implementations stay executable and mode-isolated."""

from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest

from vero.evaluation.axioms import _parse_axioms_output
from vero.generation.benchmark import load_slots
from vero.generation.sandbox import create_sandbox

ROOT = Path(__file__).resolve().parents[2]
VERDICT = ROOT / "benchmarks" / "verdict"
MODULES = ("PolicyCommon", "PolicyChrome", "PolicyFirefox", "PolicyOpenSSL", "Hex")


@pytest.mark.parametrize("mode", ["proof", "codeproof"])
def test_verdict_reference_mode_isolation(tmp_path: Path, mode: str) -> None:
    sandbox = tmp_path / mode
    result = create_sandbox(VERDICT, sandbox, mode=mode)
    code_count = 0
    for module in MODULES:
        relative = Path("Verdict") / "Impl" / f"{module}.lean"
        source = VERDICT / relative
        rendered = sandbox / relative
        if mode == "proof":
            assert rendered.read_text() == source.read_text()
        for slot in load_slots(rendered):
            body = "\n".join(slot.body).strip()
            if slot.key == "code":
                code_count += 1
                assert (body == "sorry") == (mode == "codeproof")
            elif mode == "codeproof" and slot.key in {"code_aux", "global_aux"}:
                assert not body
    assert code_count == 20
    assert result.proof_files and all(path.is_file() for path in result.proof_files)
    assert (sandbox / "Verdict" / "Proof" / "Joint.lean").exists() == (
        mode == "codeproof"
    )
    assert not (sandbox / "PolicyTests.lean").exists()
    assert not (sandbox / "tests").exists()


@pytest.mark.slow
def test_verdict_reference_behavior_and_axioms(tmp_path: Path) -> None:
    if shutil.which("lake") is None:
        pytest.skip("Lean 4.29.1 / lake is required")

    def run(*args: str) -> str:
        proc = subprocess.run(
            ["lake", *args],
            cwd=VERDICT,
            capture_output=True,
            text=True,
            timeout=600,
            check=False,
        )
        output = proc.stdout + proc.stderr
        assert proc.returncode == 0, output
        return output

    run("build")
    run("env", "lean", str(ROOT / "tests/fixtures/verdict_reference/PolicyTests.lean"))

    # Inspect the APIs and every added helper, including their transitive dependencies.
    declarations = []
    for module in MODULES:
        for slot in load_slots(VERDICT / "Verdict" / "Impl" / f"{module}.lean"):
            if slot.key == "code":
                declarations.append(f"Verdict.{slot.def_name}")
            elif slot.key == "global_aux":
                body = "\n".join(slot.body)
                namespace = re.search(r"^namespace ([\w.]+)$", body, re.MULTILINE)
                if namespace:
                    declarations.extend(
                        f"{namespace[1]}.{name}"
                        for name in re.findall(r"^def (\w+)", body, re.MULTILINE)
                    )
    audit = tmp_path / "Axioms.lean"
    audit.write_text(
        "".join(f"import Verdict.Impl.{module}\n" for module in MODULES)
        + "".join(f"#print axioms {name}\n" for name in declarations),
        encoding="utf-8",
    )
    checks = _parse_axioms_output(run("env", "lean", str(audit)), declarations)
    assert all(check.status == "clean" for check in checks), checks
