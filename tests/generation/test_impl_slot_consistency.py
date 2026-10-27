"""Focused regressions for Impl headers and provided definitions."""

from pathlib import Path

from vero.generation.benchmark import Benchmark, load_slots
from vero.generation.extractor import expected_slots, extract
from vero.generation.render import render_sandbox
from vero.generation.sandbox import create_sandbox

BENCHMARKS = Path(__file__).resolve().parents[2] / "benchmarks"


def test_no_api_headers_match_trusted_source() -> None:
    for name, rel, headers in [
        ("Unicode", "UnicodeV2/Impl/Unicode.lean", []),
        ("VerifiedBitmasks", "VerifiedBitmasks/Impl/MachineTypes.lean", ["imports"]),
    ]:
        bench = Benchmark(BENCHMARKS / name)
        slots = [s for s in expected_slots(bench, "codeproof") if s.file == rel]
        assert [(s.key, s.def_name) for s in slots] == [(h, None) for h in headers]


def test_codeproof_preserves_provided_utf8_predicates(tmp_path, monkeypatch) -> None:
    # Exercise the real pipeline without downloading or linking Lean dependencies.
    monkeypatch.setattr("vero.generation.sandbox._ensure_mathlib_cache", lambda _: None)
    monkeypatch.setattr("vero.generation.sandbox._link_lake_packages", lambda *_: None)
    source = BENCHMARKS / "Unicode"
    rel = "UnicodeV2/Impl/Utf8EncodingForm.lean"
    original = (source / rel).read_text()
    bodies = []
    for name in [
        "Unicode.utf8IsMinimalWellFormedCodeUnitSubsequence",
        "utf8WellFormed1",
        "utf8WellFormed2",
        "utf8WellFormed3",
        "utf8WellFormed4",
    ]:
        start = original.index(f"def {name}")
        bodies.append(original[start : original.index("\n\n", start)])
    sandbox, rebuilt = tmp_path / "sandbox", tmp_path / "rebuilt"
    create_sandbox(source, sandbox, mode="codeproof")
    artifact = extract(sandbox, Benchmark(source), mode="codeproof")
    assert not artifact.extras
    render_sandbox(source, artifact, rebuilt, mode="codeproof")
    for root in (sandbox, rebuilt):
        code = [slot for slot in load_slots(root / rel) if slot.key == "code"]
        assert code and all(slot.body == ("  sorry",) for slot in code)
        text = (root / rel).read_text()
        assert all(body in text for body in bodies)
        assert "def nullSV" not in text  # Algorithm helpers must still be cleared.
