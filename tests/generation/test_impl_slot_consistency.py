"""Fixed definitions survive codeproof generation and reconstruction."""

from pathlib import Path

import pytest

from vero.generation.benchmark import Benchmark, load_slots
from vero.generation.extractor import extract
from vero.generation.render import render_sandbox
from vero.generation.sandbox import create_sandbox

BENCHMARKS = Path(__file__).resolve().parents[2] / "benchmarks"


@pytest.mark.parametrize(
    ("benchmark", "rel", "names", "cleared"),
    [
        (
            "Unicode",
            "UnicodeV2/Impl/Utf8EncodingForm.lean",
            ["Unicode.utf8IsMinimalWellFormedCodeUnitSubsequence"]
            + [f"utf8WellFormed{i}" for i in range(1, 5)],
            ["nullSV"],
        ),
        (
            "sortedcontainers",
            "SortedcontainersCore/Impl/SortedList.lean",
            [
                "SortedContainers.SortedKeyList.bisect_key_left",
                "SortedContainers.SortedKeyList.bisect_key_right",
            ],
            [],
        ),
    ],
    ids=["unicode", "sortedcontainers"],
)
def test_codeproof_preserves_fixed_definitions(
    tmp_path, monkeypatch, benchmark, rel, names, cleared
) -> None:
    # Exercise the real pipeline without downloading or linking Lean dependencies.
    monkeypatch.setattr("vero.generation.sandbox._ensure_mathlib_cache", lambda _: None)
    monkeypatch.setattr("vero.generation.sandbox._link_lake_packages", lambda *_: None)
    source = BENCHMARKS / benchmark
    original = (source / rel).read_text()
    bodies = []
    for name in names:
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
        assert all(f"def {name}" not in text for name in cleared)
