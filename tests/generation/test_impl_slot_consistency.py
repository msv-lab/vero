"""Regressions for trusted Impl permissions and provided benchmark definitions."""

from __future__ import annotations

import shutil
from collections import Counter
from pathlib import Path

import pytest

from vero.generation.benchmark import Benchmark, load_slots
from vero.generation.extractor import expected_slots, extract
from vero.generation.render import render_sandbox
from vero.generation.sandbox import create_sandbox

REPO_ROOT = Path(__file__).resolve().parents[2]
BENCHMARKS = sorted((REPO_ROOT / "benchmarks").glob("*/manifest.json"))


@pytest.fixture()
def offline_sandbox(monkeypatch: pytest.MonkeyPatch) -> None:
    # These tests exercise rendering, not Lean dependency installation.
    monkeypatch.setattr("vero.generation.sandbox._ensure_mathlib_cache", lambda _: None)
    monkeypatch.setattr("vero.generation.sandbox._link_lake_packages", lambda *_: None)


@pytest.mark.parametrize("manifest", BENCHMARKS, ids=lambda p: p.parent.name)
@pytest.mark.parametrize("mode", ["proof", "codeproof"])
def test_shipped_impl_schedule_matches_source_markers(
    manifest: Path, mode: str
) -> None:
    bench = Benchmark(manifest.parent)
    impl_files = {m.impl_rel for m in bench.iter_modules() if m.impl_rel}
    expected = Counter(
        (s.file, s.prefix, s.key, s.def_name)
        for s in expected_slots(bench, mode)
        if s.file in impl_files
    )
    actual = Counter(
        (rel, s.prefix, s.key, s.def_name)
        for rel in impl_files
        for s in load_slots(bench.root / rel)
    )
    assert expected == actual


@pytest.mark.parametrize(
    ("benchmark", "package", "module"),
    [
        ("VerifiedBitmasks", "VerifiedBitmasks", name)
        for name in ["MachineTypes", "BitFieldsAxioms", "BitFields", "BitmaskSpec"]
    ]
    + [("verdict", "Verdict", name) for name in ["PolicyStandard", "Convert"]],
)
def test_no_api_modules_keep_existing_imports(
    benchmark: str, package: str, module: str
) -> None:
    bench = Benchmark(REPO_ROOT / "benchmarks" / benchmark)
    rel = f"{package}/Impl/{module}.lean"
    slots = [s for s in expected_slots(bench, "codeproof") if s.file == rel]
    assert [(s.key, s.def_name) for s in slots] == [("imports", None)]


def test_agent_cannot_change_no_api_header_permissions(
    tmp_path: Path, offline_sandbox: None
) -> None:
    source = REPO_ROOT / "benchmarks" / "VerifiedBitmasks"
    bench = Benchmark(source)
    sandbox = tmp_path / "sandbox"
    create_sandbox(source, sandbox, mode="codeproof")
    before = expected_slots(bench, "codeproof")
    rel = "VerifiedBitmasks/Impl/MachineTypes.lean"
    target = sandbox / rel
    text = target.read_text().replace("@start imports", "@start global_aux")
    text = text.replace("@end imports", "@end global_aux")
    target.write_text(text)

    artifact = extract(sandbox, bench, mode="codeproof")
    assert expected_slots(bench, "codeproof") == before
    [missing] = [s for s in artifact.slots if s.file == rel]
    assert missing.key == "imports" and missing.error == "missing"
    assert [(s.file, s.key) for s in artifact.extras] == [(rel, "global_aux")]


def test_api_modules_still_require_both_headers(tmp_path: Path) -> None:
    source = tmp_path / "source"
    shutil.copytree(
        REPO_ROOT / "reference" / "BankLedger",
        source,
        ignore=shutil.ignore_patterns(".lake"),
    )
    rel = "BankLedger/Impl/Account.lean"
    target = source / rel
    lines = target.read_text().splitlines(keepends=True)
    [slot] = [s for s in load_slots(target) if s.key == "global_aux"]
    del lines[slot.start_line - 1 : slot.end_line]
    target.write_text("".join(lines))
    slots = [s for s in expected_slots(Benchmark(source), "proof") if s.file == rel]
    assert {"imports", "global_aux"} <= {s.key for s in slots}


PROVIDED = [
    (
        "Unicode",
        "UnicodeV2/Impl/UnicodeEncodingForm.lean",
        ["Unicode.uefIsMinimalWellFormedCodeUnitSubsequence"],
        ["isValidScalarCodePoint"],
        ["nullScalarValue", "natToScalarValue"],
    ),
    (
        "Unicode",
        "UnicodeV2/Impl/Utf8EncodingForm.lean",
        ["Unicode.utf8IsMinimalWellFormedCodeUnitSubsequence"],
        ["utf8WellFormed1", "utf8WellFormed2", "utf8WellFormed3", "utf8WellFormed4"],
        ["nullSV"],
    ),
    (
        "Unicode",
        "UnicodeV2/Impl/Utf16EncodingForm.lean",
        ["Unicode.utf16IsMinimalWellFormedCodeUnitSubsequence"],
        [],
        [],
    ),
    (
        "sortedcontainers",
        "SortedcontainersCore/Impl/SortedList.lean",
        [
            "SortedContainers.SortedKeyList.bisect_key_left",
            "SortedContainers.SortedKeyList.bisect_key_right",
        ],
        [],
        [],
    ),
]


@pytest.mark.parametrize(
    ("benchmark", "rel", "provided", "support", "algorithm_aux"),
    PROVIDED,
    ids=[case[1] for case in PROVIDED],
)
def test_codeproof_preserves_provided_definitions_through_render(
    tmp_path: Path,
    offline_sandbox: None,
    benchmark: str,
    rel: str,
    provided: list[str],
    support: list[str],
    algorithm_aux: list[str],
) -> None:
    source = REPO_ROOT / "benchmarks" / benchmark
    bench = Benchmark(source)
    original = (source / rel).read_text()
    # All these declarations have contiguous bodies ending at a blank line.
    frozen = []
    for name in provided + support:
        start = original.index(f"def {name}")
        end = original.find("\n\n", start)
        body = original[start : end if end != -1 else None]
        assert "sorry" not in body
        frozen.append(body)
    for name in algorithm_aux:
        assert f"def {name}" in original

    sandbox, rendered = tmp_path / "sandbox", tmp_path / "rendered"
    create_sandbox(source, sandbox, mode="codeproof")
    artifact = extract(sandbox, bench, mode="codeproof")
    assert artifact.extras == []
    assert all(s.found for s in artifact.slots)
    assert artifact.file_errors == {}
    render_sandbox(source, artifact, rendered, mode="codeproof")

    for root in (sandbox, rendered):
        text = (root / rel).read_text()
        assert all(body in text for body in frozen)
        assert all(f"def {name}" not in text for name in algorithm_aux)
        slots = load_slots(root / rel)
        code = [s for s in slots if s.key == "code"]
        assert code and all(s.body == ("  sorry",) for s in code)
        for slot in slots:
            if slot.key in {"code_aux", "global_aux"}:
                assert not any(line.strip() for line in slot.body)


def test_agent_cannot_reintroduce_provided_helper_slot(
    tmp_path: Path, offline_sandbox: None
) -> None:
    source = REPO_ROOT / "benchmarks" / "Unicode"
    bench = Benchmark(source)
    sandbox, rendered = tmp_path / "sandbox", tmp_path / "rendered"
    create_sandbox(source, sandbox, mode="codeproof")
    rel = "UnicodeV2/Impl/Utf16EncodingForm.lean"
    target = sandbox / rel
    text = target.read_text()
    name = "utf16IsMinimalWellFormedCodeUnitSubsequence"
    start = text.index("  fun s =>", text.index(f"def Unicode.{name}"))
    end = text.index("\n\n", start)
    injected = (
        f"-- !benchmark @start code def={name}\n"
        "  fun _ => false\n"
        f"-- !benchmark @end code def={name}"
    )
    target.write_text(text[:start] + injected + text[end:])
    artifact = extract(sandbox, bench, mode="codeproof")
    assert [(s.file, s.key, s.def_name) for s in artifact.extras] == [
        (rel, "code", name)
    ]
    assert not any(s.def_name == name for s in artifact.slots)
    render_sandbox(source, artifact, rendered, mode="codeproof")
    restored = (rendered / rel).read_text()
    assert injected not in restored
    assert text[start:end] in restored
