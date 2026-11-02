"""Exercise rendered task material, not host filesystem access control."""

from __future__ import annotations

import re
import shutil
from pathlib import Path

import pytest

from vero.generation.benchmark import Benchmark, load_slots
from vero.generation.extractor import extract
from vero.generation.render import render_sandbox
from vero.generation.sandbox import create_sandbox

ROOT = Path(__file__).resolve().parents[2]
BENCHMARKS = sorted(p.parent for p in (ROOT / "benchmarks").glob("*/manifest.json"))


@pytest.fixture(autouse=True)
def offline(monkeypatch: pytest.MonkeyPatch) -> None:
    # Materialization is deterministic Python; do not fetch/build mathlib.
    monkeypatch.setattr("vero.generation.sandbox._ensure_mathlib_cache", lambda _: None)


def assert_material_isolated(root: Path, mode: str, packages: set[str]) -> None:
    """Inspect every project module, including modules outside the manifest."""
    assert not list(root.rglob("certificates"))
    assert not list(root.rglob("catalog.json"))
    assert not list(root.rglob("Proof_mode*"))
    for file in root.rglob("*"):
        if ".lake" not in file.relative_to(root).parts:
            assert not file.name.endswith(
                (".olean", ".olean.private", ".olean.server", ".ilean", ".ir")
            ), file
    for file in root.rglob("*.lean"):
        if ".lake" in file.relative_to(root).parts:
            continue  # dependency cache, not benchmark material
        assert file.resolve().is_relative_to(root.resolve()), file
        text = file.read_text(encoding="utf-8")
        imports = re.findall(r"^\s*import\s+([^\n]+)", text, re.MULTILINE)
        for modules in imports:
            for module in modules.split():
                assert "certificat" not in module.lower(), (file, module)
                assert "proof_mode" not in module.lower(), (file, module)
                if module.split(".")[0] in packages:
                    # Every project-local edge resolves inside this copy.
                    # All modules are scanned, so this also covers transitive
                    # imports and modules an agent could import via a new slot.
                    imported = root.joinpath(*module.split(".")).with_suffix(".lean")
                    assert imported.is_file(), (file, module)
                    assert imported.resolve().is_relative_to(root.resolve())
        for slot in load_slots(file):
            body = [line.strip() for line in slot.body if line.strip()]
            if "Proof" in file.relative_to(root).parts and slot.key == "proof":
                assert body in (["sorry"], ["-- sorry"]), (file, slot.def_name)
            if mode == "codeproof" and "Impl" in file.relative_to(root).parts:
                if slot.key == "code":
                    assert body == ["sorry"], (file, slot.def_name)
                elif slot.key in {"global_aux", "code_aux"}:
                    assert not body, (file, slot.key)


def test_inventory_is_the_full_released_suite() -> None:
    assert len(BENCHMARKS) == 43


@pytest.mark.parametrize("benchmark", BENCHMARKS, ids=lambda p: p.name)
@pytest.mark.parametrize("mode", ["proof", "codeproof"])
def test_every_released_generation_and_grading_material(
    benchmark: Path, mode: str, tmp_path: Path
) -> None:
    source = Benchmark(benchmark)
    generated = tmp_path / "generated"
    create_sandbox(benchmark, generated, mode=mode)
    packages = {package.name for package in source.packages}
    assert_material_isolated(generated, mode, packages)
    # Reference code is intentionally visible in proof mode; compare every
    # original slot so stripping did not silently replace the reference.
    if mode == "proof":
        for original in source.all_impl_files():
            copied = generated / original.relative_to(benchmark)
            before = {(s.key, s.def_name): s.body for s in load_slots(original)}
            after = {(s.key, s.def_name): s.body for s in load_slots(copied)}
            for identity, body in before.items():
                if identity[0] in {"code", "code_aux", "global_aux"}:
                    # Curation annotation lines are deliberately stripped.
                    expected = tuple(
                        x for x in body if not x.lstrip().startswith("-- !curation")
                    )
                    assert after[identity] == expected
    artifact = extract(generated, source, mode=mode)
    graded = tmp_path / "graded"
    render_sandbox(benchmark, artifact, graded, mode=mode)
    assert_material_isolated(graded, mode, packages)


@pytest.mark.parametrize("mode", ["proof", "codeproof"])
def test_certificates_and_stale_proofs_are_not_shipped(
    mode: str, tmp_path: Path
) -> None:
    bench = tmp_path / "source"
    shutil.copytree(
        ROOT / "reference" / "BankLedger",
        bench,
        ignore=shutil.ignore_patterns(".lake", ".git"),
    )
    # A sibling canonical certificate is not part of a task project.
    cert = tmp_path / "certificates" / "bankledger"
    cert.mkdir(parents=True)
    (cert / "Correct.lean").write_text("-- SECRET_CANONICAL_PROOF\n", encoding="utf-8")
    # Even an accidentally nested certificate tree is excluded.
    shutil.copytree(tmp_path / "certificates", bench / "certificates")
    stale = bench / "BankLedger" / "Proof" / "Secret.lean"
    stale.parent.mkdir(exist_ok=True)
    stale.write_text("-- SECRET_CANONICAL_PROOF\n", encoding="utf-8")
    # A manually compiled reference next to a source can reveal its body even
    # when that source is later blanked for codeproof.
    for suffix in (".olean", ".olean.private", ".olean.server", ".ilean", ".ir"):
        (bench / "BankLedger" / "Impl" / ("Account" + suffix)).write_bytes(
            b"SECRET_COMPILED_REFERENCE"
        )
    generated = tmp_path / "generated"
    create_sandbox(bench, generated, mode=mode)
    assert_material_isolated(generated, mode, {"BankLedger"})
    assert not (generated / "BankLedger" / "Proof" / "Secret.lean").exists()
    artifact = extract(generated, Benchmark(bench), mode=mode)
    graded = tmp_path / "graded"
    render_sandbox(bench, artifact, graded, mode=mode)
    assert_material_isolated(graded, mode, {"BankLedger"})
    assert not (graded / "BankLedger" / "Proof" / "Secret.lean").exists()
    for task in (generated, graded):
        assert all(
            "SECRET_CANONICAL_PROOF" not in p.read_text(encoding="utf-8")
            for p in task.rglob("*.lean")
        )
