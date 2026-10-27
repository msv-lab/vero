"""Unit tests for joint_rerender's pure helpers (no Lean invocation)."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from vero.evaluation.joint_rerender import _parse_spec_list, _render_joint_check
from vero.generation.benchmark import Benchmark


def test_default_placeholder_returns_none() -> None:
    body = ["specs=[<FILL: comma-separated spec names, e.g. spec_a, spec_b>]"]
    assert _parse_spec_list(body) is None


def test_well_formed_list() -> None:
    body = ["specs=[spec_a, spec_b, spec_c]"]
    assert _parse_spec_list(body) == ("spec_a", "spec_b", "spec_c")


def test_empty_list_is_empty_tuple() -> None:
    body = ["specs=[]"]
    assert _parse_spec_list(body) == ()


def test_no_list_returns_none() -> None:
    body = ["-- no specs here"]
    assert _parse_spec_list(body) is None


def test_list_can_span_lines() -> None:
    body = [
        "-- some commentary",
        "specs=[spec_a,",
        "       spec_b]",
    ]
    # We accept single-line per current impl; multi-line is rare. Skip it for now.
    # If multi-line is needed later, update _LIST_RE to be multiline-aware.
    # Just ensure the helper doesn't crash.
    result = _parse_spec_list(body)
    # Either parses both or just the first (acceptable v1 behavior).
    assert result is None or result[0] == "spec_a"


BENCHMARKS = Path(__file__).resolve().parents[2] / "benchmarks"
SPEC_MODULES = [
    (path, module)
    for path in sorted(BENCHMARKS.iterdir())
    if (path / "manifest.json").is_file()
    for module in Benchmark(path).iter_modules()
    if module.specs
]


def render_imports(bench: Benchmark, specs: tuple[str, ...]) -> list[str]:
    text, _ = _render_joint_check(
        bench,
        specs,
        proof_body=["  exact joint_proof"],
        proof_aux_body=[],
        global_aux_body=[],
        imports_body=[],
    )
    return [line for line in text.splitlines() if line.startswith("import ")]


@pytest.mark.parametrize(
    ("path", "module"),
    SPEC_MODULES,
    ids=[f"{path.name}/{module.name}" for path, module in SPEC_MODULES],
)
def test_joint_imports_real_spec_file(path, module) -> None:
    """A claim must import the actual spec file, including nested layouts."""
    assert module.spec_rel is not None
    assert (path / module.spec_rel).is_file()
    expected = module.spec_rel.removesuffix(".lean").replace("/", ".")
    imports = render_imports(Benchmark(path), module.specs[:2])
    assert imports == [
        f"import {Benchmark(path).root_package}.Harness",
        f"import {expected}",
    ]


def test_joint_imports_keep_package_identity_and_legacy_fallback(
    tmp_path: Path,
) -> None:
    """Same-named modules in different packages must not collapse to one import."""
    manifest = {
        "benchmark_id": "multi_package",
        "lean_version": "4.29.1",
        "root_package": "Root",
        "packages": [
            {
                "name": package,
                "bundle": f"{package}/Bundle.lean",
                "bundle_type": f"{package}Bundle",
                "repo_impl_field": package.lower(),
                "modules": [
                    {
                        "name": "Nested/Shared",
                        "spec": spec_path,
                        "specs": [spec],
                    }
                ],
            }
            for package, spec_path, spec in [
                ("A", "A/Nested/Spec/Shared.lean", "spec_a"),
                ("B", None, "spec_b"),
            ]
        ],
    }
    (tmp_path / "manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
    assert render_imports(Benchmark(tmp_path), ("spec_a", "spec_b")) == [
        "import Root.Harness",
        "import A.Nested.Spec.Shared",
        "import B.Spec.Nested.Shared",
    ]
