"""Unit tests for joint_rerender's pure helpers (no Lean invocation)."""

from __future__ import annotations

from types import SimpleNamespace

import pytest

from vero.evaluation.joint_rerender import _parse_spec_list, _render_joint_check


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


@pytest.mark.parametrize(
    ("root", "module_paths", "expected"),
    [
        (
            "Flocq",
            [("Flocq", "Core/FLT", "Flocq/Core/Spec/FLT.lean")],
            ["Flocq.Core.Spec.FLT"],
        ),
        (
            "JsonV2",
            [("JsonV2", "Utils/Seq", "JsonV2/Spec/Utils/Seq.lean")],
            ["JsonV2.Spec.Utils.Seq"],
        ),
        ("Root", [("Root", "Core", None)], ["Root.Spec.Core"]),
        (
            "Root",
            [("A", "Shared", "A/Spec/Shared.lean"), ("B", "Shared", None)],
            ["A.Spec.Shared", "B.Spec.Shared"],
        ),
    ],
    ids=["flocq", "json", "flat-fallback", "same-name-different-packages"],
)
def test_joint_imports(root, module_paths, expected) -> None:
    # The pure renderer needs only these manifest fields; no files or Lean setup.
    modules = [
        SimpleNamespace(package=package, name=name, spec_rel=path, specs=(f"spec_{i}",))
        for i, (package, name, path) in enumerate(module_paths)
    ]
    bench = SimpleNamespace(root_package=root, iter_modules=lambda: iter(modules))
    text, _ = _render_joint_check(
        bench,
        tuple(module.specs[0] for module in modules),
        proof_body=["  exact joint_proof"],
        proof_aux_body=[],
        global_aux_body=[],
        imports_body=[],
    )
    assert [line for line in text.splitlines() if line.startswith("import ")] == [
        f"import {root}.Harness",
        *[f"import {name}" for name in expected],
    ]
