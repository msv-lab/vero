from __future__ import annotations

import copy
import json
import shutil
import tempfile
from pathlib import Path

import pytest

from vero.certification.check import (
    CatalogError,
    check_task,
    main,
    new_catalog,
    validate_catalog,
)


@pytest.fixture(autouse=True)
def runtime_temp_directory(tmp_path, monkeypatch):
    monkeypatch.setattr(tempfile, "tempdir", str(tmp_path))


@pytest.fixture
def repository(tmp_path):
    task = tmp_path / "benchmarks/Tiny"
    task.mkdir(parents=True)
    (task / "Tiny.lean").write_text(
        "structure RepoImpl where\n  value : Nat\n"
        "def canonical : RepoImpl := ⟨0⟩\n"
        "def spec_good (impl : RepoImpl) : Prop := impl.value = 0\n"
        "def spec_bad (impl : RepoImpl) : Prop := impl.value = 1\n",
        encoding="utf-8",
    )
    (task / "lakefile.toml").write_text(
        'name = "Tiny"\n[[lean_lib]]\nname = "Tiny"\n', encoding="utf-8"
    )
    (task / "lean-toolchain").write_text("leanprover/lean4:v4.29.1\n", encoding="utf-8")
    (task / "manifest.json").write_text(
        json.dumps(
            {
                "benchmark_id": "Tiny",
                "trusted_axioms": ["cheat"],
                "packages": [
                    {
                        "name": "Tiny",
                        "modules": [
                            {
                                "name": "Model",
                                "spec": "Tiny.lean",
                                "apis": [{"name": "value"}],
                                "specs": ["spec_good", {"name": "spec_bad"}],
                            }
                        ],
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    (tmp_path / "certificates/Tiny").mkdir(parents=True)
    return tmp_path


def test_inventory_and_unresolved_exit(repository):
    catalog = new_catalog(repository)
    validate_catalog(repository, catalog)
    assert catalog["tasks"]["Tiny"]["apis"] == 1
    assert len(catalog["entries"]) == 2
    (repository / "certificates/catalog.json").write_text(
        json.dumps(catalog), encoding="utf-8"
    )
    assert (
        main(["--root", str(repository), "--output", str(repository / "result.json")])
        == 1
    )
    assert not json.loads((repository / "result.json").read_text(encoding="utf-8"))[
        "complete"
    ]


@pytest.mark.parametrize(
    "mutation",
    [
        "missing",
        "duplicate",
        "wrong_task",
        "wrong_spec",
        "wrong_file",
        "invalid_status",
    ],
)
def test_reject_bad_catalog(repository, mutation):
    catalog = new_catalog(repository)
    if mutation == "missing":
        catalog["entries"].pop()
    elif mutation == "duplicate":
        catalog["entries"].append(copy.deepcopy(catalog["entries"][0]))
    else:
        field, value = {
            "wrong_task": ("task", "AnotherTask"),
            "wrong_spec": ("spec", "spec_other"),
            "wrong_file": ("spec_file", "Other.lean"),
            "invalid_status": ("status", "compiled"),
        }[mutation]
        catalog["entries"][0][field] = value
    with pytest.raises(CatalogError):
        validate_catalog(repository, catalog)


@pytest.mark.parametrize(
    "relative", ["Tiny.lean", "manifest.json", "lakefile.toml", "Aux.lean"]
)
def test_source_drift_rejected(repository, relative):
    catalog = new_catalog(repository)
    path = repository / "benchmarks/Tiny" / relative
    path.write_text(
        (path.read_text(encoding="utf-8") if path.exists() else "")
        + ("\n " if relative == "manifest.json" else "\n-- drift\n"),
        encoding="utf-8",
    )
    with pytest.raises(CatalogError, match="drift"):
        validate_catalog(repository, catalog)


def test_certificate_path_and_declaration_uniqueness(repository):
    catalog = new_catalog(repository)
    for entry in catalog["entries"]:
        entry.update(
            status="proven",
            declaration="proof",
            certificate_file="certificates/Tiny/Proof.lean",
        )
    (repository / "certificates/Tiny/Proof.lean").write_text("", encoding="utf-8")
    with pytest.raises(CatalogError, match="duplicate certificate"):
        validate_catalog(repository, catalog)
    catalog["entries"][1]["declaration"] = "proof2"
    catalog["entries"][0]["certificate_file"] = "certificates/Tiny/../../secret.lean"
    with pytest.raises(CatalogError, match="unsafe path"):
        validate_catalog(repository, catalog)


def test_duplicate_json_and_complete_inventory(repository):
    catalog = new_catalog(repository)
    (repository / "certificates/catalog.json").write_text(
        '{"schema_version": 1, "schema_version": 1}', encoding="utf-8"
    )
    output = repository / "result.json"
    assert main(["--root", str(repository), "--output", str(output)]) == 2
    assert (
        "duplicate JSON key" in json.loads(output.read_text(encoding="utf-8"))["error"]
    )
    catalog["entries"][0]["harness_file"] = "Other.lean"
    with pytest.raises(CatalogError, match="wrong specification"):
        validate_catalog(repository, catalog)


def test_all_repository_specs_enumerated():
    root = Path(__file__).resolve().parents[2]
    catalog = new_catalog(root)
    assert len(catalog["tasks"]) == 43
    assert sum(t["apis"] for t in catalog["tasks"].values()) == 743
    assert len(catalog["entries"]) == 2705


@pytest.mark.slow
@pytest.mark.skipif(shutil.which("lean") is None, reason="requires real Lean")
@pytest.mark.parametrize(
    "status,spec,body,accepted",
    [
        (
            "proven",
            "spec_good",
            "theorem certificate : spec_good canonical := rfl",
            True,
        ),
        (
            "refuted",
            "spec_bad",
            "theorem certificate : ¬ spec_bad canonical := by unfold spec_bad canonical; decide",
            True,
        ),
        (
            "proven",
            "spec_good",
            "theorem certificate : spec_good canonical := by sorry",
            False,
        ),
        (
            "proven",
            "spec_good",
            "axiom cheat : False\ntheorem certificate : spec_good canonical := cheat.elim",
            False,
        ),
        ("proven", "spec_good", "theorem certificate : True := True.intro", False),
        ("proven", "spec_good", "axiom certificate : spec_good canonical", False),
        ("proven", "spec_good", "def certificate : spec_good canonical := rfl", False),
        (
            "proven",
            "spec_good",
            (
                "axiom hidden : False\nopaque helper : False := hidden\n"
                "theorem certificate : spec_good canonical := helper.elim"
            ),
            False,
        ),
        (
            "proven",
            "spec_good",
            (
                "namespace Fake\ndef spec_good (_ : RepoImpl) : Prop := True\n"
                "theorem certificate : spec_good canonical := True.intro\nend Fake"
            ),
            False,
        ),
        (
            "proven",
            "spec_good",
            "unsafe def escape : Nat := 0\ntheorem certificate : spec_good canonical := rfl",
            False,
        ),
    ],
)
def test_real_lean_certificates(repository, status, spec, body, accepted):
    entry = next(e for e in new_catalog(repository)["entries"] if e["spec"] == spec)
    entry.update(
        status=status,
        declaration="Fake.certificate" if "namespace Fake" in body else "certificate",
        certificate_file="certificates/Tiny/Proof.lean",
    )
    (repository / entry["certificate_file"]).write_text(
        "import Tiny\n" + body + "\n", encoding="utf-8"
    )
    (result,) = check_task(repository, "Tiny", [entry], timeout=120)
    assert result["checked"] == accepted, result["error"]
    if accepted:
        assert set(result["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}


@pytest.mark.slow
@pytest.mark.skipif(shutil.which("lean") is None, reason="requires real Lean")
def test_unsafe_canonical_rejected(repository):
    task = repository / "benchmarks/Tiny/Tiny.lean"
    task.write_text(
        task.read_text(encoding="utf-8").replace(
            "def canonical", "unsafe def canonical"
        ),
        encoding="utf-8",
    )
    entry = new_catalog(repository)["entries"][0]
    entry.update(
        status="proven",
        declaration="certificate",
        certificate_file="certificates/Tiny/Proof.lean",
    )
    (repository / entry["certificate_file"]).write_text(
        "import Tiny\nunsafe def certificate : spec_good canonical := rfl\n",
        encoding="utf-8",
    )
    (result,) = check_task(repository, "Tiny", [entry], timeout=120)
    assert not result["checked"]


@pytest.mark.slow
@pytest.mark.skipif(shutil.which("lean") is None, reason="requires real Lean")
def test_canonical_extra_field_axiom_rejected(repository):
    task = repository / "benchmarks/Tiny/Tiny.lean"
    task.write_text(
        "axiom hidden : Nat\n"
        "structure RepoImpl where\n  value : Nat\n  unused : Nat\n"
        "noncomputable def canonical : RepoImpl := ⟨0, hidden⟩\n"
        "def spec_good (impl : RepoImpl) : Prop := impl.value = 0\n",
        encoding="utf-8",
    )
    entry = new_catalog(repository)["entries"][0]
    entry.update(
        status="proven",
        declaration="certificate",
        certificate_file="certificates/Tiny/Proof.lean",
    )
    (repository / entry["certificate_file"]).write_text(
        "import Tiny\ntheorem certificate : spec_good canonical := rfl\n",
        encoding="utf-8",
    )
    (result,) = check_task(repository, "Tiny", [entry], timeout=120)
    assert not result["checked"]
    assert "unapproved certificate axiom: hidden" in result["error"]


@pytest.mark.slow
@pytest.mark.skipif(shutil.which("lean") is None, reason="requires real Lean")
def test_namespace_target_and_certificate_options_isolated(repository):
    task = repository / "benchmarks/Tiny/Tiny.lean"
    task.write_text(
        "namespace Model\n" + task.read_text(encoding="utf-8") + "end Model\n",
        encoding="utf-8",
    )
    entry = new_catalog(repository)["entries"][0]
    entry.update(
        status="proven",
        declaration="Proof.certificate",
        certificate_file="certificates/Tiny/Proof.lean",
    )
    (repository / entry["certificate_file"]).write_text(
        "import Tiny\nset_option maxHeartbeats 100\n"
        "namespace Proof\nopen Model\n"
        "theorem certificate : spec_good canonical := rfl\nend Proof\n",
        encoding="utf-8",
    )
    # An old binary is never a substitute for the current frozen source.
    (repository / "benchmarks/Tiny/Tiny.olean").write_bytes(b"untrusted stale binary")
    (result,) = check_task(repository, "Tiny", [entry], timeout=120)
    assert result["checked"], result["error"]


@pytest.mark.slow
@pytest.mark.skipif(shutil.which("lean") is None, reason="requires real Lean")
def test_expanded_projection_passes_but_reference_blocks_complete(repository):
    task = repository / "benchmarks/Tiny/Tiny.lean"
    task.write_text(
        "axiom hidden : Nat\n"
        "structure RepoImpl where\n  value : Nat\n  unused : Nat\n"
        "noncomputable def canonical : RepoImpl := ⟨0, hidden⟩\n"
        "def spec_good (impl : RepoImpl) : Prop := impl.value = 0\n"
        "def spec_bad (impl : RepoImpl) : Prop := impl.value = 1\n",
        encoding="utf-8",
    )
    catalog = new_catalog(repository)
    catalog["entries"] = [catalog["entries"][0]]
    # This test intentionally exercises check_task directly for the projection;
    # main's complete gate is tested separately with an exhaustive one-spec manifest.
    entry = catalog["entries"][0]
    entry.update(
        status="proven",
        declaration="certificate",
        certificate_file="certificates/Tiny/Proof.lean",
    )
    (repository / entry["certificate_file"]).write_text(
        "import Tiny\ntheorem certificate : (0 : Nat) = 0 := rfl\n",
        encoding="utf-8",
    )
    (result,) = check_task(repository, "Tiny", [entry], timeout=120)
    assert result["checked"], result["error"]
    assert result["axioms"] == []
    assert {"kind": "axiom", "declaration": "hidden"} in result["reference_assumptions"]

    manifest_path = repository / "benchmarks/Tiny/manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["packages"][0]["modules"][0]["specs"] = ["spec_good"]
    manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
    catalog["tasks"] = new_catalog(repository)["tasks"]
    (repository / "certificates/catalog.json").write_text(
        json.dumps(catalog), encoding="utf-8"
    )
    output = repository / "result.json"
    assert main(["--root", str(repository), "--output", str(output)]) == 1
    payload = json.loads(output.read_text(encoding="utf-8"))
    assert payload["summary"] == {"proven": 1, "refuted": 0, "unresolved": 0}
    assert not payload["complete"]
    assert payload["reference_assumptions"]["Tiny"]


@pytest.mark.slow
@pytest.mark.skipif(shutil.which("lean") is None, reason="requires real Lean")
def test_certificate_helper_source_and_individual_rejection(repository):
    entries = new_catalog(repository)["entries"]
    for entry in entries:
        entry.update(status="proven", certificate_file="certificates/Tiny/Proof.lean")
    entries[0]["declaration"] = "good"
    entries[1]["declaration"] = "bad"
    (repository / "certificates/Tiny/Helper.lean").write_text(
        "theorem helper : (0 : Nat) = 0 := rfl\n", encoding="utf-8"
    )
    (repository / "certificates/Tiny/Proof.lean").write_text(
        "import Tiny\nimport Helper\n"
        "theorem good : spec_good canonical := helper\n"
        "theorem bad : True := True.intro\n",
        encoding="utf-8",
    )
    good, bad = check_task(repository, "Tiny", entries, timeout=120)
    assert good["checked"], good["error"]
    assert not bad["checked"]


@pytest.mark.slow
@pytest.mark.skipif(shutil.which("lean") is None, reason="requires real Lean")
def test_skipped_kernel_check_cannot_forge_certificate(repository, monkeypatch):
    entry = new_catalog(repository)["entries"][0]
    entry.update(
        status="proven",
        declaration="certificate",
        certificate_file="certificates/Tiny/Proof.lean",
    )
    (repository / entry["certificate_file"]).write_text(
        "import Lean\nimport Tiny\n"
        "set_option debug.skipKernelTC true\n"
        "run_meta do\n"
        "  let target ← Lean.Meta.mkAppM `spec_good #[Lean.mkConst `canonical]\n"
        "  Lean.addDecl (.thmDecl { name := `certificate, levelParams := [], "
        "type := target, value := Lean.mkConst ``True.intro })\n",
        encoding="utf-8",
    )
    from vero.certification import check

    original_run = check._run
    compiled = []

    def record_run(command, *args, **kwargs):
        output = original_run(command, *args, **kwargs)
        if "-o" in command and Path(command[-1]).name == "Proof.lean":
            compiled.append(True)
        return output

    monkeypatch.setattr(check, "_run", record_run)
    (result,) = check_task(repository, "Tiny", [entry], timeout=120)
    assert compiled, "negative fixture must compile successfully before kernel replay"
    assert not result["checked"], "forged theorem must be rejected by kernel replay"
    assert "replaying" in result["error"], result["error"]


@pytest.mark.parametrize("filename", ["tiny.lean", "verocertificatedriver.lean"])
def test_casefold_certificate_collision_rejected(repository, monkeypatch, filename):
    monkeypatch.setattr("vero.certification.check._run", lambda *a, **k: "4.29.1")
    entry = new_catalog(repository)["entries"][0]
    entry.update(
        status="proven",
        declaration="certificate",
        certificate_file=f"certificates/Tiny/{filename}",
    )
    (repository / entry["certificate_file"]).write_text("", encoding="utf-8")
    with pytest.raises(CatalogError, match="shadows trusted source"):
        check_task(repository, "Tiny", [entry])


def test_deferred_task_cannot_replace_frozen_sources(repository, monkeypatch):
    catalog = new_catalog(repository)
    path = repository / "benchmarks/Tiny/Tiny.lean"

    def mutate_after_initial_validation(*args, **kwargs):
        path.write_text(
            path.read_text(encoding="utf-8") + "\n-- concurrent change\n",
            encoding="utf-8",
        )
        return "4.29.1"

    monkeypatch.setattr(
        "vero.certification.check._run", mutate_after_initial_validation
    )
    with pytest.raises(CatalogError, match="frozen source drift"):
        check_task(
            repository,
            "Tiny",
            catalog["entries"],
            expected_sources=catalog["tasks"]["Tiny"]["sources"],
        )


def test_deferred_task_cannot_replace_frozen_certificate(repository, monkeypatch):
    from vero.certification.check import certificate_sources

    path = repository / "certificates/Tiny/Proof.lean"
    path.write_text("", encoding="utf-8")
    expected = certificate_sources(repository)
    entries = new_catalog(repository)["entries"]

    def mutate_after_initial_validation(*args, **kwargs):
        path.write_text("-- changed while another task was running\n", encoding="utf-8")
        return "4.29.1"

    monkeypatch.setattr(
        "vero.certification.check._run", mutate_after_initial_validation
    )
    with pytest.raises(CatalogError, match="frozen certificate source drift"):
        check_task(repository, "Tiny", entries, expected_certificate_sources=expected)


def test_default_cli_rechecks_certificate_hashes_at_end(repository, monkeypatch):
    from vero.certification.check import certificate_sources, write_catalog

    path = repository / "certificates/Tiny/Proof.lean"
    path.write_text("", encoding="utf-8")
    catalog = new_catalog(repository)
    catalog["certificate_sources"] = certificate_sources(repository)
    write_catalog(repository / "certificates/catalog.json", catalog)

    def mutate_after_check(root, task, entries, **kwargs):
        assert kwargs["expected_certificate_sources"] == catalog["certificate_sources"]
        path.write_text("-- late drift\n", encoding="utf-8")
        return [
            dict(
                e,
                checked=False,
                error="unresolved",
                axioms=[],
                reference_assumptions=[],
            )
            for e in entries
        ]

    monkeypatch.setattr("vero.certification.check.check_task", mutate_after_check)
    output = repository / "result.json"
    assert main(["--root", str(repository), "--output", str(output)]) == 2
    assert (
        "certificate source drift"
        in json.loads(output.read_text(encoding="utf-8"))["error"]
    )


@pytest.mark.slow
@pytest.mark.skipif(shutil.which("lean") is None, reason="requires real Lean")
def test_unused_certificate_theorem_with_sorry_is_rejected(repository, monkeypatch):
    entry = new_catalog(repository)["entries"][0]
    entry.update(
        status="proven",
        declaration="certificate",
        certificate_file="certificates/Tiny/Proof.lean",
    )
    (repository / entry["certificate_file"]).write_text(
        "import Tiny\ntheorem hidden : False := by sorry\ntheorem certificate : spec_good canonical := rfl\n",
        encoding="utf-8",
    )
    from vero.certification import check

    original_run = check._run
    compiled = []

    def record(command, *args, **kwargs):
        output = original_run(command, *args, **kwargs)
        if "-o" in command and Path(command[-1]).name == "Proof.lean":
            compiled.append(True)
        return output

    monkeypatch.setattr(check, "_run", record)
    (result,) = check_task(repository, "Tiny", [entry], timeout=120)
    assert compiled
    assert not result["checked"]
    assert "sorryAx" in result["error"], result["error"]


@pytest.mark.slow
@pytest.mark.skipif(shutil.which("lean") is None, reason="requires real Lean")
def test_unused_benchmark_theorem_with_sorry_blocks_reference(repository):
    path = repository / "benchmarks/Tiny/Tiny.lean"
    path.write_text(
        path.read_text(encoding="utf-8") + "\ntheorem hidden : False := by sorry\n",
        encoding="utf-8",
    )
    entry = new_catalog(repository)["entries"][0]
    entry.update(
        status="proven",
        declaration="certificate",
        certificate_file="certificates/Tiny/Proof.lean",
    )
    (repository / entry["certificate_file"]).write_text(
        "import Tiny\ntheorem certificate : (0 : Nat) = 0 := rfl\n", encoding="utf-8"
    )
    (result,) = check_task(repository, "Tiny", [entry], timeout=120)
    assert result["checked"], result["error"]
    assert {"kind": "axiom", "declaration": "sorryAx"} in result[
        "reference_assumptions"
    ]


@pytest.mark.slow
@pytest.mark.skipif(shutil.which("lean") is None, reason="requires real Lean")
def test_certificate_cannot_poison_cached_native_driver(repository, monkeypatch):
    entry = new_catalog(repository)["entries"][0]
    entry.update(
        status="proven",
        declaration="certificate",
        certificate_file="certificates/Tiny/Proof.lean",
    )
    (repository / entry["certificate_file"]).write_text(
        "import Tiny\ntheorem certificate : True := True.intro\n", encoding="utf-8"
    )
    from vero.certification import check

    original_run = check._run
    native_paths = []
    tampered = []
    restored = []

    def record(command, cwd, *args, **kwargs):
        if Path(command[0]).name in {"audit-driver", "audit-driver.exe"}:
            native_paths.append(Path(command[0]))
            if tampered:
                restored.append(
                    not native_paths[-1].read_bytes().startswith(b"#!/bin/sh")
                )
        output = original_run(command, cwd, *args, **kwargs)
        if "-o" in command and Path(command[-1]).name == "Proof.lean":
            assert native_paths, (
                "reference phase must build the trusted native driver first"
            )
            native_paths[-1].write_text(
                '#!/bin/sh\nprintf \'[{"declaration":"certificate","checked":true,"axioms":[]}]\\n\'\n',
                encoding="utf-8",
            )
            tampered.append(True)
        return output

    monkeypatch.setattr(check, "_run", record)
    (result,) = check_task(repository, "Tiny", [entry], timeout=120)
    assert tampered and restored == [True]
    assert not result["checked"]
    assert "wrong certificate type" in result["error"], result["error"]


@pytest.mark.slow
@pytest.mark.skipif(shutil.which("lean") is None, reason="requires real Lean")
@pytest.mark.parametrize("attack", ["macro", "initializer"])
def test_certificate_meta_code_cannot_control_audit(repository, monkeypatch, attack):
    entry = new_catalog(repository)["entries"][0]
    entry.update(
        status="proven",
        declaration="certificate",
        certificate_file="certificates/Tiny/Proof.lean",
    )
    injection = (
        'macro (priority := high) "run_meta " _t:term : command =>\n'
        '  `(command| #eval IO.println "VERO_CERTIFICATE_OK certificate AXIOMS []")\n'
        if attack == "macro"
        else "initialize marker : Unit ← do\n"
        '  IO.FS.writeFile "initializer-fired" "executed"\n'
        '  IO.println "VERO_CERTIFICATE_OK certificate AXIOMS []"\n'
    )
    (repository / entry["certificate_file"]).write_text(
        "import Lean\nimport Tiny\n"
        + injection
        + "theorem certificate : True := True.intro\n",
        encoding="utf-8",
    )
    from vero.certification import check

    original_run = check._run
    compiled = []
    legacy_spoofed = []
    marker_paths = []
    runtime_initializers = []

    def record_run(command, cwd, *args, **kwargs):
        output = original_run(command, cwd, *args, **kwargs)
        if (
            Path(command[0]).name in {"audit-driver", "audit-driver.exe"}
            and marker_paths
        ):
            runtime_initializers.append((cwd / "initializer-fired").exists())
        if "-o" in command and Path(command[-1]).name == "Proof.lean":
            compiled.append(True)
            marker = cwd / "initializer-fired"
            marker.unlink(missing_ok=True)
            marker_paths.append(marker)
            if attack == "macro":
                probe = cwd / "LegacyProbe.lean"
                probe.write_text(
                    "import Proof\nrun_meta (pure () : Lean.MetaM Unit)\n",
                    encoding="utf-8",
                )
                legacy_spoofed.append(
                    "VERO_CERTIFICATE_OK certificate AXIOMS []"
                    in original_run(["lean", str(probe)], cwd, *args, **kwargs)
                )
        return output

    monkeypatch.setattr(check, "_run", record_run)
    (result,) = check_task(repository, "Tiny", [entry], timeout=120)
    assert compiled, "attack fixture must be a valid compiled module"
    if attack == "macro":
        assert legacy_spoofed == [True], (
            "fixture must actually intercept the old audit command"
        )
    assert not result["checked"], result
    assert runtime_initializers and not any(runtime_initializers), (
        "runtime audit must not run certificate initializers"
    )


@pytest.mark.slow
@pytest.mark.skipif(shutil.which("lean") is None, reason="requires real Lean")
def test_unused_imported_benchmark_axiom_is_reference_blocker(repository):
    task = repository / "benchmarks/Tiny/Tiny.lean"
    task.write_text(
        task.read_text(encoding="utf-8") + "\naxiom unrelated : False\n",
        encoding="utf-8",
    )
    entry = new_catalog(repository)["entries"][0]
    entry.update(
        status="proven",
        declaration="certificate",
        certificate_file="certificates/Tiny/Proof.lean",
    )
    (repository / entry["certificate_file"]).write_text(
        "import Tiny\ntheorem certificate : (0 : Nat) = 0 := rfl\n", encoding="utf-8"
    )
    (result,) = check_task(repository, "Tiny", [entry], timeout=120)
    assert result["checked"], result["error"]
    assert {"kind": "axiom", "declaration": "unrelated"} in result[
        "reference_assumptions"
    ]


def test_failed_claim_becomes_unresolved(repository, monkeypatch):
    catalog = new_catalog(repository)
    entry = catalog["entries"][0]
    entry.update(
        status="proven",
        declaration="certificate",
        certificate_file="certificates/Tiny/Proof.lean",
    )
    (repository / entry["certificate_file"]).write_text("", encoding="utf-8")
    (repository / "certificates/catalog.json").write_text(
        json.dumps(catalog), encoding="utf-8"
    )

    def fail(root, task, entries, **kwargs):
        return [dict(e, checked=False, axioms=[], error="rejected") for e in entries]

    monkeypatch.setattr("vero.certification.check.check_task", fail)
    output = repository / "result.json"
    assert main(["--root", str(repository), "--output", str(output)]) == 1
    result = json.loads(output.read_text(encoding="utf-8"))
    assert result["summary"] == {"proven": 0, "refuted": 0, "unresolved": 2}
    assert result["entries"][0]["claimed_status"] == "proven"
    assert result["entries"][0]["status"] == "unresolved"


def test_candidate_is_not_proven_until_checked(repository, monkeypatch):
    from vero.certification.check import certificate_sources, write_catalog

    catalog = new_catalog(repository)
    (repository / "certificates/Tiny/Proof.lean").write_text("", encoding="utf-8")
    catalog["entries"][0]["candidates"] = [
        {
            "status": "proven",
            "declaration": "certificate",
            "certificate_file": "certificates/Tiny/Proof.lean",
        }
    ]
    catalog["certificate_sources"] = certificate_sources(repository)
    path = repository / "certificates/catalog.json"
    write_catalog(path, catalog)
    validate_catalog(repository, json.loads(path.read_text(encoding="utf-8")))
    assert (
        json.loads(path.read_text(encoding="utf-8"))["entries"][0]["status"]
        == "unresolved"
    )

    def fake_check(root, task, entries, **kwargs):
        return [
            dict(
                e,
                checked=e.get("declaration") == "certificate",
                axioms=[],
                error=None,
                reference_assumptions=[],
            )
            for e in entries
        ]

    monkeypatch.setattr("vero.certification.check.check_task", fake_check)
    output = repository / "result.json"
    assert (
        main(
            [
                "--root",
                str(repository),
                "--certify-candidates",
                "--write-catalog",
                "--output",
                str(output),
            ]
        )
        == 1
    )
    saved = json.loads(path.read_text(encoding="utf-8"))
    assert [e["status"] for e in saved["entries"]] == ["proven", "unresolved"]
    assert "candidates" not in saved["entries"][0]
    assert len(json.loads(output.read_text(encoding="utf-8"))["entries"]) == 2
    validate_catalog(repository, saved)


def test_candidate_rejection_and_certificate_hash_drift(repository, monkeypatch):
    from vero.certification.check import certificate_sources, write_catalog

    path = repository / "certificates/Tiny/Proof.lean"
    path.write_text("", encoding="utf-8")
    catalog = new_catalog(repository)
    catalog["entries"][0]["candidates"] = [
        {
            "status": "proven",
            "declaration": "certificate",
            "certificate_file": "certificates/Tiny/Proof.lean",
        }
    ]
    catalog["certificate_sources"] = certificate_sources(repository)
    catalog_path = repository / "certificates/catalog.json"
    write_catalog(catalog_path, catalog)

    def fake_check(root, task, entries, **kwargs):
        return [
            dict(
                e,
                checked=False,
                axioms=[],
                error="kernel rejected",
                reference_assumptions=[],
            )
            for e in entries
        ]

    monkeypatch.setattr("vero.certification.check.check_task", fake_check)
    assert (
        main(
            [
                "--root",
                str(repository),
                "--certify-candidates",
                "--write-catalog",
                "--output",
                str(repository / "result.json"),
            ]
        )
        == 1
    )
    assert all(
        e["status"] == "unresolved"
        for e in json.loads(catalog_path.read_text(encoding="utf-8"))["entries"]
    )
    path.write_text("-- drift\n", encoding="utf-8")
    with pytest.raises(CatalogError, match="certificate source drift"):
        validate_catalog(repository, catalog)


def test_candidate_cannot_replace_manifest_spec_or_canonical_source(repository):
    catalog = new_catalog(repository)
    path = repository / "certificates/Tiny/Proof.lean"
    path.write_text("", encoding="utf-8")
    catalog["entries"][0]["candidates"] = [
        {
            "status": "proven",
            "declaration": "certificate",
            "certificate_file": "certificates/Tiny/Proof.lean",
            "spec_file": "Forged.lean",
        }
    ]
    with pytest.raises(CatalogError, match="override its manifest target"):
        validate_catalog(repository, catalog)


def test_unselected_task_drift_does_not_replace_selected_snapshot(repository):
    shutil.copytree(repository / "benchmarks/Tiny", repository / "benchmarks/Other")
    catalog = new_catalog(repository)
    path = repository / "benchmarks/Other/Tiny.lean"
    path.write_text(
        path.read_text(encoding="utf-8") + "\n-- pending unrelated edit\n",
        encoding="utf-8",
    )
    validate_catalog(repository, catalog, selected={"Tiny"})
    with pytest.raises(CatalogError, match="frozen source drift"):
        validate_catalog(repository, catalog)


def test_refresh_source_hashes_revokes_old_proof_before_rechecking(
    repository, monkeypatch
):
    from vero.certification.check import certificate_sources, write_catalog

    catalog = new_catalog(repository)
    path = repository / "certificates/Tiny/Proof.lean"
    path.write_text("", encoding="utf-8")
    catalog["entries"][0].update(
        status="proven",
        declaration="certificate",
        certificate_file="certificates/Tiny/Proof.lean",
    )
    catalog["certificate_sources"] = certificate_sources(repository)
    catalog_path = repository / "certificates/catalog.json"
    write_catalog(catalog_path, catalog)
    source = repository / "benchmarks/Tiny/Tiny.lean"
    source.write_text(
        source.read_text(encoding="utf-8") + "\n-- approved semantic revision\n",
        encoding="utf-8",
    )
    observations = []

    def fake_check(root, task, entries, **kwargs):
        observations.append(
            all(e["status"] == "unresolved" and "declaration" not in e for e in entries)
        )
        return [
            dict(
                e,
                checked=False,
                axioms=[],
                error="not revalidated",
                reference_assumptions=[],
            )
            for e in entries
        ]

    monkeypatch.setattr("vero.certification.check.check_task", fake_check)
    assert (
        main(
            [
                "--root",
                str(repository),
                "--refresh-source-hashes",
                "--write-catalog",
                "--output",
                str(repository / "result.json"),
            ]
        )
        == 1
    )
    saved = json.loads(catalog_path.read_text(encoding="utf-8"))
    assert observations == [True]
    assert saved["entries"][0]["status"] == "unresolved"
    assert saved["entries"][0]["candidates"][0]["declaration"] == "certificate"


def test_partial_refresh_does_not_rebind_unselected_proof(repository, monkeypatch):
    from vero.certification.check import certificate_sources, write_catalog

    shutil.copytree(repository / "benchmarks/Tiny", repository / "benchmarks/Other")
    (repository / "certificates/Other").mkdir()
    for task in ("Tiny", "Other"):
        (repository / f"certificates/{task}/Proof.lean").write_text(
            "", encoding="utf-8"
        )
    catalog = new_catalog(repository)
    for entry in catalog["entries"]:
        if entry["spec"] == "spec_good":
            entry.update(
                status="proven",
                declaration="certificate",
                certificate_file=f"certificates/{entry['task']}/Proof.lean",
            )
    catalog["certificate_sources"] = certificate_sources(repository)
    old = catalog["certificate_sources"]["certificates/Other/Proof.lean"]
    write_catalog(repository / "certificates/catalog.json", catalog)
    (repository / "certificates/Other/Proof.lean").write_text(
        "-- unselected edit\n", encoding="utf-8"
    )
    monkeypatch.setattr(
        "vero.certification.check.check_task",
        lambda root, task, entries, **kwargs: [
            dict(
                e,
                checked=False,
                error="not checked",
                axioms=[],
                reference_assumptions=[],
            )
            for e in entries
        ],
    )
    assert (
        main(
            [
                "--root",
                str(repository),
                "--task",
                "Tiny",
                "--refresh-source-hashes",
                "--write-catalog",
                "--output",
                str(repository / "result.json"),
            ]
        )
        == 1
    )
    saved = json.loads(
        (repository / "certificates/catalog.json").read_text(encoding="utf-8")
    )
    assert saved["certificate_sources"]["certificates/Other/Proof.lean"] == old
    assert (
        next(
            e
            for e in saved["entries"]
            if e["task"] == "Other" and e["spec"] == "spec_good"
        )["status"]
        == "proven"
    )
    with pytest.raises(CatalogError, match="certificate source drift"):
        validate_catalog(repository, saved)


def test_partial_runs_preserve_global_summary_and_reference_results(
    repository, monkeypatch
):
    from vero.certification.check import write_catalog

    shutil.copytree(repository / "benchmarks/Tiny", repository / "benchmarks/Other")
    (repository / "certificates/Other").mkdir()
    for task in ("Tiny", "Other"):
        (repository / f"certificates/{task}/Proof.lean").write_text(
            "", encoding="utf-8"
        )
    write_catalog(repository / "certificates/catalog.json", new_catalog(repository))

    def fake_check(root, task, entries, **kwargs):
        return [
            dict(
                e,
                status="proven" if e["spec"] == "spec_good" else "unresolved",
                checked=e["spec"] == "spec_good",
                declaration="certificate",
                certificate_file=f"certificates/{task}/Proof.lean",
                error=None,
                axioms=[],
                reference_assumptions=[]
                if task == "Tiny"
                else [{"kind": "axiom", "declaration": "Other.semantic"}],
            )
            for e in entries
        ]

    monkeypatch.setattr("vero.certification.check.check_task", fake_check)
    for task in ("Tiny", "Other"):
        assert (
            main(
                [
                    "--root",
                    str(repository),
                    "--task",
                    task,
                    "--write-catalog",
                    "--output",
                    str(repository / f"{task}.json"),
                ]
            )
            == 1
        )
    saved = json.loads(
        (repository / "certificates/catalog.json").read_text(encoding="utf-8")
    )["validation"]
    assert saved["summary"] == {"proven": 2, "refuted": 0, "unresolved": 2}
    assert saved["tasks_checked"] == ["Other", "Tiny"]
    assert set(saved["reference_assumptions"]) == {"Other", "Tiny"}
    assert saved["checker_sha256"] and saved["auditor_sha256"]
    assert not saved["complete"]


def test_checker_hash_is_captured_at_start_and_drift_fails(repository, monkeypatch):
    from vero.certification.check import write_catalog

    write_catalog(repository / "certificates/catalog.json", new_catalog(repository))
    identities = iter(
        [
            {"checker_sha256": "before", "auditor_sha256": "same"},
            {"checker_sha256": "after", "auditor_sha256": "same"},
        ]
    )
    monkeypatch.setattr(
        "vero.certification.check._checker_identity", lambda: next(identities)
    )
    monkeypatch.setattr(
        "vero.certification.check.check_task",
        lambda root, task, entries, **kwargs: [
            dict(
                e,
                checked=False,
                error="unresolved",
                axioms=[],
                reference_assumptions=[],
            )
            for e in entries
        ],
    )
    output = repository / "result.json"
    assert main(["--root", str(repository), "--output", str(output)]) == 2
    assert (
        "checker source drift"
        in json.loads(output.read_text(encoding="utf-8"))["error"]
    )


def test_certificate_compilation_cannot_replace_fixed_benchmark(
    repository, monkeypatch
):
    entry = new_catalog(repository)["entries"][0]
    entry.update(
        status="proven",
        declaration="certificate",
        certificate_file="certificates/Tiny/Proof.lean",
    )
    (repository / entry["certificate_file"]).write_text(
        "import Tiny\n", encoding="utf-8"
    )
    original_source = (repository / "benchmarks/Tiny/Tiny.lean").read_bytes()
    observed_restoration = []

    def fake_run(command, cwd, timeout, env=None):
        if "--short-version" in command:
            return "4.29.1"
        if "--src-deps" in command:
            return (
                str(cwd / "Tiny.lean") if Path(command[-1]).name == "Proof.lean" else ""
            )
        if command[0] == "leanc":
            Path(command[command.index("-o") + 1]).write_bytes(b"fake native driver")
            return ""
        if "-o" in command:
            file = Path(command[-1])
            if not file.is_absolute():
                file = cwd / file
            output = Path(command[command.index("-o") + 1])
            if not output.is_absolute():
                output = cwd / output
            output.write_bytes(b"original " + file.stem.encode())
            if file.name == "Proof.lean":
                (cwd / "Tiny.lean").write_text(
                    "-- attacker substituted source", encoding="utf-8"
                )
                (cwd / "Tiny.olean").write_bytes(b"attacker substituted canonical")
            return ""
        if command[0] == "leanchecker":
            assert (cwd / "Tiny.olean").read_bytes() == b"original Tiny"
            return ""
        if Path(command[0]).name in {"audit-driver", "audit-driver.exe"}:
            request = json.loads(Path(command[-1]).read_text(encoding="utf-8"))
            assert (cwd / "Tiny.lean").read_bytes() == original_source
            assert (cwd / "Tiny.olean").read_bytes() == b"original Tiny"
            observed_restoration.append(True)
            return (
                "[]"
                if request["reference"]
                else '[{"declaration":"certificate","checked":true,"axioms":[]}]'
            )
        raise AssertionError(command)

    monkeypatch.setattr("vero.certification.check._run", fake_run)
    (result,) = check_task(repository, "Tiny", [entry])
    assert result["checked"], result["error"]
    assert observed_restoration == [True, True]
