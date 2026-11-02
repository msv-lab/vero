"""Fail-closed reference certification; deliberately independent of grading.

Run ``python -m vero.certification --task primepy``. A successful Lean build
alone never changes an unresolved entry into a proof. The JSON result contains
every selected specification, with individually checked evidence and errors.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

STATES = {"proven", "refuted", "unresolved"}
IDENTIFIER = re.compile(r"[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*\Z")
CONFIGS = {
    "manifest.json",
    "lakefile.toml",
    "lakefile.lean",
    "lake-manifest.json",
    "lean-toolchain",
}


class CatalogError(ValueError):
    pass


def _json(path: Path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise CatalogError(f"duplicate JSON key {key}: {path}")
            result[key] = value
        return result

    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique)


def _safe(root: Path, relative: str) -> Path:
    path = root / relative
    if Path(relative).is_absolute() or ".." in Path(relative).parts:
        raise CatalogError(f"unsafe path: {relative}")
    if not path.resolve().is_relative_to(root.resolve()):
        raise CatalogError(f"path outside repository: {relative}")
    if any(
        parent.is_symlink() for parent in [path, *path.parents] if parent != root.parent
    ):
        raise CatalogError(f"symlink not permitted: {relative}")
    return path


def frozen_sources(task: Path) -> dict[str, str]:
    """Hash every Lean source and build input, never cached .olean output.

    UTF-8 LF normalization makes a Git CRLF checkout equivalent to its LF
    checkout. All semantic source changes (including auxiliary files) differ.
    """
    result = {}
    for directory, directories, files in os.walk(task, followlinks=False):
        directories[:] = sorted(
            name for name in directories if not name.startswith(".")
        )
        for name in directories:
            if (Path(directory) / name).is_symlink():
                raise CatalogError(f"symlink not permitted: {Path(directory) / name}")
        for name in files:
            path = Path(directory) / name
            if name.startswith(".") or (path.suffix != ".lean" and name not in CONFIGS):
                continue
            rel = path.relative_to(task)
            _safe(task, rel.as_posix())
            data = path.read_bytes().replace(b"\r\n", b"\n")
            result[rel.as_posix()] = hashlib.sha256(data).hexdigest()
    return dict(sorted(result.items()))


def inventory(root: Path) -> tuple[dict, list[dict]]:
    tasks, entries = {}, []
    for manifest_path in sorted((root / "benchmarks").glob("*/manifest.json")):
        task = manifest_path.parent.name
        manifest = _json(manifest_path)
        apis = 0
        for package in manifest["packages"]:
            for module in package["modules"]:
                apis += sum(api.get("kind", "api") == "api" for api in module["apis"])
                for spec in module.get("specs", []):
                    if isinstance(spec, dict):
                        spec = spec.get("lean_name") or spec["name"]
                    if not IDENTIFIER.fullmatch(spec):
                        raise CatalogError(f"invalid spec name: {spec}")
                    entries.append(
                        {
                            "task": task,
                            "package": package["name"],
                            "module": module["name"],
                            "spec": spec,
                            "spec_file": module["spec"],
                            "harness_file": manifest.get("files", {}).get(
                                "harness", module["spec"]
                            ),
                            "status": "unresolved",
                        }
                    )
        tasks[task] = {
            "benchmark_id": manifest["benchmark_id"],
            "apis": apis,
            "sources": frozen_sources(manifest_path.parent),
        }
    if not tasks:
        raise CatalogError("no benchmark manifests found")
    return tasks, entries


def entry_key(entry: dict) -> tuple[str, str, str, str]:
    return tuple(entry[k] for k in ("task", "package", "module", "spec"))


def new_catalog(root: Path) -> dict:
    tasks, entries = inventory(root)
    return {"schema_version": 1, "tasks": tasks, "entries": entries}


def certificate_sources(root: Path) -> dict[str, str]:
    return {
        path.relative_to(root).as_posix(): hashlib.sha256(
            _safe(root, path.relative_to(root).as_posix())
            .read_bytes()
            .replace(b"\r\n", b"\n")
        ).hexdigest()
        for path in sorted((root / "certificates").rglob("*.lean"))
        if not any(
            part.startswith(".")
            for part in path.relative_to(root / "certificates").parts
        )
    }


def _validate_evidence(root: Path, task: str, evidence: dict) -> None:
    if not isinstance(evidence, dict):
        raise CatalogError("candidate/evidence must be an object")
    if evidence.get("status") not in {"proven", "refuted"}:
        raise CatalogError("candidate/evidence must name proven or refuted polarity")
    if not isinstance(evidence.get("declaration"), str) or not IDENTIFIER.fullmatch(
        evidence["declaration"]
    ):
        raise CatalogError("invalid certificate declaration")
    relative = evidence.get("certificate_file", "")
    if (
        not isinstance(relative, str)
        or not relative.startswith(f"certificates/{task}/")
        or not relative.endswith(".lean")
    ):
        raise CatalogError("certificate outside task certificate directory")
    if not _safe(root, relative).is_file():
        raise CatalogError(f"missing certificate source: {relative}")


def validate_catalog(
    root: Path, catalog: dict, *, selected: set[str] | None = None
) -> None:
    tasks, expected_entries = inventory(root)
    if catalog.get("schema_version") != 1:
        raise CatalogError("unsupported catalog schema")
    scope = set(tasks) if selected is None else selected
    if set(catalog.get("tasks", {})) != set(tasks) or any(
        catalog["tasks"][task] != tasks[task] for task in scope
    ):
        raise CatalogError(
            "task inventory or frozen source drift (manifest/Lean/build inputs)"
        )
    if "certificate_sources" in catalog:
        frozen = catalog["certificate_sources"]
        actual = certificate_sources(root)
        if scope != set(tasks):
            frozen = {
                p: value for p, value in frozen.items() if Path(p).parts[1] in scope
            }
            actual = {
                p: value for p, value in actual.items() if Path(p).parts[1] in scope
            }
        if frozen != actual:
            raise CatalogError("frozen certificate source drift")
    expected = {entry_key(e): e for e in expected_entries}
    if len(expected) != len(expected_entries):
        raise CatalogError("duplicate manifest specification")
    seen, declarations = set(), set()
    for entry in catalog["entries"]:
        key = entry_key(entry)
        if key in seen:
            raise CatalogError(f"duplicate specification: {key}")
        seen.add(key)
        if key not in expected or any(
            entry.get(field) != expected[key][field]
            for field in ("spec_file", "harness_file")
        ):
            raise CatalogError(f"wrong specification or target source: {key}")
        if entry.get("status") not in STATES:
            raise CatalogError(f"invalid status: {key}")
        if not isinstance(entry.get("candidates", []), list):
            raise CatalogError(f"invalid candidate list: {key}")
        for candidate in entry.get("candidates", []):
            if not isinstance(candidate, dict) or set(candidate) != {
                "status",
                "declaration",
                "certificate_file",
            }:
                raise CatalogError("candidate may not override its manifest target")
            _validate_evidence(root, entry["task"], candidate)
        if entry["status"] == "unresolved":
            if "declaration" in entry or "certificate_file" in entry:
                raise CatalogError(f"unresolved entry claims evidence: {key}")
            continue
        declaration = entry.get("declaration", "")
        _validate_evidence(root, entry["task"], entry)
        if not IDENTIFIER.fullmatch(declaration):
            raise CatalogError(f"invalid declaration: {key}")
        pair = (entry["task"], declaration)
        if pair in declarations:
            raise CatalogError(f"duplicate certificate declaration: {pair}")
        declarations.add(pair)
        relative = entry.get("certificate_file", "")
        if not relative.startswith(
            f"certificates/{entry['task']}/"
        ) or not relative.endswith(".lean"):
            raise CatalogError(f"certificate outside task certificate directory: {key}")
        if not _safe(root, relative).is_file():
            raise CatalogError(f"missing certificate source: {relative}")
    if seen != set(expected):
        raise CatalogError(f"missing specifications: {sorted(set(expected) - seen)}")


def _run(command: list[str], cwd: Path, timeout: int, env: dict | None = None) -> str:
    result = subprocess.run(
        command,
        check=False,
        cwd=cwd,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=timeout,
        env=env,
    )
    output = result.stdout + result.stderr
    if result.returncode:
        raise RuntimeError(f"{command!r} exited {result.returncode}\n{output}")
    return output


def _checker_identity() -> dict[str, str]:
    return {
        name: hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()
        for name, path in (
            ("checker_sha256", Path(__file__)),
            ("auditor_sha256", Path(__file__).with_name("Audit.lean")),
        )
    }


def _failure_reason(error: str | None) -> str:
    if error:
        for line in error.splitlines():
            line = line.strip()
            if line.startswith(
                (
                    "unapproved ",
                    "forbidden certificate ",
                    "unsafe dependency:",
                    "wrong certificate type",
                    "conflicting verified",
                    "source drift",
                )
            ):
                return line[:400]
        if "timed out" in error:
            return "certificate build or independent audit timed out"
        if "replaying declaration" in error:
            return "official leanchecker rejected a local declaration"
        if "excessive memory" in error:
            return "independent verification exceeded the Lean memory limit"
    return "no independently verified certificate"


def _module(path: str) -> str:
    result = Path(path).with_suffix("").as_posix().replace("/", ".")
    if not path.endswith(".lean") or not IDENTIFIER.fullmatch(result):
        raise CatalogError(f"invalid Lean module source: {path}")
    return result


def _requests(entries: list[dict]) -> list[dict]:
    return [
        {
            "declaration": e.get("declaration", ""),
            "spec": e["spec"],
            "specModule": _module(e["spec_file"]),
            "harnessModule": _module(e["harness_file"]),
            "refuted": e["status"] == "refuted",
        }
        for e in entries
    ]


def check_task(
    root: Path,
    task: str,
    entries: list[dict],
    *,
    timeout: int = 600,
    packages: Path | None = None,
    expected_sources: dict[str, str] | None = None,
    expected_certificate_sources: dict[str, str] | None = None,
    workspace_parent: Path | None = None,
    native_driver: dict | None = None,
) -> list[dict]:
    native_driver = {} if native_driver is None else native_driver
    results = [dict(e, checked=False, axioms=[], error="unresolved") for e in entries]
    groups = {}
    for result in results:
        if result["status"] != "unresolved":
            groups.setdefault(result["certificate_file"], []).append(result)
    source = root / "benchmarks" / task
    try:
        toolchain = (source / "lean-toolchain").read_text(encoding="utf-8").strip()
        required = re.fullmatch(
            r"leanprover/lean4:v([0-9]+\.[0-9]+\.[0-9]+)", toolchain
        )
        if required is None:
            raise CatalogError(f"unsupported exact Lean toolchain: {toolchain}")
        actual = _run(["lean", "--short-version"], source, timeout).strip()
        if actual != required[1]:
            raise CatalogError(
                f"wrong Lean toolchain: expected {required[1]}, got {actual}"
            )
    except (OSError, RuntimeError, subprocess.TimeoutExpired, ValueError) as exc:
        for result in results:
            result.update(
                error=str(exc),
                reference_assumptions=[{"kind": "audit_error", "error": str(exc)}],
            )
        return results
    sources_before = frozen_sources(source)
    if expected_sources is not None and sources_before != expected_sources:
        raise CatalogError(f"frozen source drift before certification: {task}")
    certificate_root = root / "certificates" / task
    certificate_sources = {
        file.relative_to(root).as_posix(): _safe(
            root, file.relative_to(root).as_posix()
        ).read_bytes()
        for file in certificate_root.rglob("*.lean")
    }
    if (
        expected_certificate_sources is not None
        and {
            relative: hashlib.sha256(data.replace(b"\r\n", b"\n")).hexdigest()
            for relative, data in certificate_sources.items()
        }
        != expected_certificate_sources
    ):
        raise CatalogError(
            f"frozen certificate source drift before certification: {task}"
        )
    auditor = Path(__file__).with_name("Audit.lean").read_text(encoding="utf-8")
    if workspace_parent is None:
        workspace_context = tempfile.TemporaryDirectory(
            prefix=f"vero-certificate-{task}-"
        )
    else:
        workspace_parent.mkdir(parents=True, exist_ok=True)
        workspace_context = contextlib.nullcontext(
            tempfile.mkdtemp(prefix=f"{task}-", dir=workspace_parent)
        )
    with workspace_context as directory:
        workspace = Path(directory)
        fixed_sources = {}
        for rel, expected_hash in sources_before.items():
            dst = workspace / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source / rel, dst)
            fixed_sources[dst] = dst.read_bytes()
            if (
                hashlib.sha256(dst.read_bytes().replace(b"\r\n", b"\n")).hexdigest()
                != expected_hash
            ):
                raise CatalogError(f"source changed during copy: {task}/{rel}")
        # Only trusted external dependency oleans enter LEAN_PATH. Local modules
        # are rebuilt from the frozen sources in this otherwise empty directory.
        paths = [str(workspace)]
        source_paths = [str(workspace)]
        if packages is not None:
            paths.extend(
                str(p / ".lake/build/lib/lean")
                for p in sorted(packages.resolve().iterdir())
                if p.is_dir()
            )
            source_paths.extend(
                str(p) for p in sorted(packages.resolve().iterdir()) if p.is_dir()
            )
        env = dict(
            os.environ,
            LEAN_PATH=os.pathsep.join(paths),
            LEAN_SRC_PATH=os.pathsep.join(source_paths),
        )
        built, pending = set(), set()
        local_dependencies = {}

        def build(file: Path) -> None:
            if file in built:
                return
            if file in pending:
                raise RuntimeError(f"cyclic Lean imports: {file}")
            pending.add(file)
            # Lean's own parser handles multiline imports and comments. Never
            # infer imports with regex or reuse an input benchmark .olean.
            output = _run(["lean", "--src-deps", str(file)], workspace, timeout, env)
            local_dependencies[file] = []
            for line in output.splitlines():
                dependency = Path(line.strip()).with_suffix(".lean")
                if dependency.is_relative_to(workspace) and dependency != file:
                    if not dependency.is_file():
                        raise RuntimeError(f"missing local Lean import: {dependency}")
                    local_dependencies[file].append(dependency)
                    build(dependency)
            _run(
                ["lean", "-o", str(file.with_suffix(".olean")), str(file)],
                workspace,
                timeout,
                env,
            )
            pending.remove(file)
            built.add(file)

        occupied = {rel.casefold() for rel in sources_before}
        for relative, data in certificate_sources.items():
            local = Path(relative).relative_to(Path("certificates") / task)
            if (
                local.as_posix().casefold() in occupied
                or local.name.casefold().startswith("verocertificate")
                or local.name.casefold().startswith("veroreference")
                or local.name.casefold().startswith("veroevidence")
            ):
                raise CatalogError(
                    f"certificate module shadows trusted source: {relative}"
                )
            dst = workspace / local
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_bytes(data)
            occupied.add(local.as_posix().casefold())
            fixed_sources[dst] = data

        fixed_artifacts = {}

        def preserve_artifacts(files):
            for file in files:
                for artifact in file.parent.glob(file.stem + ".olean*"):
                    fixed_artifacts[artifact] = artifact.read_bytes()

        def restore_fixed_inputs():
            # Source elaboration may run metaprograms with IO. Restore the
            # independently built benchmark and earlier certificate artifacts
            # before reading them in the trusted verification processes.
            for file, data in {**fixed_sources, **fixed_artifacts}.items():
                file.parent.mkdir(parents=True, exist_ok=True)
                file.write_bytes(data)

        def kernel_replay(files=None):
            # Official LeanChecker reconstructs each module in the environment
            # of its imports, with extensions disabled. Every local import is
            # included; only the explicit external cache/toolchain is trusted.
            needed, todo = set(), list(built if files is None else files)
            while todo:
                file = todo.pop()
                if file in needed:
                    continue
                needed.add(file)
                todo.extend(local_dependencies.get(file, []))
            roots = sorted(
                {
                    _module(f.relative_to(workspace).as_posix()).split(".")[0]
                    for f in needed
                }
            )
            if roots:
                _run(
                    ["leanchecker", *roots],
                    workspace,
                    timeout,
                    dict(env, LEAN_NUM_THREADS="1"),
                )

        def run_driver(imports, group, reference):
            request_file = workspace / "VeroCertificateRequest.json"
            request_file.write_text(
                json.dumps(
                    {
                        "imports": imports,
                        "requests": _requests(group),
                        "searchPaths": paths,
                        "benchmarkModules": [
                            _module(rel)
                            for rel in sources_before
                            if rel.endswith(".lean")
                        ],
                        "certificateModules": [
                            _module(
                                Path(rel)
                                .relative_to(Path("certificates") / task)
                                .as_posix()
                            )
                            for rel in certificate_sources
                        ],
                        "reference": reference,
                    }
                ),
                encoding="utf-8",
            )
            # Compile only trusted code to a native executable, once per batch.
            # This avoids holding a frontend environment plus a second imported
            # environment and interpreting large dependency graphs.
            driver_env = dict(
                env,
                LEAN_PATH="",
                LEAN_SRC_PATH="",
            )
            driver_key = (
                hashlib.sha256(
                    auditor.replace("\r\n", "\n").encode("utf-8")
                ).hexdigest(),
                toolchain,
            )
            if native_driver.get("key") != driver_key:
                native_driver.clear()
                trusted = Path(tempfile.mkdtemp(prefix="vero-trusted-driver-"))
                (trusted / "lean-toolchain").write_text(
                    toolchain + "\n", encoding="utf-8"
                )
                (trusted / "Audit.lean").write_text(auditor, encoding="utf-8")
                _run(
                    ["lean", "-o", "Audit.olean", "-c", "Audit.c", "Audit.lean"],
                    trusted,
                    timeout,
                    driver_env,
                )
                executable = trusted / (
                    "audit-driver.exe" if os.name == "nt" else "audit-driver"
                )
                _run(
                    ["leanc", "-O3", "-o", str(executable), "Audit.c"],
                    trusted,
                    timeout,
                    driver_env,
                )
                native_driver.update(
                    executable=executable,
                    binary=executable.read_bytes(),
                    key=driver_key,
                )
            executable = native_driver["executable"]
            executable.write_bytes(native_driver["binary"])
            if os.name != "nt":
                executable.chmod(0o700)
            # Untrusted modules enter only at runtime via loadExts=false; their
            # initializers, macros, and persistent extensions cannot run.
            output = _run(
                [str(executable), str(request_file)],
                workspace,
                timeout,
                driver_env,
            )
            return json.loads(output)

        reference_assumptions = []
        try:
            reference_imports = sorted(
                {_module(e["spec_file"]) for e in entries}
                | {_module(e["harness_file"]) for e in entries}
            )
            for module in reference_imports:
                build(workspace / (module.replace(".", "/") + ".lean"))
            preserve_artifacts(built)
            kernel_replay()
            reference_assumptions = run_driver(reference_imports, entries, True)
        except (OSError, RuntimeError, subprocess.TimeoutExpired, ValueError) as exc:
            reference_assumptions = [{"kind": "audit_error", "error": str(exc)}]
            pending.clear()
        for result in results:
            result["reference_assumptions"] = reference_assumptions
        compiled_groups = []
        for relative, group in groups.items():
            try:
                local = Path(relative).relative_to(Path("certificates") / task)
                file = workspace / local
                restore_fixed_inputs()
                build(file)
                preserve_artifacts([file])
                compiled_groups.append((local, group))
            except (
                OSError,
                RuntimeError,
                subprocess.TimeoutExpired,
                ValueError,
            ) as exc:
                for entry in group:
                    entry.update(checked=False, error=str(exc))
                pending.clear()

        def audit_groups(selected_groups, index):
            restore_fixed_inputs()
            group = [entry for _, entries in selected_groups for entry in entries]
            imports = sorted(
                {_module(e["spec_file"]) for e in group}
                | {_module(e["harness_file"]) for e in group}
                | {_module(local.as_posix()) for local, _ in selected_groups}
            )
            for module in imports:
                build(workspace / (module.replace(".", "/") + ".lean"))
            kernel_replay(
                [workspace / (module.replace(".", "/") + ".lean") for module in imports]
            )
            return run_driver(imports, group, False)

        batches = []
        if compiled_groups:
            try:
                batches.append((compiled_groups, audit_groups(compiled_groups, 0)))
            except (
                OSError,
                RuntimeError,
                subprocess.TimeoutExpired,
                ValueError,
            ):
                # Independently valid files can define colliding helper names.
                # Replaying them separately preserves per-certificate evidence.
                for index, selected_group in enumerate(compiled_groups, 1):
                    try:
                        batches.append(
                            ([selected_group], audit_groups([selected_group], index))
                        )
                    except (
                        OSError,
                        RuntimeError,
                        subprocess.TimeoutExpired,
                        ValueError,
                    ) as exc:
                        for entry in selected_group[1]:
                            entry.update(checked=False, error=str(exc))
                        pending.clear()
        for selected_groups, output in batches:
            for _, group in selected_groups:
                for entry in group:
                    matches = [
                        result
                        for result in output
                        if result.get("declaration") == entry["declaration"]
                    ]
                    if len(matches) != 1:
                        entry.update(
                            checked=False,
                            error=f"missing or duplicate audit result: {entry['declaration']}",
                        )
                        continue
                    checked = matches[0].get("checked") is True
                    entry.update(
                        checked=checked,
                        error=matches[0].get("error"),
                        axioms=sorted(matches[0].get("axioms", [])),
                    )
        if workspace_parent is not None:
            for result in results:
                result["workspace"] = str(workspace)
    if frozen_sources(source) != sources_before or any(
        _safe(root, relative).read_bytes() != data
        for relative, data in certificate_sources.items()
    ):
        for result in results:
            result.update(
                checked=False,
                error="source drift during certification",
                reference_assumptions=[
                    {
                        "kind": "audit_error",
                        "error": "source drift during certification",
                    }
                ],
            )
    return results


def check_entries(
    root: Path, task: str, entries: list[dict], *, candidates: bool = False, **kwargs
) -> list[dict]:
    probes = list(entries)
    if candidates:
        for entry in entries:
            for candidate in entry.get("candidates", []):
                probes.append(
                    {
                        **entry,
                        **{
                            field: candidate[field]
                            for field in ("status", "declaration", "certificate_file")
                        },
                    }
                )
    checked = check_task(root, task, probes, **kwargs)
    results = []
    for entry in entries:
        attempts = [
            result for result in checked if entry_key(result) == entry_key(entry)
        ]
        successes = [result for result in attempts if result["checked"]]
        if len({result["status"] for result in successes}) > 1:
            results.append(
                dict(
                    entry,
                    checked=False,
                    axioms=[],
                    error="conflicting verified proof and refutation",
                    reference_assumptions=attempts[0].get("reference_assumptions", []),
                )
            )
        elif successes:
            results.append(successes[0])
        else:
            result = dict(attempts[0])
            errors = [r["error"] for r in attempts if r.get("error") != "unresolved"]
            result["error"] = (
                errors[0] if errors else "no independently verified certificate"
            )
            results.append(result)
    return results


def write_catalog(path: Path, catalog: dict) -> None:
    # Compact per-entry lines make the exhaustive inventory reviewable in Git.
    prefix = {key: value for key, value in catalog.items() if key != "entries"}
    text = json.dumps(prefix, ensure_ascii=False, indent=2)[:-2] + ',\n  "entries": [\n'
    text += ",\n".join(
        "    " + json.dumps(entry, ensure_ascii=False, separators=(",", ":"))
        for entry in catalog["entries"]
    )
    path.write_text(text + "\n  ]\n}\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument(
        "--catalog", type=Path, default=Path("certificates/catalog.json")
    )
    parser.add_argument(
        "--task", action="append", help="restrict reproduction to named benchmark(s)"
    )
    parser.add_argument(
        "--packages", type=Path, help="trusted Lake external dependency cache"
    )
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--output", type=Path, help="write the machine-readable result")
    parser.add_argument(
        "--certify-candidates",
        action="store_true",
        help="independently check unverified candidate leads stored in the catalog",
    )
    parser.add_argument(
        "--write-catalog",
        action="store_true",
        help="persist only independently checked statuses to the existing catalog",
    )
    parser.add_argument(
        "--refresh-source-hashes",
        action="store_true",
        help="freeze the current sources before checking, preserving the exact manifest target inventory",
    )
    parser.add_argument(
        "--progress", action="store_true", help="print per-task progress to stderr"
    )
    args = parser.parse_args(argv)
    identity = _checker_identity()
    try:
        root = args.root.resolve()
        catalog = _json(_safe(root, args.catalog.as_posix()))
        selected = set(args.task or catalog["tasks"])
        if not selected <= catalog["tasks"].keys():
            raise CatalogError(f"unknown tasks: {selected - catalog['tasks'].keys()}")
        if args.refresh_source_hashes:
            fresh = new_catalog(root)
            if {
                entry_key(e): (e["spec_file"], e["harness_file"])
                for e in fresh["entries"]
            } != {
                entry_key(e): (e["spec_file"], e["harness_file"])
                for e in catalog["entries"]
            } or {task: value["apis"] for task, value in fresh["tasks"].items()} != {
                task: value["apis"] for task, value in catalog["tasks"].items()
            }:
                raise CatalogError(
                    "cannot refresh a changed manifest target/API inventory"
                )
            fresh_certificates = certificate_sources(root)
            old_certificates = catalog.get("certificate_sources", {})
            for task in selected:
                changed = catalog["tasks"][task] != fresh["tasks"][task] or {
                    p: digest
                    for p, digest in old_certificates.items()
                    if Path(p).parts[1] == task
                } != {
                    p: digest
                    for p, digest in fresh_certificates.items()
                    if Path(p).parts[1] == task
                }
                if changed:
                    for entry in catalog["entries"]:
                        if entry["task"] == task and entry["status"] != "unresolved":
                            candidate = {
                                field: entry[field]
                                for field in (
                                    "status",
                                    "declaration",
                                    "certificate_file",
                                )
                            }
                            if candidate not in entry.setdefault("candidates", []):
                                entry["candidates"].append(candidate)
                            entry["status"] = "unresolved"
                            for field in ("declaration", "certificate_file", "axioms"):
                                entry.pop(field, None)
                            entry["reason"] = (
                                "source changed; independent revalidation required"
                            )
                catalog["tasks"][task] = fresh["tasks"][task]
            catalog["certificate_sources"] = (
                fresh_certificates
                if selected == catalog["tasks"].keys()
                else {
                    **{
                        path: digest
                        for path, digest in old_certificates.items()
                        if Path(path).parts[1] not in selected
                    },
                    **{
                        path: digest
                        for path, digest in fresh_certificates.items()
                        if Path(path).parts[1] in selected
                    },
                }
            )
        validate_catalog(root, catalog, selected=selected)
        results = []
        native_driver = {}
        for task in sorted(selected):
            task_results = check_entries(
                root,
                task,
                [e for e in catalog["entries"] if e["task"] == task],
                timeout=args.timeout,
                packages=args.packages,
                expected_sources=catalog["tasks"][task]["sources"],
                expected_certificate_sources={
                    path: digest
                    for path, digest in catalog["certificate_sources"].items()
                    if Path(path).parts[1] == task
                }
                if "certificate_sources" in catalog
                else None,
                workspace_parent=(
                    args.output.parent / (args.output.stem + ".workspaces")
                )
                if args.output
                else None,
                candidates=args.certify_candidates,
                native_driver=native_driver,
            )
            results.extend(task_results)
            if args.output:
                checkpoint = args.output.parent / (args.output.stem + ".tasks")
                checkpoint.mkdir(parents=True, exist_ok=True)
                (checkpoint / (task + ".json")).write_text(
                    json.dumps(
                        {
                            "task": task,
                            "source_hashes": catalog["tasks"][task]["sources"],
                            "certificate_sources": {
                                path: digest
                                for path, digest in catalog.get(
                                    "certificate_sources", {}
                                ).items()
                                if Path(path).parts[1] == task
                            },
                            **identity,
                            "entries": task_results,
                        },
                        ensure_ascii=False,
                        indent=2,
                    ),
                    encoding="utf-8",
                )
            if args.progress:
                proven = sum(
                    e["checked"] and e["status"] == "proven" for e in task_results
                )
                refuted = sum(
                    e["checked"] and e["status"] == "refuted" for e in task_results
                )
                print(
                    f"{task}: {proven} proven, {refuted} refuted, {len(task_results) - proven - refuted} unresolved",
                    file=sys.stderr,
                    flush=True,
                )
        validate_catalog(root, catalog, selected=selected)
        if _checker_identity() != identity:
            raise CatalogError("checker source drift during certification")
        for result in results:
            result["claimed_status"] = result["status"]
            if not result["checked"]:
                result["status"] = "unresolved"
        summary = {s: sum(e["status"] == s for e in results) for s in sorted(STATES)}
        reference_assumptions = {
            task: next(
                (
                    e.get("reference_assumptions", [{"kind": "not_checked"}])
                    for e in results
                    if e["task"] == task
                ),
                [{"kind": "not_checked"}],
            )
            for task in sorted(selected)
        }
        complete = (
            all(e["checked"] and e["status"] == "proven" for e in results)
            and not any(reference_assumptions.values())
            and selected == catalog["tasks"].keys()
        )
        payload = {
            "complete": complete,
            "summary": summary,
            "reference_assumptions": reference_assumptions,
            "entries": results,
            "verification": {
                **identity,
                "toolchains": sorted(
                    {
                        (root / "benchmarks" / task / "lean-toolchain")
                        .read_text(encoding="utf-8")
                        .strip()
                        for task in selected
                    }
                ),
                "method": "official leanchecker local-module replay; native trusted driver; loadExts=false; exact canonical type and recursive type/body audit",
                "native_driver_sha256": hashlib.sha256(
                    native_driver["binary"]
                ).hexdigest()
                if "binary" in native_driver
                else None,
            },
        }
        code = 0 if complete else 1
        if args.write_catalog:
            validate_catalog(root, catalog, selected=selected)
            by_key = {entry_key(result): result for result in results}
            for entry in catalog["entries"]:
                result = by_key.get(entry_key(entry))
                if result is None:
                    continue
                if result["checked"]:
                    for field in (
                        "status",
                        "declaration",
                        "certificate_file",
                        "axioms",
                    ):
                        entry[field] = result[field]
                    entry.pop("candidates", None)
                    entry.pop("reason", None)
                else:
                    if entry["status"] != "unresolved":
                        entry.setdefault("candidates", []).append(
                            {
                                field: entry[field]
                                for field in (
                                    "status",
                                    "declaration",
                                    "certificate_file",
                                )
                            }
                        )
                    entry["status"] = "unresolved"
                    for field in ("declaration", "certificate_file", "axioms"):
                        entry.pop(field, None)
                    entry["reason"] = _failure_reason(result.get("error"))
            previous = catalog.get("validation", {})
            same_checker = all(
                previous.get(key) == digest for key, digest in identity.items()
            )
            merged_references = (
                dict(previous.get("reference_assumptions", {})) if same_checker else {}
            )
            merged_references.update(
                {
                    task: [
                        {
                            **item,
                            **(
                                {"error": _failure_reason(item["error"])}
                                if item.get("kind") == "audit_error"
                                else {}
                            ),
                        }
                        for item in items
                    ]
                    for task, items in reference_assumptions.items()
                }
            )
            checked_tasks = (
                set(previous.get("tasks_checked", [])) if same_checker else set()
            )
            checked_tasks.update(selected)
            catalog["validation"] = {
                "complete": complete,
                "tasks_checked": sorted(checked_tasks),
                "summary": {
                    state: sum(entry["status"] == state for entry in catalog["entries"])
                    for state in sorted(STATES)
                },
                "reference_assumptions": merged_references,
                **payload["verification"],
            }
            validate_catalog(root, catalog, selected=selected)
            write_catalog(_safe(root, args.catalog.as_posix()), catalog)
    except (OSError, KeyError, TypeError, ValueError) as exc:
        payload, code = {"complete": False, "error": str(exc)}, 2
    serialized = json.dumps(payload, ensure_ascii=False, indent=2) + "\n"
    if args.output:
        args.output.write_text(serialized, encoding="utf-8")
    else:
        print(serialized, end="")
    return code
