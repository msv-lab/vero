"""Compile imported formal modules and independent Lean axiom-audit files."""

import os
import pathlib
import re
import subprocess
import sys

build_root = pathlib.Path(os.environ.get("AUDIT_BUILD_DIR", "/tmp/remaining-audit"))
source_root = pathlib.Path(os.environ.get("AUDIT_BENCHMARKS", "/repo/benchmarks"))
build_root.mkdir(exist_ok=True, parents=True)
os.chdir(build_root)
package_paths = [
    str(path)
    for path in pathlib.Path("/opt/vero-packages").glob("*/.lake/build/lib/lean")
]
os.environ["LEAN_PATH"] = ":".join([str(build_root), *package_paths])
compiled = set()


def compile_module(module):
    if module in compiled:
        return
    compiled.add(module)
    files = list(source_root.glob("*/" + module.replace(".", "/") + ".lean"))
    if not files:
        return
    source = files[0]
    target = build_root / (module.replace(".", "/") + ".lean")
    target.parent.mkdir(parents=True, exist_ok=True)
    text = source.read_text(encoding="utf-8")
    target.write_text(text, encoding="utf-8")
    for dependency in re.findall(r"^import\s+(\S+)", text, re.MULTILINE):
        compile_module(dependency)
    result = subprocess.run(
        [
            "lean",
            "-DautoImplicit=false",
            "-o",
            str(target.with_suffix(".olean")),
            str(target),
        ],
        check=False,
        text=True,
        capture_output=True,
    )
    print(result.stdout, end="", flush=True)
    print(result.stderr, end="", flush=True)
    if result.returncode:
        sys.exit(result.returncode)


for module in sys.argv[1].split(","):
    compile_module(module)
for check in sys.argv[2:]:
    result = subprocess.run(["lean", "-DautoImplicit=false", check], check=False)
    if result.returncode:
        sys.exit(result.returncode)
