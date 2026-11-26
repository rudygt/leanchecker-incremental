"""Build the Mathlib build tree of a master commit from Mathlib's cache, without compiling anything.

usage: mathlib_tree.py COMMIT

Set INCCHECK_PFR to a Lake project whose `.lake/packages/mathlib` holds the Mathlib build of `c47f9ad9` (in our runs,
the PFR project). That build is the base, and it is hard-linked into `test/work/tree-<commit>`. Modules whose Mathlib cache
key differs at COMMIT are extracted from the cache archives and moved into place by rename, so PFR's files are never
written. The commit must have the same toolchain, lakefile and dependency manifest as `c47f9ad9` (true for master from
2026-11-20 to 2026-11-26), so the dependencies' builds in PFR stay valid. Prints the LEAN_PATH to use.
"""

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WORK = ROOT / "test/work"
CLONE = WORK / "mathlib-src"
XDG = WORK / "xdg"
CACHE = XDG / "mathlib"
PFR = Path(os.environ["INCCHECK_PFR"])  # a Lake project whose `.lake/packages/mathlib` is the build of `c47f9ad9`
PFR_MATHLIB = PFR / ".lake/packages/mathlib"
PFR_LIB = PFR_MATHLIB / ".lake/build/lib/lean"
BASE = "c47f9ad906c5ec32a953f99911b446cd26dcc123"
DEPS = ["batteries", "aesop", "Qq", "plausible", "LeanSearchClient", "importGraph", "proofwidgets", "Cli"]
LEANTAR = Path.home() / ".elan/toolchains/leanprover--lean4---v4.37.0-rc1/bin/leantar"


def run(args: list, **kw) -> subprocess.CompletedProcess:
    return subprocess.run(["nice", "-n", "19", *map(str, args)], check=True, **kw)


def lean_path() -> str:
    p = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=PFR, capture_output=True, text=True, check=True)
    return p.stdout.strip()


def env() -> dict:
    return dict(os.environ, LEAN_PATH=lean_path(), XDG_CACHE_HOME=str(XDG),
                LEAN_SRC_PATH=":".join(["."] + [str(PFR / ".lake/packages" / d) for d in DEPS]))


def clone() -> None:
    if not CLONE.exists():
        run(["git", "clone", "-q", "--single-branch", "--branch", "master", "--shallow-since=2026-11-19",
             "https://github.com/leanprover-community/mathlib4.git", CLONE])


def keys(commit: str) -> dict[str, str]:
    out = WORK / f"keys-{commit[:8]}.txt"
    if not out.exists():
        run(["git", "-C", CLONE, "checkout", "-q", "--detach", commit])
        p = run(["lean", "--run", ROOT / "test/DumpKeys.lean"], cwd=CLONE, env=env(), capture_output=True, text=True)
        out.write_text(p.stdout)
    return dict(line.split() for line in out.read_text().splitlines())


def fetch(commit: str, wanted: list[str]) -> None:
    CACHE.mkdir(parents=True, exist_ok=True)
    if not any(CACHE.iterdir()):
        run(["cp", "-al", f"{Path.home()}/.cache/mathlib/.", CACHE])
    if all((CACHE / f).exists() for f in wanted):
        return
    run(["git", "-C", CLONE, "checkout", "-q", "--detach", commit])
    run([PFR_MATHLIB / ".lake/build/bin/cache", "get-"], cwd=CLONE, env=env(), capture_output=True)
    missing = [f for f in wanted if not (CACHE / f).exists()]
    if missing:
        raise SystemExit(f"{len(missing)} archives are not in Mathlib's cache, for example {missing[0]}")


def build_tree(commit: str) -> Path:
    tree = WORK / f"tree-{commit[:8]}"
    base, target = keys(BASE), keys(commit)
    changed = [m for m in target if m.startswith("Mathlib") and base.get(m) != target[m]]
    removed = [m for m in base if m.startswith("Mathlib") and m not in target]
    if not tree.exists():
        fetch(commit, [target[m] for m in changed])
        run(["cp", "-al", PFR_LIB, tree])
        for start in range(0, len(changed), 500):
            batch = changed[start:start + 500]
            with tempfile.TemporaryDirectory(dir=WORK) as td:
                spec = json.dumps([{"file": str(CACHE / target[m]), "base": f"{td}/{m}"} for m in batch])
                run([LEANTAR, "-x", "-j", "-"], input=spec, text=True)
                for m in batch:
                    lib = Path(td, m, ".lake/build/lib/lean")
                    for f in lib.rglob("*"):
                        if f.is_file():
                            dest = tree / f.relative_to(lib)
                            dest.parent.mkdir(parents=True, exist_ok=True)
                            os.replace(f, dest)
        for m in removed:
            for f in tree.glob(str(Path(*m.split("."))) + ".*"):
                f.unlink()
    print(f"{commit[:8]}: {len(changed)} modules replaced, {len(removed)} removed", file=sys.stderr)
    return tree


def main() -> None:
    commit = sys.argv[1]
    WORK.mkdir(parents=True, exist_ok=True)
    clone()
    tree = build_tree(commit)
    deps = [p for p in lean_path().split(":") if not any(s in p for s in ("/packages/mathlib/", "/pfr/.lake/build",
                                                                         "AddCombi", "checkdecls"))]
    print(":".join([str(tree), *deps]))


if __name__ == "__main__":
    main()
