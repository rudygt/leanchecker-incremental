"""Edit the toy project, rebuild it, and check which declarations `leanchecker-inc` sends to the kernel.

Run from anywhere: `python3 test/scenarios.py [--id-cache]`. With `--id-cache` every check also reuses CA ids through
`--id-cache`, so the scenarios cover the cached path. Every build and check runs under `nice -n 19`.
"""

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TOY = ROOT / "test/toy"
WORK = ROOT / "test/work"
STORE = WORK / "scenarios.store"
LOG = WORK / "checked.txt"
IDS = WORK / "scenarios.ids"
USE_ID_CACHE = "--id-cache" in sys.argv
A, B, BAD = TOY / "Toy/A.lean", TOY / "Toy/B.lean", TOY / "Bad.lean"

BAD_SOURCE = """import Toy
import Lean
open Lean Elab Command

-- `1 = 2` with `Eq.refl 1` as its proof, added without a kernel check.
set_option debug.skipKernelTC true in
run_cmd liftTermElabM do
  let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 2)
  let val := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1)
  addDecl (.thmDecl { name := `bad, levelParams := [], type := ty, value := val })
"""


def sh(args: list[str], **kw) -> subprocess.CompletedProcess:
    return subprocess.run(["nice", "-n", "19", *args], cwd=TOY, capture_output=True, text=True, **kw)


def build(target: str = "Toy") -> None:
    p = sh(["lake", "build", target])
    assert p.returncode == 0, p.stdout + p.stderr


def check(module: str = "Toy", record: bool = True) -> tuple[int, set[str], str]:
    args = ["lake", "exe", "leanchecker-inc", "--store", str(STORE), "--log-checked", str(LOG), module]
    if not record:
        args.insert(-1, "--no-record")
    args[-1:-1] = ["--id-cache", str(IDS)] if USE_ID_CACHE else ["--no-id-cache"]
    LOG.unlink(missing_ok=True)
    p = sh(args)
    names = {line for line in LOG.read_text().splitlines() if line and not line.startswith("inductive ")} \
        if LOG.exists() else set()
    return p.returncode, names, (p.stdout + p.stderr).strip()


def reset() -> None:
    A.write_text((TOY / "A.base").read_text())
    B.write_text((TOY / "B.base").read_text())
    BAD.unlink(missing_ok=True)


def edit(path: Path, old: str, new: str) -> None:
    text = path.read_text()
    assert old in text, old
    path.write_text(text.replace(old, new))


def scenario(title: str) -> None:
    print(f"\n== {title}", flush=True)


def main() -> None:
    WORK.mkdir(parents=True, exist_ok=True)
    STORE.unlink(missing_ok=True)
    IDS.unlink(missing_ok=True)
    reset()
    build()

    scenario("empty store: the kernel checks everything")
    code, names, out = check()
    print(out.splitlines()[0])
    assert code == 0 and len(names) > 60000, out

    scenario("same build again: nothing is re-checked, inductive blocks included")
    code, names, out = check()
    assert code == 0 and names == set(), (names, out)
    assert "and 0 inductive blocks" in out, out
    print("checked: none")

    scenario("proof edit that elaborates to the same term up to binder names: nothing is re-checked")
    edit(A, "unfold double; omega", "show n + n = 2 * n; omega")
    build()
    code, names, out = check()
    print("checked:", sorted(names))
    assert code == 0 and names == set(), (names, out)

    scenario("proof of double_eq changed: only double_eq is re-checked, not the theorems that use it")
    edit(A, "show n + n = 2 * n; omega", "unfold double; exact (Nat.two_mul n).symm")
    build()
    code, names, out = check()
    print("checked:", sorted(names))
    assert code == 0 and names == {"double_eq"}, (names, out)

    scenario("body of double changed: its dependents are re-checked, Color is not")
    edit(A, "unfold double; exact (Nat.two_mul n).symm", "unfold double; omega")
    edit(A, "def double (n : Nat) : Nat := n + n", "def double (n : Nat) : Nat := 2 * n")
    build()
    code, names, out = check()
    print("checked:", sorted(names))
    must = {"double", "double_eq", "Box.twice", "twice_val", "quadruple", "quadruple_eq"}
    assert code == 0 and must <= names, (must - names, out)
    assert not any("olor" in n for n in names), names

    scenario("a false theorem added without a kernel check is rejected, and nothing is recorded")
    BAD.write_text(BAD_SOURCE)
    build("Bad")
    before = STORE.stat().st_size
    code, names, out = check("Bad")
    print(out.splitlines()[-1] if out else "")
    assert code == 1 and "bad" in out, out
    assert STORE.stat().st_size == before, "a failed run must not append to the store"
    fresh = sh(["lake", "env", "leanchecker", "--fresh", "Bad"])
    assert fresh.returncode != 0, "official leanchecker --fresh should reject Bad too"

    reset()
    build()
    print("\nall scenarios passed")


if __name__ == "__main__":
    try:
        main()
    finally:
        reset()
        sys.stdout.flush()
