"""Run leanchecker-inc on forged .olean files and a poisoned verdict store.

Run from anywhere: `python3 test/attacks.py`. For each forged module, it records what leanchecker-inc and the
toolchain's own `leanchecker --fresh` do, and fails if leanchecker-inc accepts one.
"""

import os
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WORK = ROOT / "test/work/attacks"
FORGED = WORK / "forged"


def toolchain() -> Path:
    p = subprocess.run(["lake", "env", "printenv", "LEAN_SYSROOT"], cwd=ROOT, capture_output=True, text=True,
                       check=True)
    return Path(p.stdout.strip())


SYSROOT = toolchain()
ENV = dict(os.environ, LEAN_PATH=str(FORGED), LEAN_SYSROOT=str(SYSROOT),
           PATH=f"{SYSROOT / 'bin'}:{os.environ['PATH']}")
BIN = ROOT / ".lake/build/bin/leanchecker-inc"


def run(args: list) -> subprocess.CompletedProcess:
    return subprocess.run(["nice", "-n", "19", *map(str, args)], cwd=WORK, env=ENV, capture_output=True, text=True)


def ours(module: str, *extra: str) -> subprocess.CompletedProcess:
    return run([BIN, "--no-id-cache", "-q", *extra, module])


def main() -> None:
    shutil.rmtree(WORK, ignore_errors=True)
    WORK.mkdir(parents=True)
    subprocess.run(["nice", "-n", "19", "lake", "build", "leanchecker-inc", "inc-forge"], cwd=ROOT, check=True,
                   capture_output=True)
    subprocess.run([ROOT / ".lake/build/bin/inc-forge", FORGED], check=True)

    failures = 0
    print(f"{'module':<22} {'leanchecker-inc':<18} {'leanchecker --fresh':<20} reason")
    for module in ["ForgedNameMismatch", "ForgedInductive", "ForgedFalse"]:
        p = ours(module, "--no-store")
        fresh = run([SYSROOT / "bin/leanchecker", "--fresh", module])
        verdict = lambda c: "accept" if c.returncode == 0 else f"reject (exit {c.returncode})"
        reason = (p.stderr.strip().splitlines() or [""])[-1][:70]
        print(f"{module:<22} {verdict(p):<18} {verdict(fresh):<20} {reason}")
        if p.returncode != 1:
            failures += 1

    # A store is trusted. Planting the key of the false theorem in it makes the check accept, which is why the
    # store must be protected; with --no-store the false theorem is rejected again.
    keys = WORK / "keys.txt"
    run([BIN, "--no-id-cache", "-q", "--hash-only", "--dump-keys", keys, "ForgedFalse"])
    key = next(line.split()[1] for line in keys.read_text().splitlines() if line.startswith("forgedFalse "))
    store = WORK / "poisoned.bin"
    store.write_bytes(bytes.fromhex(key))
    poisoned = ours("ForgedFalse", "--store", str(store), "--no-record")
    clean = ours("ForgedFalse", "--no-store")
    print(f"poisoned store: {'accepts' if poisoned.returncode == 0 else 'rejects'} the false theorem; "
          f"--no-store: {'accepts' if clean.returncode == 0 else 'rejects'} it")
    if poisoned.returncode != 0 or clean.returncode != 1:
        failures += 1

    # Constants that differ only in their names: `bad : a = b` is a copy of `good : a = a`, for two axioms `a b : Nat`,
    # and `f : A → B` is a copy of `g : A → A`, for two inductive types with the same structure. Key scheme 2 left names
    # out of the ids, so both reused the verdicts of `good` and `g` and were accepted.
    toy = ROOT / "test/toy"
    lake = lambda *a: subprocess.run(["nice", "-n", "19", "lake", *a], cwd=toy, capture_output=True, text=True)
    built = lake("build", "Collide.Good", "Collide.BadAxiom", "Collide.BadInductive")
    if built.returncode != 0:
        raise SystemExit(built.stdout + built.stderr)
    store = WORK / "collide.bin"
    good = lake("exe", "leanchecker-inc", "-q", "--no-id-cache", "--store", str(store), "Collide.Good")
    if good.returncode != 0:
        failures += 1
    for module in ["Collide.BadAxiom", "Collide.BadInductive"]:
        bad = lake("exe", "leanchecker-inc", "-q", "--no-id-cache", "--store", str(store), "--no-record", module)
        print(f"{module:<22} with the verdicts of Collide.Good: "
              f"{'accepted' if bad.returncode == 0 else 'rejected'}")
        if bad.returncode != 1:
            failures += 1

    print("all attack tests behave as documented" if failures == 0 else f"{failures} failures")
    raise SystemExit(1 if failures else 0)


if __name__ == "__main__":
    main()
