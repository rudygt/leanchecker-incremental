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

    # Two runs: record the verdicts of a module that both checkers accept, then check a module that
    # `leanchecker --fresh` rejects against them. Each pair is a shape that once made leanchecker-inc accept.
    pairs = [
        # An inductive type stored without the recursor the kernel generates for it, then the same type with an axiom
        # named like that recursor. Skipping the block left the name free, so the axiom was accepted.
        ("ForgedBlockNoRec", "ForgedBlockRecAxiom"),
        # A nested inductive type, then an axiom named like an auxiliary type the kernel makes while checking it.
        ("N1", "N2"),
    ]
    for good, bad in pairs:
        store = WORK / f"{good}.bin"
        recorded = ours(good, "--store", str(store))
        fresh = run([SYSROOT / "bin/leanchecker", "--fresh", bad])
        attacked = ours(bad, "--store", str(store), "--no-record")
        reason = (attacked.stderr.strip().splitlines() or [""])[-1][:60]
        print(f"{bad:<22} with the verdicts of {good}: {'accepted' if attacked.returncode == 0 else 'rejected'}; "
              f"leanchecker --fresh: {'accepts' if fresh.returncode == 0 else 'rejects'} ({reason})")
        if recorded.returncode != 0 or fresh.returncode == 0 or attacked.returncode != 1:
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

    # Version 1 of a module set, then version 2, with the verdicts and the id cache of version 1. In the first two, a
    # module that stayed byte-identical shares its cached ids with a changed one. In the third, the change is one the
    # keys left out. All three shapes once made leanchecker-inc accept.
    for title, modules in [
        ("CacheX.0 : False, a name the id cache stored truncated", ["CacheTop"]),
        ("dupThm proved by Nat.zero, a copy of a theorem another module declares", ["DupA", "DupB"]),
        ("MdT.mk with its type in mdata, which the kernel rejects and the keys once ignored", ["MdBlock"]),
        ("g = true through a stored unsafe recursor the kernel never compared", ["URec"]),
        ("a theorem that needs Char.ofNat, which was present but unhashable and is now gone", ["P"]),
    ]:
        store, ids = WORK / f"{modules[0]}.bin", WORK / f"{modules[0]}.ids"
        env1, env2 = dict(ENV, LEAN_PATH=str(FORGED / "v1")), dict(ENV, LEAN_PATH=str(FORGED / "v2"))
        cached = ["--store", str(store), "--id-cache", str(ids)]
        recorded = subprocess.run([BIN, "-q", *cached, *modules], cwd=WORK, env=env1, capture_output=True, text=True)
        fresh = subprocess.run([SYSROOT / "bin/leanchecker", "--fresh", *modules], cwd=WORK, env=env2,
                               capture_output=True, text=True)
        attacked = subprocess.run([BIN, "-q", *cached, "--no-record", *modules], cwd=WORK, env=env2,
                                  capture_output=True, text=True)
        print(f"{title}: {'accepted' if attacked.returncode == 0 else 'rejected'}; "
              f"leanchecker --fresh: {'accepts' if fresh.returncode == 0 else 'rejects'}")
        if recorded.returncode != 0 or fresh.returncode == 0 or attacked.returncode != 1:
            failures += 1

    # Two runs record `t1 : False` from an axiom and `t2` from `t1`, and the same the other way round. The third proves
    # them from each other with no axiom. Each verdict is valid alone; together they form a cycle that `--fresh` rejects.
    store = WORK / "circ.bin"
    envs = {v: dict(ENV, LEAN_PATH=str(FORGED / v)) for v in ["c1", "c2", "c3"]}
    recorded = [subprocess.run([BIN, "-q", "--no-id-cache", "--store", str(store), "Circ"], cwd=WORK, env=envs[v],
                               capture_output=True, text=True) for v in ["c1", "c2"]]
    fresh = subprocess.run([SYSROOT / "bin/leanchecker", "--fresh", "Circ"], cwd=WORK, env=envs["c3"],
                           capture_output=True, text=True)
    attacked = subprocess.run([BIN, "-q", "--no-id-cache", "--store", str(store), "--no-record", "Circ"], cwd=WORK,
                              env=envs["c3"], capture_output=True, text=True)
    print(f"t1 := t2 and t2 := t1 with the verdicts of two acyclic runs: "
          f"{'accepted' if attacked.returncode == 0 else 'rejected'}; "
          f"leanchecker --fresh: {'accepts' if fresh.returncode == 0 else 'rejects'}")
    if any(r.returncode != 0 for r in recorded) or fresh.returncode == 0 or attacked.returncode != 1:
        failures += 1

    # The same cycle split across two modules and two shards. Each shard assumes the other's keys, so without the cycle
    # check each accepted its half and the merged stores skipped both.
    stores = [WORK / f"shard{i}.bin" for i in range(2)]
    shards = [ours("ShardA", "ShardB", "--store", str(stores[i]), "--shard", f"{i}/2") for i in range(2)]
    merged = WORK / "shards.bin"
    merged.write_bytes(b"".join(p.read_bytes() for p in stores if p.exists()))
    attacked = ours("ShardA", "ShardB", "--store", str(merged), "--no-record")
    print(f"the cycle split across two shards: shards {'accept' if all(r.returncode == 0 for r in shards) else 'reject'}, "
          f"the merged run {'accepts' if attacked.returncode == 0 else 'rejects'}")
    if any(r.returncode != 1 for r in shards) or attacked.returncode != 1:
        failures += 1

    # `2^200 = 2^200` by literals, recorded with the default `LEAN_NAT_MAX_SIZE`, then checked with a limit of 8 bytes,
    # under which the kernel rejects the literals.
    store = WORK / "biglit.bin"
    recorded = ours("BigLit", "--store", str(store))
    small = dict(ENV, LEAN_NAT_MAX_SIZE="8")
    fresh = subprocess.run([SYSROOT / "bin/leanchecker", "--fresh", "BigLit"], cwd=WORK, env=small,
                           capture_output=True, text=True)
    attacked = subprocess.run([BIN, "-q", "--no-id-cache", "--store", str(store), "--no-record", "BigLit"], cwd=WORK,
                              env=small, capture_output=True, text=True)
    print(f"2^200 = 2^200 under LEAN_NAT_MAX_SIZE=8 with a verdict from the default limit: "
          f"{'accepted' if attacked.returncode == 0 else 'rejected'}; "
          f"leanchecker --fresh: {'accepts' if fresh.returncode == 0 else 'rejects'}")
    if recorded.returncode != 0 or fresh.returncode == 0 or attacked.returncode != 1:
        failures += 1

    # A check that reads a theorem's proof: `liftQ thm = true` holds by `Eq.refl` only while `thm`, a proof of a
    # quotient in `Prop`, reduces to `Quot.mk`. Changing only that proof and rebuilding only its module must not reuse
    # the verdict of the user, whose key leaves the proof out.
    lib = toy / "QuotProof/Lib.lean"
    source = ("def R : True → True → Prop := fun _ _ => True\n"
              "axiom qax : @Quot True R\n"
              "theorem thm : @Quot True R := {proof}\n"
              "def liftQ (q : @Quot True R) : Bool := @Quot.lift True R Bool (fun _ => true) (fun _ _ _ => rfl) q\n")
    lib.write_text(source.format(proof="Quot.mk R True.intro"))
    try:
        built = lake("build", "QuotProof.Use")
        if built.returncode != 0:
            raise SystemExit(built.stdout + built.stderr)
        store = WORK / "quot.bin"
        recorded = lake("exe", "leanchecker-inc", "-q", "--no-id-cache", "--store", str(store), "QuotProof.Use")
        lib.write_text(source.format(proof="qax"))
        rebuilt = lake("build", "QuotProof.Lib")
        if rebuilt.returncode != 0:
            raise SystemExit(rebuilt.stdout + rebuilt.stderr)
        attacked = lake("exe", "leanchecker-inc", "-q", "--no-id-cache", "--store", str(store), "--no-record",
                        "QuotProof.Use")
        fresh = lake("exe", "leanchecker-inc", "-q", "--no-store", "QuotProof.Use")
        print(f"liftQ thm = true after thm's proof changed: {'accepted' if attacked.returncode == 0 else 'rejected'}; "
              f"--no-store: {'accepts' if fresh.returncode == 0 else 'rejects'}")
        if recorded.returncode != 0 or fresh.returncode != 1 or attacked.returncode != 1:
            failures += 1
    finally:
        lib.unlink(missing_ok=True)

    print("all attack tests behave as documented" if failures == 0 else f"{failures} failures")
    raise SystemExit(1 if failures else 0)


if __name__ == "__main__":
    main()
