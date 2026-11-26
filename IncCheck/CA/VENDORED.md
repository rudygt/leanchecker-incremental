The files in this folder come from https://github.com/proofinity-it/CA at commit
62881ab0ffe6edee5dd96c55bd73b31e979c2cb7 (Apache-2.0, see LICENSE and NOTICE). Only `Base58`, `Canonical`, `SHA256`,
`Util` and `RefHash` are copied: `RefHash` needs nothing else.

Three changes. First, the module path. The files live under `IncCheck/CA/` and import each other as `IncCheck.CA.*`
instead of `CA.*`, so that a project which requires both this package and CA itself gets no clashing module names. The
Lean namespaces (`CA.RefHash` and so on) are unchanged.

Second and third, two changes make the ids follow what Lean's kernel actually reads, so that a stored verdict can never
apply to a declaration the kernel would treat differently (see `docs/soundness.md`):

- `canonicalizeLevel` no longer calls `Level.normalize`. The kernel compares some levels syntactically, and
  normalizing can erase an undeclared universe parameter that the kernel rejects.
- A definition's `decl` id includes its reducibility hints, which steer the kernel's lazy unfolding.

Both change ids, so the ids computed here differ from upstream CA's for definitions and for terms whose universe
levels are not already in normal form.
