The files in this folder come from https://github.com/proofinity-it/CA at commit
62881ab0ffe6edee5dd96c55bd73b31e979c2cb7 (Apache-2.0, see LICENSE and NOTICE). Only `Base58`, `Canonical`, `SHA256`,
`Util` and `RefHash` are copied: `RefHash` needs nothing else.

The only change is the module path. The files live under `IncCheck/CA/` and import each other as `IncCheck.CA.*`
instead of `CA.*`, so that a project which requires both this package and CA itself gets no clashing module names. The
Lean namespaces (`CA.RefHash` and so on) are unchanged.
