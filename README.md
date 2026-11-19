# Generalized Confluence in Lean 4

This repository contains a Lean 4 formalization of generalized confluence for binary relations, together with results concerning functional graphs, iteration, periodicity, and finite uniform periods.

## Toolchain and dependency versions

- Lean: `leanprover/lean4:v4.36.0`
- Mathlib: `v4.36.0`

The Lean version is pinned in `lean-toolchain`. The Mathlib version is declared in `lakefile.lean`; `lake-manifest.json` pins Mathlib and its transitive dependencies to exact Git revisions.

## Build

Install Lean with [elan](https://github.com/leanprover/elan), then run from the repository root:

```bash
lake exe cache get
lake build
```

Do not run `lake update` for an ordinary build: it can change the dependency lockfile. When intentionally upgrading Lean or Mathlib, update the relevant version declaration, run `lake update`, review the resulting `lake-manifest.json`, and commit the updated lockfile.

The main formalization is in `GeneralizedConfluence.lean`, under the namespace `GeneralizedConfluence`.

## Verification status

On 19 November 2026, GitHub Actions completed `lake build` successfully with Lean 4.36.0 and Mathlib v4.36.0. The build log confirms that `GeneralizedConfluence` was compiled:

```text
✔ [18250/18252] Built GeneralizedConfluence (4.3s)
Build completed successfully (18252 jobs).
```

The run contained no Lean compiler warnings or errors. The workflow uses the committed dependency manifest and checks compilation on pushes and pull requests.

See the [successful warning-free build](https://github.com/zaferozdemir/generalized-confluence-lean4/actions/runs/44507673240).

## Scope

The development includes the generalized-confluence/frame-validity correspondence and formal results about function graphs and finite periodic behavior. The repository records the formalization; it does not by itself establish the novelty of the mathematical results.

## License

No license has been assigned yet. All rights are reserved by default unless a license is added.
