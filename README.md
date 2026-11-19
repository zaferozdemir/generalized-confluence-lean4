# Generalized Confluence in Lean 4

This repository contains a Lean 4 formalization of generalized confluence for binary relations, together with results concerning functional graphs, iteration, periodicity, and finite uniform periods.

## Toolchain

- Lean: `leanprover/lean4:v4.36.0`
- Mathlib: `v4.36.0`

The versions are pinned in `lean-toolchain` and `lakefile.lean`.

## Build

Install Lean using [elan](https://github.com/leanprover/elan), then run:

```bash
lake update
lake exe cache get
lake build
```

The main formalization is in `GeneralizedConfluence.lean`, under the namespace `GeneralizedConfluence`.

## Verification status

On 19 November 2026, GitHub Actions completed `lake build` successfully with Lean 4.36.0 and Mathlib v4.36.0. The build log confirms that `GeneralizedConfluence` was compiled and reports:

```text
✔ [18250/18252] Built GeneralizedConfluence (4.3s)
Build completed successfully (18252 jobs).
```

The run contained no Lean compiler warnings or errors. The workflow verifies compilation; project test and lint targets are not currently configured.

See the [successful GitHub Actions run](https://github.com/zaferozdemir/generalized-confluence-lean4/actions/runs/44507673240).

## Scope

The development includes the generalized-confluence/frame-validity correspondence and formal results about function graphs and finite periodic behavior. The repository records the formalization; it does not by itself establish the novelty of the mathematical results.

## License

No license has been assigned yet. All rights are reserved by default unless a license is added.
