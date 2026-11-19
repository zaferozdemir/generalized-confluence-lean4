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

The source file was transferred from the project working copy without intentional mathematical edits. A successful Lean build has **not yet been independently confirmed**. The GitHub Actions workflow runs `lake build` on pushes and pull requests; its result will provide the first repository-side build check.

## Scope

The development includes the generalized-confluence/frame-validity correspondence and formal results about function graphs and finite periodic behavior. The repository records the formalization; it does not by itself establish the novelty of the mathematical results.

## License

No license has been assigned yet. All rights are reserved by default unless a license is added.
