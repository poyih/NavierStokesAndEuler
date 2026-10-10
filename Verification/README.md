# Independent verification of the Navier–Stokes formalization

This directory records an independent check of the Navier–Stokes part of this
repository, carried out with Lean 4 in a fresh, isolated cloud container on
2026-10-10. Only the `NavierStokes` library and its Comparator challenge were
checked; the `Euler` library was not part of this run.

## Environment

| Component | Version |
| --- | --- |
| Repository commit checked | `f9e8bc5b38b6e212696e8a30e3e91517af887bbd` (`main`) |
| Lean | 4.34.0-rc2, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`, release tarball from GitHub |
| Mathlib | `85e3a25e006c35636f0e53b0e9296caca2685bc0` (tag `v4.34.0-rc2`), built from source |
| Comparator | `19e111e2141cf333c7daff0f64c5f24acc91dd2e` (tag `v4.34.0-rc2`) |
| lean4export | `cacf989bd75f608700820f6afc595f32e7a99a4d` |
| nanoda_lib | `3a2407216ee84a75f9e1aead6803d0578be06ae7`, `cargo build --release` |
| landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (0.1.18), `go build`, Landlock active on Linux 6.18 |
| Machine | 4 vCPU, 15 GB RAM |

The Mathlib olean cache (`lakecache.blob.core.windows.net`) was not reachable
from the container, so every one of the 8381 Mathlib modules was compiled from
source by this Lean toolchain rather than downloaded. The toolchain itself was
downloaded from the `leanprover/lean4` GitHub release because
`release.lean-lang.org` was not reachable either.

## Summary of results

| # | Check | Result |
| --- | --- | --- |
| 1 | Source audit for escape hatches | No `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `partial`, `implemented_by`, `extern`, `native_decide`, or `set_option` in any NavierStokes source |
| 2 | Challenge statement provenance | `ComparatorChallenges/NavierStokes.lean` matches Formal Conjectures at `8bf45ed7` up to metadata; definitions and theorems (C), (D) byte-identical |
| 3 | Full build | `lake build NavierStokes ComparatorChallenges`: 9583 jobs, 0 errors; the only 4 warnings are the intentional `sorry` placeholders in the two challenge files |
| 4 | Axiom audit | Both main theorems depend only on `propext`, `Classical.choice`, `Quot.sound` |
| 5 | Independent restatement | `Verification/NavierStokesIndependentCheck.lean` compiles; restated (C) and (D) proved from the submission with the same three axioms |
| 6 | `leanchecker` kernel replay of all 817 NavierStokes modules | PENDING |
| 7 | Comparator (landrun + lean4export + nanoda + Lean kernel) | PENDING |

## Details

### 1. Source audit

All 816 files under `NavierStokes/` (707 top-level, 109 under `R3/`), 429,279
lines in total, plus `NavierStokes.lean`, were searched for the standard ways of
weakening a Lean development:

```
sorry  admit  axiom  unsafe  opaque  partial  implemented_by  extern
native_decide  ofReduceBool  csimp  set_option  macro  elab  syntax  initialize
```

None occur (the words `prefix` and `notation` appear only in doc comments and
as `local notation`). The only `attribute` commands are four
`attribute [local instance] Classical.propDecidable`. The only imports are
`Mathlib.*` and `NavierStokes.*`; nothing imports `ComparatorChallenges` or
`Euler`.

### 2. Challenge statement provenance

`ComparatorChallenges/NavierStokes.lean` was diffed against
`FormalConjectures/Millenium/NavierStokes.lean` at the commit it cites,
`8bf45ed70d48b2b2a501de9c00b26bfa38c573ee`. The differences are:

- `import FormalConjecturesUtil` replaced by `import Mathlib`;
- namespace `NavierStokes` renamed to `NavierStokes.Comparator`;
- the `ℝ^n` and `ℝ³` notations inlined as `EuclideanSpace ℝ (Fin n)` and
  `EuclideanSpace ℝ (Fin 3)`, which is exactly how
  `FormalConjecturesForMathlib/Geometry/Euclidean.lean` and `3d.lean` define
  them at that commit;
- `@[category …, AMS 35]` attributes removed and `notation` made `local`;
- the existence alternatives (A) and (B) removed; the breakdown alternatives
  (C) and (D) are retained verbatim with their `sorry` placeholders.

Every structure and definition is byte-identical. Separately,
`NavierStokes/ComparatorDefinitions.lean`, the copy of the definitions that the
proof imports, is byte-identical to the challenge file from `open ContDiff …`
onward except that the two theorems are absent.

### 3. Build

```
lake build NavierStokes ComparatorChallenges
…
✔ [9582/9583] Built NavierStokes (5.5s)
Build completed successfully (9583 jobs).
```

The build ran in three incremental segments because of a two-hour limit on
background tasks in the session; Lake's trace files guarantee that every module
was compiled exactly once against up-to-date dependencies. The four warnings in
the log are:

```
ComparatorChallenges/NavierStokes.lean:273:8: declaration uses `sorry`
ComparatorChallenges/NavierStokes.lean:280:8: declaration uses `sorry`
ComparatorChallenges/Euler.lean:85:8: declaration uses `sorry`
ComparatorChallenges/Euler.lean:170:8: declaration uses `sorry`
```

These are the intentional placeholders in the challenge files. No module of the
`NavierStokes` library produced a warning or an error.

### 4. Axiom audit

`NavierStokes/ComparatorSolution.lean` ends with two `#print axioms` commands;
the build log records:

```
'NavierStokes.Comparator.navier_stokes_breakdown_R3' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes.Comparator.navier_stokes_breakdown_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

In particular `sorryAx` does not appear, and no project-specific axiom exists.

### 5. Independent restatement

`Verification/NavierStokesIndependentCheck.lean` imports only the submission
root `NavierStokes.ComparatorSolution`, never the challenge module. It restates
every challenge definition in a fresh namespace `NavierStokes.IndependentCheck`
and proves (C) and (D) as stated with those restated definitions, using the
submission's theorems. The proofs consist solely of unpacking and repacking
structure fields, so they can only succeed if each restated structure has
exactly the fields, with exactly the types, of the submission's structure.
Running it:

```
lake env lean Verification/NavierStokesIndependentCheck.lean
'NavierStokes.Comparator.navier_stokes_breakdown_R3' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes.Comparator.navier_stokes_breakdown_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes.IndependentCheck.navier_stokes_breakdown_R3' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes.IndependentCheck.navier_stokes_breakdown_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The restated definitions were additionally compiled on their own against plain
`import Mathlib` to confirm they do not depend on anything from the project.

### 6. leanchecker kernel replay

PENDING

### 7. Comparator

PENDING

## What this does and does not establish

- The two Lean theorems `NavierStokes.Comparator.navier_stokes_breakdown_R3`
  and `navier_stokes_breakdown_periodic` are accepted by the Lean 4.34.0-rc2
  kernel, with no axioms beyond the three standard ones, and their statements
  are exactly the Formal Conjectures encodings of the Clay alternatives (C)
  and (D), with viscosity `nu > 0` universally quantified.
- Whether that encoding faithfully captures the informal Clay problem statement
  is a mathematical-modelling question that no proof checker can settle. The
  encoding is the one maintained by the Formal Conjectures project; this check
  only confirms that the proof targets it unchanged.
- Trust base: the Lean kernel (and, for the Comparator run, nanoda as a second
  kernel), the Lean compiler and Lake used to build Mathlib and the project, the
  operating system, and the hardware. Comparator's README also assumes the
  solution has not been compiled before Comparator runs it; in this session the
  solution was built first by the same toolchain in the same fresh container.
  This matters only for an adversarial solution that tampers with the checking
  environment at compile time; the statement comparison and both kernel replays
  operate on lean4export output of the already-built oleans, which such
  tampering could not alter after the fact without also defeating the
  independent build of Mathlib from the pinned git revision.

## Reproducing

With `elan` installed (or the Lean 4.34.0-rc2 release tarball on `PATH`),
from the repository root:

```sh
lake exe cache get                      # or build Mathlib from source
lake build NavierStokes ComparatorChallenges
lake env lean Verification/NavierStokesIndependentCheck.lean
lake env leanchecker NavierStokes.ComparatorSolution   # or every NavierStokes.* module
COMPARATOR_LANDRUN=… COMPARATOR_LEAN4EXPORT=… COMPARATOR_NANODA=… \
  lake exe comparator ComparatorChallenges/NavierStokes.json
```
