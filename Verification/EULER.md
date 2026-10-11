# Independent verification of the Euler formalization

This file records an independent check of the Euler part of this repository,
carried out with the same method, toolchain, and container as the Navier–Stokes
check in [README.md](README.md), on 2026-10-11. The environment table there
applies unchanged (Lean 4.34.0-rc2, Mathlib `85e3a25e` built from source,
Comparator `19e111e2`, lean4export `cacf989b`, nanoda_lib `3a240721`,
landrun 0.1.18, 4 vCPU, 15 GB RAM).

## Summary of results

| # | Check | Result |
| --- | --- | --- |
| 1 | Source audit for escape hatches | No `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `partial`, `implemented_by`, `extern`, `native_decide`, `set_option`, or metaprogramming in any of the 1839 Euler sources |
| 2 | Challenge statement provenance | First theorem's definitions are the Formal Conjectures Navier–Stokes definitions specialized to `n = 3`, `nu = 0`, `f = 0`; second theorem's definitions are project-specific and were reviewed by hand (below); `Euler/SolutionDefinitions.lean` is identical to the challenge minus the two theorems |
| 3 | Full build | `lake build Euler ComparatorChallenges`: 10606 jobs, 0 errors; the only 4 warnings are the intentional `sorry` placeholders in the two challenge files; the `Euler` library itself compiles with `warningAsError` |
| 4 | Axiom audit | Both `Euler.euler_breakdown_R3` and `Euler.exists_compact_smooth_euler_singularity` depend only on `propext`, `Classical.choice`, `Quot.sound` |
| 5 | Independent restatement | `Verification/EulerIndependentCheck.lean` compiles; both restated theorems proved from the submission with the same three axioms |
| 6 | `leanchecker` kernel replay | PENDING |
| 7 | Comparator (landrun + lean4export + nanoda + Lean kernel) | `Your solution is okay!`: statements match the challenge, axioms permitted, nanoda and the Lean kernel both accept the solution replayed from an empty environment |

## Details

### 1. Source audit

All 1839 files under `Euler/` (211,578 lines) plus `Euler.lean` were searched
for the same patterns as in the Navier–Stokes audit:

```
sorry  admit  axiom  unsafe  opaque  partial  implemented_by  extern
native_decide  ofReduceBool  csimp  set_option  macro  elab  syntax  initialize
```

None occur. The only `attribute` commands are local ones:
`attribute [local instance] …` (for `CompletePartialOrder.toSupSet` and a
compact-interval instance), `attribute [local irreducible] …`, and
`attribute [local gcongr] …`. None of these can affect what the kernel accepts.
The only imports are `Mathlib.*` and `Euler.*`; nothing imports
`ComparatorChallenges` or `NavierStokes`. The Lake configuration compiles the
library with `autoImplicit = false` and `warningAsError = true`, so any
warning would have failed the build.

### 2. Challenge statement provenance and review

`ComparatorChallenges/Euler.lean` is not a verbatim copy of an upstream file; it
is adapted from the Formal Conjectures Navier–Stokes statement. It was compared
by hand with `FormalConjectures/Millenium/NavierStokes.lean` at commit
`8bf45ed70d48b2b2a501de9c00b26bfa38c573ee`.

**First theorem, `euler_breakdown_R3`.** Its definitions are the upstream ones
specialized to dimension 3, viscosity 0, and force 0:

- `divergence`, `InitialVelocityCondition`, `InitialVelocityConditionDecay`:
  the upstream definitions with `ℝ^n` replaced by `EuclideanSpace ℝ (Fin 3)`.
- `EulerExistenceAndSmoothness`: the upstream
  `NavierStokesExistenceAndSmoothness` with the equation's right-hand side
  `nu • Δ (v · t) x - gradient (p · t) x + f x t` replaced by
  `-gradient (p · t) x`, which is what it reduces to for `nu = 0`, `f = 0`;
  `div_free`, `initial_condition`, `velocity_smooth`, `pressure_smooth` are
  unchanged (with `Function.uncurry` written out instead of the `↿` notation).
- `EulerExistenceAndSmoothnessR3`: the upstream `…Rn` class, with the same
  `integrable` and `globally_bounded_energy` fields.
- The theorem asks for a datum `u₀` with `InitialVelocityConditionDecay u₀`
  such that no `(v, p)` satisfies `EulerExistenceAndSmoothnessR3 u₀ v p`. This
  is the shape of Clay alternative (C) with the force fixed to zero, which is a
  stronger requirement on the construction than (C) itself.

**Second theorem, `exists_compact_smooth_euler_singularity`.** Its additional
definitions have no upstream source, so each was read for junk-value traps
(a Lean definition that returns a default value when a hypothesis fails can
make a statement vacuous if nothing in the statement rules the default out):

- `toL2 f` is the `L²` class of `f` if `MemLp f 2 volume`, else `0`. Every use
  is inside `SobolevSmoothOn I v`, whose fields `integrable` and
  `jets_integrable` require `MemLp` for `v · t` and every
  `iteratedFDeriv ℝ m (v · t)` at every `t ∈ I`, and inside
  `HasDerivAt (fun s => toL2 (v · s)) (toL2 (w · t)) t` at interior `t`,
  where `v` and `w` are both required `SobolevSmoothOn I`. So the default
  branch is never the one being talked about.
- `vorticity v x` is the curl computed from `fderiv ℝ v x`, which is `0` where
  `v` is not differentiable; `SobolevSmoothOn` requires `ContDiff ℝ ∞ (v · t)`.
- `velocityC1Norm v` and `vorticityNorm v` are suprema in `ℝ≥0∞` of
  `ENNReal.ofReal` of pointwise norms, so an unbounded field has norm `⊤` and
  nothing is clipped.
- `EulerSobolevExistenceAndSmoothnessR3On I u₀ v p` imposes the equation only
  at interior times through a witness `w` for the strong `L²` time derivative,
  and asks nothing of `p` beyond spatial differentiability at interior times.
  Since `w` and `v` are fixed by the other fields, `∇p` is determined by the
  equation, so the weak requirement on `p` does not create a loophole.
- The conclusion packages: a nonzero compactly supported datum satisfying the
  first theorem's decay class; a lifespan `0 < Tstar ≤ 1`; a solution on
  `[0, Tstar)` with uniformly bounded energy; maximality in the Sobolev class
  (closed-interval solutions exist exactly for `T < Tstar`); bounded `C¹` norm
  and finite vorticity integral on every `[0, T]` with `T < Tstar`; `limsup` of
  the `C¹` norm equal to `⊤` as `t → Tstar⁻`; vorticity integral over
  `[0, Tstar)` equal to `⊤`; and the first theorem's global nonexistence for
  the same datum.

The reading found nothing that makes either statement vacuous or weaker than
its informal description. `Euler/SolutionDefinitions.lean`, the copy that the
proof imports, is byte-identical to the challenge file from the `ℝ³` notation
onward except that the two theorems and their doc comments are absent.

### 3. Build

```
lake build Euler ComparatorChallenges
…
Build completed successfully (10606 jobs).
```

All 1839 `Euler.*` modules plus the root `Euler` module were compiled (the
job count includes the already-built Mathlib and NavierStokes dependencies of
the shared Comparator target). The log (`logs/euler-build-summary.log`) has
0 errors and 4 warnings, all of them the `sorry` placeholders in the two
challenge files:

```
ComparatorChallenges/Euler.lean:85:8: declaration uses `sorry`
ComparatorChallenges/Euler.lean:170:8: declaration uses `sorry`
ComparatorChallenges/NavierStokes.lean:273:8: declaration uses `sorry`
ComparatorChallenges/NavierStokes.lean:280:8: declaration uses `sorry`
```

Because the `Euler` library is configured with `warningAsError = true`, a
warning in any of its own modules would have been a build failure.

### 4. Axiom audit

`Euler/Solution.lean` ends with two `#print axioms` commands; the build log
records:

```
'Euler.euler_breakdown_R3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Euler.exists_compact_smooth_euler_singularity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`sorryAx` does not appear, and no project-specific axiom exists.

### 5. Independent restatement

`Verification/EulerIndependentCheck.lean` imports only the submission root
`Euler.Solution`, never the challenge module. It restates every challenge
definition in a fresh namespace `Euler.IndependentCheck`, proves each
definition equal to the submission's by `rfl` and each structure equivalent
field by field, and then derives both theorems as stated with the restated
definitions from the submission's theorems. Running it:

```
lake env lean Verification/EulerIndependentCheck.lean
'Euler.euler_breakdown_R3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Euler.exists_compact_smooth_euler_singularity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Euler.IndependentCheck.euler_breakdown_R3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Euler.IndependentCheck.exists_compact_smooth_euler_singularity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The restated definitions were additionally compiled on their own against plain
`import Mathlib` to confirm they do not depend on anything from the project.

### 6. leanchecker kernel replay

PENDING

### 7. Comparator

`lake exe comparator ComparatorChallenges/Euler.json` was run exactly as for
Navier–Stokes, with the real `landrun` sandbox, `lean4export`, and
`nanoda_bin`. Output (build lines omitted; the filtered log is in
`logs/comparator-euler.log`):

```
Building ComparatorChallenges.Euler
Build completed successfully (8763 jobs).
Exporting #[…, Euler.euler_breakdown_R3, Euler.exists_compact_smooth_euler_singularity, propext, Quot.sound, Classical.choice, …] from ComparatorChallenges.Euler
Building Euler.Solution
Build completed successfully (10591 jobs).
Exporting #[…] from Euler.Solution
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

This is the check that matters most for the second theorem: Comparator
compares every constant reachable from the two theorem statements between the
challenge export and the solution export, so the project-specific definitions
`toL2`, `SobolevSmoothOn`, `EulerSobolevExistenceAndSmoothnessR3On`,
`vorticity`, `velocityC1Norm`, and `vorticityNorm` are certified identical in
the two modules, down to the elaborated instance paths. Wall time for the
whole run was about 24 minutes (01:06:09 to 01:30:31 UTC).

## What this does and does not establish

The same remarks as in [README.md](README.md) apply. In addition, the Euler
challenge is maintained in this repository rather than by an external project,
so there is no upstream reference statement to defer to; the hand review in
section 2 is the substitute, and readers should repeat it for themselves.
