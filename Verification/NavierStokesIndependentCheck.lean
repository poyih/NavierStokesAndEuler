import NavierStokes.ComparatorSolution

/-!
# Independent restatement check for the Navier–Stokes Comparator submission

This file is an independent cross-check of the Comparator submission in
`NavierStokes/ComparatorSolution.lean`, written without using the Comparator tool.

It restates, in a fresh namespace `NavierStokes.IndependentCheck`, every definition
of the challenge file `ComparatorChallenges/NavierStokes.lean` verbatim. Those are the
definitions of the Formal Conjectures Navier–Stokes statement at commit
`8bf45ed70d48b2b2a501de9c00b26bfa38c573ee`, with the `ℝ^n` / `ℝ³` notation inlined as
`EuclideanSpace ℝ (Fin n)` / `EuclideanSpace ℝ (Fin 3)`, exactly as the upstream
`FormalConjecturesForMathlib.Geometry` files define it.

It then proves the two breakdown alternatives (C) and (D), stated with the restated
definitions, from the submission's theorems. The proofs only unpack and repack structure
fields: no mathematics is involved. A successful compilation therefore certifies that
the submission's theorems have exactly the meaning of the challenge statements, with
respect to a copy of the challenge definitions that the submission never imports.

The file imports only the submission root, never `ComparatorChallenges.NavierStokes`,
so the two sets of definitions are compared purely by their types.
-/

open ContDiff Set InnerProductSpace MeasureTheory
open scoped Laplacian

namespace NavierStokes.IndependentCheck

local notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

variable {n : ℕ}

/-! ## Verbatim copies of the challenge definitions -/

noncomputable
def divergence (v : ℝ^n → ℝ^n) (x : ℝ^n) : ℝ := (fderiv ℝ v x).trace ℝ (ℝ^n)

local notation "∇⬝" => divergence

def IsOnePeriodic {α : Sort*} (f : ℝ^n → α) : Prop :=
  ∀ x i, f (x + EuclideanSpace.single i 1) = f x

structure InitialVelocityCondition (u₀ : ℝ^n → ℝ^n) : Prop where
  div_free : ∀ x, ∇⬝ u₀ x = 0
  smooth : ContDiff ℝ ∞ u₀

structure InitialVelocityConditionDecay (u₀ : ℝ^n → ℝ^n) : Prop extends
    InitialVelocityCondition u₀ where
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ m u₀ x‖ ≤ C / (1 + ‖x‖) ^ K

structure InitialVelocityConditionPeriodic (u₀ : ℝ^n → ℝ^n) : Prop extends
    InitialVelocityCondition u₀ where
  isOnePeriodic : IsOnePeriodic u₀

structure ForceCondition (f : ℝ^n → ℝ → ℝ^n) : Prop where
  smooth : ContDiffOn ℝ ∞ (↿f) (Set.univ ×ˢ Set.Ici 0)

structure ForceConditionDecay (f : ℝ^n → ℝ → ℝ^n) : Prop extends ForceCondition f where
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ∀ t ≥ 0,
    ‖iteratedFDerivWithin ℝ m (↿f) (Set.univ ×ˢ Set.Ici 0) (x, t)‖ ≤ C / (1 + ‖x‖ + t) ^ K

structure ForceConditionPeriodic (f : ℝ^n → ℝ → ℝ^n) : Prop extends ForceCondition f where
  isOnePeriodic : ∀ t ≥ 0, IsOnePeriodic (f · t)
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ∀ t ≥ 0,
    ‖iteratedFDerivWithin ℝ m (↿f) (Set.univ ×ˢ Set.Ici 0) (x, t)‖ ≤ C / (1 + t) ^ K

structure NavierStokesExistenceAndSmoothness
    (nu : ℝ) (u₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v : ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) : Prop where
  navier_stokes : ∀ x, ∀ t ≥ 0,
    derivWithin (v x ·) (Set.Ici 0) t + fderiv ℝ (v · t) x (v x t) =
      nu • Δ (v · t) x - gradient (p · t) x + f x t
  div_free : ∀ x, ∀ t ≥ 0, ∇⬝ (v · t) x = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : ContDiffOn ℝ ∞ (↿v) (Set.univ ×ˢ Set.Ici 0)
  pressure_smooth : ContDiffOn ℝ ∞ (↿p) (Set.univ ×ˢ Set.Ici 0)

structure NavierStokesExistenceAndSmoothnessRn
    (nu : ℝ) (u₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v : ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) : Prop
  extends NavierStokesExistenceAndSmoothness nu u₀ f v p where
  integrable : ∀ t ≥ 0, MemLp (‖v · t‖) 2
  globally_bounded_energy : ∃ E, ∀ t ≥ 0, (∫ x : ℝ^n, ‖v x t‖ ^ 2) < E

structure NavierStokesExistenceAndSmoothnessPeriodic
    (nu : ℝ) (u₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v : ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) : Prop
  extends NavierStokesExistenceAndSmoothness nu u₀ f v p where
  isOnePeriodic_velocity : ∀ t ≥ 0, IsOnePeriodic (v · t)
  isOnePeriodic_pressure : ∀ t ≥ 0, IsOnePeriodic (p · t)

/-! ## Field-by-field correspondence with the submission's definitions

Each lemma below is proved by `rfl`, `Iff.rfl`, or by listing the fields. If the
submission's definitions differed from the restated ones in any way, these would fail
to typecheck. -/

theorem divergence_eq (v : ℝ^n → ℝ^n) (x : ℝ^n) :
    divergence v x = Comparator.divergence v x := rfl

theorem isOnePeriodic_iff {α : Sort*} (f : ℝ^n → α) :
    IsOnePeriodic f ↔ Comparator.IsOnePeriodic f := Iff.rfl

theorem initialVelocityConditionDecay_iff (u₀ : ℝ^n → ℝ^n) :
    InitialVelocityConditionDecay u₀ ↔ Comparator.InitialVelocityConditionDecay u₀ :=
  ⟨fun h => { div_free := h.div_free, smooth := h.smooth, decay := h.decay },
   fun h => { div_free := h.div_free, smooth := h.smooth, decay := h.decay }⟩

theorem initialVelocityConditionPeriodic_iff (u₀ : ℝ^n → ℝ^n) :
    InitialVelocityConditionPeriodic u₀ ↔ Comparator.InitialVelocityConditionPeriodic u₀ :=
  ⟨fun h => { div_free := h.div_free, smooth := h.smooth, isOnePeriodic := h.isOnePeriodic },
   fun h => { div_free := h.div_free, smooth := h.smooth, isOnePeriodic := h.isOnePeriodic }⟩

theorem forceConditionDecay_iff (f : ℝ^n → ℝ → ℝ^n) :
    ForceConditionDecay f ↔ Comparator.ForceConditionDecay f :=
  ⟨fun h => { smooth := h.smooth, decay := h.decay },
   fun h => { smooth := h.smooth, decay := h.decay }⟩

theorem forceConditionPeriodic_iff (f : ℝ^n → ℝ → ℝ^n) :
    ForceConditionPeriodic f ↔ Comparator.ForceConditionPeriodic f :=
  ⟨fun h => { smooth := h.smooth, isOnePeriodic := h.isOnePeriodic, decay := h.decay },
   fun h => { smooth := h.smooth, isOnePeriodic := h.isOnePeriodic, decay := h.decay }⟩

theorem navierStokesExistenceAndSmoothnessRn_iff
    (nu : ℝ) (u₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v : ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) :
    NavierStokesExistenceAndSmoothnessRn nu u₀ f v p ↔
      Comparator.NavierStokesExistenceAndSmoothnessRn nu u₀ f v p :=
  ⟨fun h => { navier_stokes := h.navier_stokes, div_free := h.div_free,
              initial_condition := h.initial_condition,
              velocity_smooth := h.velocity_smooth, pressure_smooth := h.pressure_smooth,
              integrable := h.integrable,
              globally_bounded_energy := h.globally_bounded_energy },
   fun h => { navier_stokes := h.navier_stokes, div_free := h.div_free,
              initial_condition := h.initial_condition,
              velocity_smooth := h.velocity_smooth, pressure_smooth := h.pressure_smooth,
              integrable := h.integrable,
              globally_bounded_energy := h.globally_bounded_energy }⟩

theorem navierStokesExistenceAndSmoothnessPeriodic_iff
    (nu : ℝ) (u₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v : ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) :
    NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p ↔
      Comparator.NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p :=
  ⟨fun h => { navier_stokes := h.navier_stokes, div_free := h.div_free,
              initial_condition := h.initial_condition,
              velocity_smooth := h.velocity_smooth, pressure_smooth := h.pressure_smooth,
              isOnePeriodic_velocity := h.isOnePeriodic_velocity,
              isOnePeriodic_pressure := h.isOnePeriodic_pressure },
   fun h => { navier_stokes := h.navier_stokes, div_free := h.div_free,
              initial_condition := h.initial_condition,
              velocity_smooth := h.velocity_smooth, pressure_smooth := h.pressure_smooth,
              isOnePeriodic_velocity := h.isOnePeriodic_velocity,
              isOnePeriodic_pressure := h.isOnePeriodic_pressure }⟩

/-! ## The challenge theorems, restated and derived from the submission -/

/-- (C) Breakdown of Navier–Stokes solutions on ℝ³, exactly as in the challenge file. -/
theorem navier_stokes_breakdown_R3 (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionDecay u₀ ∧ ForceConditionDecay f ∧
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p) := by
  obtain ⟨u₀, f, hu, hf, hno⟩ := Comparator.navier_stokes_breakdown_R3 nu hnu
  refine ⟨u₀, f, (initialVelocityConditionDecay_iff u₀).2 hu,
    (forceConditionDecay_iff f).2 hf, ?_⟩
  rintro ⟨v, p, hvp⟩
  exact hno ⟨v, p, (navierStokesExistenceAndSmoothnessRn_iff nu u₀ f v p).1 hvp⟩

/-- (D) Breakdown of Navier–Stokes Solutions on ℝ³/ℤ³, exactly as in the challenge file. -/
theorem navier_stokes_breakdown_periodic (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionPeriodic u₀ ∧ ForceConditionPeriodic f ∧
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p) := by
  obtain ⟨u₀, f, hu, hf, hno⟩ := Comparator.navier_stokes_breakdown_periodic nu hnu
  refine ⟨u₀, f, (initialVelocityConditionPeriodic_iff u₀).2 hu,
    (forceConditionPeriodic_iff f).2 hf, ?_⟩
  rintro ⟨v, p, hvp⟩
  exact hno ⟨v, p, (navierStokesExistenceAndSmoothnessPeriodic_iff nu u₀ f v p).1 hvp⟩

end NavierStokes.IndependentCheck

/-! ## Axiom audit

Both the submission's theorems and the restated theorems must depend only on the
three standard axioms `propext`, `Classical.choice`, and `Quot.sound`. In particular,
`sorryAx` must not appear. -/

#print axioms NavierStokes.Comparator.navier_stokes_breakdown_R3
#print axioms NavierStokes.Comparator.navier_stokes_breakdown_periodic
#print axioms NavierStokes.IndependentCheck.navier_stokes_breakdown_R3
#print axioms NavierStokes.IndependentCheck.navier_stokes_breakdown_periodic
