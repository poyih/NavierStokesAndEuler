import Euler.Solution

/-!
# Independent restatement check for the Euler Comparator submission

This file is an independent cross-check of the Comparator submission in
`Euler/Solution.lean`, written without using the Comparator tool.

It restates, in a fresh namespace `Euler.IndependentCheck`, every definition of the
challenge file `ComparatorChallenges/Euler.lean` verbatim, and then proves both
challenge theorems, stated with the restated definitions, from the submission's
theorems. The proofs only unpack and repack structure fields and existential
witnesses: no mathematics is involved. A successful compilation therefore certifies
that the submission's theorems have exactly the meaning of the challenge statements,
with respect to a copy of the challenge definitions that the submission never imports.

The file imports only the submission root, never `ComparatorChallenges.Euler`,
so the two sets of definitions are compared purely by their types.
-/

open ContDiff Set InnerProductSpace MeasureTheory

namespace Euler.IndependentCheck

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Verbatim copies of the challenge definitions -/

noncomputable def divergence (v : ℝ³ → ℝ³) (x : ℝ³) : ℝ :=
  (fderiv ℝ v x).trace ℝ ℝ³

local notation "∇⬝" => divergence

structure InitialVelocityCondition (u₀ : ℝ³ → ℝ³) : Prop where
  div_free : ∀ x, ∇⬝ u₀ x = 0
  smooth : ContDiff ℝ ∞ u₀

structure InitialVelocityConditionDecay (u₀ : ℝ³ → ℝ³) : Prop extends
    InitialVelocityCondition u₀ where
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x,
    ‖iteratedFDeriv ℝ m u₀ x‖ ≤ C / (1 + ‖x‖) ^ K

structure EulerExistenceAndSmoothness
    (u₀ : ℝ³ → ℝ³) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop where
  euler : ∀ x, ∀ t ≥ 0,
    derivWithin (v x ·) (Set.Ici 0) t + fderiv ℝ (v · t) x (v x t) =
      -gradient (p · t) x
  div_free : ∀ x, ∀ t ≥ 0, ∇⬝ (v · t) x = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : ContDiffOn ℝ ∞ (Function.uncurry v) (Set.univ ×ˢ Set.Ici 0)
  pressure_smooth : ContDiffOn ℝ ∞ (Function.uncurry p) (Set.univ ×ˢ Set.Ici 0)

structure EulerExistenceAndSmoothnessR3
    (u₀ : ℝ³ → ℝ³) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop
    extends EulerExistenceAndSmoothness u₀ v p where
  integrable : ∀ t ≥ 0, MemLp (‖v · t‖) 2
  globally_bounded_energy : ∃ E : ℝ, ∀ t ≥ 0, (∫ x : ℝ³, ‖v x t‖ ^ 2) < E

open scoped ENNReal Topology

noncomputable def toL2 {V : Type*} [NormedAddCommGroup V] (f : ℝ³ → V) :
    Lp V 2 (volume : Measure ℝ³) := by
  classical
  exact if h : MemLp f 2 volume then h.toLp f else 0

structure SobolevSmoothOn (I : Set ℝ) (v : ℝ³ → ℝ → ℝ³) : Prop where
  spatial_smooth : ∀ t ∈ I, ContDiff ℝ ∞ (v · t)
  integrable : ∀ t ∈ I, MemLp (v · t) 2
  jets_integrable : ∀ m : ℕ, ∀ t ∈ I, MemLp (iteratedFDeriv ℝ m (v · t)) 2
  continuous : ContinuousOn (fun t => toL2 (v · t)) I
  jets_continuous : ∀ m : ℕ,
    ContinuousOn (fun t => toL2 (iteratedFDeriv ℝ m (v · t))) I

structure EulerSobolevExistenceAndSmoothnessR3On (I : Set ℝ)
    (u₀ : ℝ³ → ℝ³) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop where
  div_free : ∀ x, ∀ t ∈ I, ∇⬝ (v · t) x = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : SobolevSmoothOn I v
  pressure_differentiable : ∀ t ∈ interior I, Differentiable ℝ (p · t)
  euler : ∃ w : ℝ³ → ℝ → ℝ³,
    SobolevSmoothOn I w ∧
      (∀ t ∈ interior I,
        HasDerivAt (fun s => toL2 (v · s)) (toL2 (w · t)) t) ∧
      (∀ x, ∀ t ∈ interior I,
        w x t + fderiv ℝ (v · t) x (v x t) = -gradient (p · t) x)

noncomputable def vorticity (v : ℝ³ → ℝ³) (x : ℝ³) : ℝ³ :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    (fderiv ℝ v x (EuclideanSpace.single (i + 1) 1)) (i + 2) -
      (fderiv ℝ v x (EuclideanSpace.single (i + 2) 1)) (i + 1))

noncomputable def velocityC1Norm (v : ℝ³ → ℝ³) : ℝ≥0∞ :=
  (⨆ x, ENNReal.ofReal ‖v x‖) + (⨆ x, ENNReal.ofReal ‖fderiv ℝ v x‖)

noncomputable def vorticityNorm (v : ℝ³ → ℝ³) : ℝ≥0∞ :=
  ⨆ x, ENNReal.ofReal ‖vorticity v x‖

/-! ## Correspondence with the submission's definitions

Each definition is literally the same term as the submission's, so the equations are
`rfl`; each structure is matched field by field. -/

theorem divergence_eq (v : ℝ³ → ℝ³) (x : ℝ³) : divergence v x = Euler.divergence v x := rfl

theorem toL2_eq {V : Type*} [NormedAddCommGroup V] (f : ℝ³ → V) :
    toL2 f = Euler.toL2 f := rfl

theorem vorticity_eq (v : ℝ³ → ℝ³) (x : ℝ³) : vorticity v x = Euler.vorticity v x := rfl

theorem velocityC1Norm_eq (v : ℝ³ → ℝ³) : velocityC1Norm v = Euler.velocityC1Norm v := rfl

theorem vorticityNorm_eq (v : ℝ³ → ℝ³) : vorticityNorm v = Euler.vorticityNorm v := rfl

theorem initialVelocityConditionDecay_iff (u₀ : ℝ³ → ℝ³) :
    InitialVelocityConditionDecay u₀ ↔ Euler.InitialVelocityConditionDecay u₀ :=
  ⟨fun h => { div_free := h.div_free, smooth := h.smooth, decay := h.decay },
   fun h => { div_free := h.div_free, smooth := h.smooth, decay := h.decay }⟩

theorem eulerExistenceAndSmoothnessR3_iff (u₀ : ℝ³ → ℝ³) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) :
    EulerExistenceAndSmoothnessR3 u₀ v p ↔ Euler.EulerExistenceAndSmoothnessR3 u₀ v p :=
  ⟨fun h => { euler := h.euler, div_free := h.div_free, initial_condition := h.initial_condition,
              velocity_smooth := h.velocity_smooth, pressure_smooth := h.pressure_smooth,
              integrable := h.integrable, globally_bounded_energy := h.globally_bounded_energy },
   fun h => { euler := h.euler, div_free := h.div_free, initial_condition := h.initial_condition,
              velocity_smooth := h.velocity_smooth, pressure_smooth := h.pressure_smooth,
              integrable := h.integrable, globally_bounded_energy := h.globally_bounded_energy }⟩

theorem sobolevSmoothOn_iff (I : Set ℝ) (v : ℝ³ → ℝ → ℝ³) :
    SobolevSmoothOn I v ↔ Euler.SobolevSmoothOn I v :=
  ⟨fun h => { spatial_smooth := h.spatial_smooth, integrable := h.integrable,
              jets_integrable := h.jets_integrable, continuous := h.continuous,
              jets_continuous := h.jets_continuous },
   fun h => { spatial_smooth := h.spatial_smooth, integrable := h.integrable,
              jets_integrable := h.jets_integrable, continuous := h.continuous,
              jets_continuous := h.jets_continuous }⟩

theorem eulerSobolevExistenceAndSmoothnessR3On_iff (I : Set ℝ)
    (u₀ : ℝ³ → ℝ³) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) :
    EulerSobolevExistenceAndSmoothnessR3On I u₀ v p ↔
      Euler.EulerSobolevExistenceAndSmoothnessR3On I u₀ v p := by
  constructor
  · intro h
    obtain ⟨w, hw, hderiv, heq⟩ := h.euler
    exact { div_free := h.div_free, initial_condition := h.initial_condition,
            velocity_smooth := (sobolevSmoothOn_iff I v).1 h.velocity_smooth,
            pressure_differentiable := h.pressure_differentiable,
            euler := ⟨w, (sobolevSmoothOn_iff I w).1 hw, hderiv, heq⟩ }
  · intro h
    obtain ⟨w, hw, hderiv, heq⟩ := h.euler
    exact { div_free := h.div_free, initial_condition := h.initial_condition,
            velocity_smooth := (sobolevSmoothOn_iff I v).2 h.velocity_smooth,
            pressure_differentiable := h.pressure_differentiable,
            euler := ⟨w, (sobolevSmoothOn_iff I w).2 hw, hderiv, heq⟩ }

/-! ## The challenge theorems, restated and derived from the submission -/

/-- Whole-space breakdown for unforced Euler, exactly as in the challenge file. -/
theorem euler_breakdown_R3 :
    ∃ u₀ : ℝ³ → ℝ³, InitialVelocityConditionDecay u₀ ∧
      ¬ (∃ v p, EulerExistenceAndSmoothnessR3 u₀ v p) := by
  obtain ⟨u₀, hu, hno⟩ := Euler.euler_breakdown_R3
  refine ⟨u₀, (initialVelocityConditionDecay_iff u₀).2 hu, ?_⟩
  rintro ⟨v, p, hvp⟩
  exact hno ⟨v, p, (eulerExistenceAndSmoothnessR3_iff u₀ v p).1 hvp⟩

/-- Finite lifespan and quantitative singularity, exactly as in the challenge file. -/
theorem exists_compact_smooth_euler_singularity :
    ∃ (u₀ : ℝ³ → ℝ³) (Tstar : ℝ) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
      InitialVelocityConditionDecay u₀ ∧ HasCompactSupport u₀ ∧ u₀ ≠ 0 ∧
      0 < Tstar ∧ Tstar ≤ 1 ∧
      EulerSobolevExistenceAndSmoothnessR3On (Ico 0 Tstar) u₀ v p ∧
      (∃ E : ℝ, ∀ t ∈ Ico (0 : ℝ) Tstar, (∫ x : ℝ³, ‖v x t‖ ^ 2) < E) ∧
      (∀ T : ℝ, 0 < T →
        ((∃ w q, EulerSobolevExistenceAndSmoothnessR3On (Icc 0 T) u₀ w q) ↔ T < Tstar)) ∧
      (∀ T ∈ Ioo 0 Tstar,
        (⨆ t ∈ Icc (0 : ℝ) T, velocityC1Norm (v · t)) < ⊤ ∧
        (∫⁻ t in Ico (0 : ℝ) T, vorticityNorm (v · t)) < ⊤) ∧
      Filter.limsup (fun t : ℝ => velocityC1Norm (v · t)) (𝓝[<] Tstar) = ⊤ ∧
      (∫⁻ t in Ico (0 : ℝ) Tstar, vorticityNorm (v · t)) = ⊤ ∧
      ¬ (∃ w q, EulerExistenceAndSmoothnessR3 u₀ w q) := by
  obtain ⟨u₀, Tstar, v, p, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ :=
    Euler.exists_compact_smooth_euler_singularity
  refine ⟨u₀, Tstar, v, p, (initialVelocityConditionDecay_iff u₀).2 h₁, h₂, h₃, h₄, h₅,
    (eulerSobolevExistenceAndSmoothnessR3On_iff _ u₀ v p).2 h₆, h₇, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hT
    rw [← h₈ T hT]
    constructor
    · rintro ⟨w, q, hwq⟩
      exact ⟨w, q, (eulerSobolevExistenceAndSmoothnessR3On_iff _ u₀ w q).1 hwq⟩
    · rintro ⟨w, q, hwq⟩
      exact ⟨w, q, (eulerSobolevExistenceAndSmoothnessR3On_iff _ u₀ w q).2 hwq⟩
  · intro T hT
    simpa only [velocityC1Norm_eq, vorticityNorm_eq] using h₉ T hT
  · simpa only [velocityC1Norm_eq] using h₁₀
  · simpa only [vorticityNorm_eq] using h₁₁
  · rintro ⟨w, q, hwq⟩
    exact h₁₂ ⟨w, q, (eulerExistenceAndSmoothnessR3_iff u₀ w q).1 hwq⟩

end Euler.IndependentCheck

/-! ## Axiom audit -/

#print axioms Euler.euler_breakdown_R3
#print axioms Euler.exists_compact_smooth_euler_singularity
#print axioms Euler.IndependentCheck.euler_breakdown_R3
#print axioms Euler.IndependentCheck.exists_compact_smooth_euler_singularity
