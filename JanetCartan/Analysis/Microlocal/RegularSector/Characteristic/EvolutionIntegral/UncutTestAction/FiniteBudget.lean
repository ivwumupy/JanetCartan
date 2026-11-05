module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.FiniteRetardedLimit
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.CoefficientJets

/-!
# The parent's finite primitive reserve supplies uncut inversion

The joint carrier cover and the original `fullLowReserve (d+1)` multiplier
budget produce every symbol derivative bound needed by the finite inversion
proof. Both masks are kept: a nonempty support point in each gives the
frequency cover, while a zero mask gives the zero physical test action.
Consumer: primitive instantiation of the SAME strong limits in
`app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
open FourierIntegral FullLowBounds FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
open PrimitiveProfiles SymbolBudgets KernelIdentification LowBounds.FrequencyCutoff
variable {d q : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ

/-- The exact finite normalized reserve and joint carrier cover of
`exists_retardedOperator_of_primitive_data` supply the `d+2` multiplier
bounds used by `retardedOperator_eq_uncutPhysicalIntegral_of_strongLimit`
and `elapsedGraph_eq_uncutSpatialGraph_of_finite_bounds_strongLimit`.
No all-order symbol budget is required. If a mask has empty support,
its test action is zero instead. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem norm_iteratedFDeriv_multiplier_le_primitive_joint_budgets
    (z : ι → Point (d + 1)) (δ : ι → ℝ) (χout χsource β : E → ℂ)
    (hβ : ContDiff ℝ ∞ β)
    (ho : (tsupport χout).Nonempty) (hs : (tsupport χsource).Nonempty)
    (hcover : ∀ p ∈ (tsupport χout ×ˢ tsupport χsource) ×ˢ tsupport β,
      ∃ i, ∃ R : ℝ, 1 ≤ R ∧ ∃ v ∈ Metric.closedBall (z i) (δ i),
        p = (v.1, R • v.2) ∧ 1 + ‖p.2‖ ≤ R)
    (hb : ∀ i, BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i))
      (fullLowReserve (d + 1)) (jointMultiplier β))
    (k : ℕ) (hk : k ≤ d + 2) (ξ : E) :
    ‖iteratedFDeriv ℝ k β ξ‖ ≤ ∑ i, normalizedSeminorm
      (Metric.closedBall (z i) (δ i)) k (jointMultiplier β) := by
  apply norm_iteratedFDeriv_multiplier_le_normalized_budgets z δ β hβ _ k _ ξ
  · intro η hη
    obtain ⟨x, hx⟩ := ho
    obtain ⟨y, hy⟩ := hs
    obtain ⟨i, R, hR, v, hv, he, _⟩ := hcover ((x, y), η) ⟨⟨hx, hy⟩, hη⟩
    exact ⟨i, R, hR, v, hv, congrArg Prod.snd he⟩
  · intro i
    apply (hb i).mono
    rw [fullLowReserve_eq]
    omega

/-- A zero source mask gives the actual zero Schwartz input to the multiplier,
including when the joint carrier cover is vacuous. Consumer: the empty-mask
case of primitive instantiation in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem graphTestToSchwartz_complexSourceMaskTest_eq_zero
    (χsource : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (hzero : ∀ x, χsource x = 0) (u : graphTestSpace (d + 1) q) :
    graphTestToSchwartz (complexSourceMaskTest χsource hs u) = 0 := by
  apply SchwartzMap.ext
  intro x
  simp [graphTestToSchwartz_apply, complexSourceMaskTest, hzero]

/-- Vanishing of either original physical mask makes the literal finite-budget
retarded action zero, without requiring a global bound on `β` from a vacuous
carrier cover. Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem retardedPhysicalIntegral_eq_zero_of_mask
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (hs : ContDiff ℝ ∞ χsource) (a : ℝ) (u : graphTestSpace (d + 1) q)
    (hzero : (∀ x, χout x = 0) ∨ (∀ x, χsource x = 0)) (x : E) :
    retardedPhysicalIntegral Ψ b χout χsource β hs a u x = 0 := by
  rcases hzero with ho | hs0
  · simp [retardedPhysicalIntegral, ho]
  · have hu := graphTestToSchwartz_complexSourceMaskTest_eq_zero χsource hs hs0 u
    simp [retardedPhysicalIntegral, hu, physicalMultiplierIntegral,
      sourceInputFourierTransform, Real.fourierInv_eq', graphOperator]

/-- The parent's compact physical representatives vanish for the same empty
mask cases. Together with strong-limit uniqueness, this supplies the zero
case of primitive instantiation without another analytic premise. Source:
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem cutRetardedPhysical_eq_zero_of_mask
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β θ : E → ℂ)
    (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (a : ℝ) (u : graphTestSpace (d + 1) q)
    (hzero : (∀ x, χout x = 0) ∨ (∀ x, χsource x = 0)) (x : E) :
    cutRetardedPhysical Ψ b χout χsource β θ hs hβ hθ hθcs a u x = 0 := by
  rcases hzero with ho | hs0
  · simp [cutRetardedPhysical, ho]
  · have hu := graphTestToSchwartz_complexSourceMaskTest_eq_zero χsource hs hs0 u
    have hm (s : ℝ) (y : Euclidean d) :
        cutPhysicalMultiplierSlice β θ (graphTestToSchwartz
          (complexSourceMaskTest χsource hs u)) hβ hθ hθcs s y = 0 := by
      rw [cutPhysicalMultiplierSlice_apply, cutPhysicalMultiplier_eq_integral, hu]
      simp [sourceInputFourierTransform]
    simp [cutRetardedPhysical, graphOperator, hm]

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
