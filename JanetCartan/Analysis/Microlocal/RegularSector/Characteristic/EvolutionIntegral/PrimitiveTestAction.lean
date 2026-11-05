module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction

/-!
# Closing the fixed-time and literal-adjoint primitive test actions

The exact regularizations of `PrimitiveRetarded` identify the original
fixed-time spatial action and reversed-triangle adjoint. All analytic bounds
are derived from the original finite symbol budgets, including empty masks.
The final construction in `PrimitiveBounds` supplies the strong limits.
Source: `app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral
open FourierIntegral SymbolBudgets KernelIdentification UncutTestAction
open FullLowBounds FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local PrimitiveProfiles
open LowBounds.FrequencyCutoff
variable {d q : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => Euclidean (d + 1)

/-- Original fixed-time test action from the same strong limit and finite
primitive budgets, with both masks. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem elapsedGraph_eq_uncutSpatialGraph_of_primitive_budgets
    (z : ι → Point (d + 1)) (δ : ι → ℝ)
    {J : Set (TwoTimePoint d)} (hJ : IsCompact J)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (Δ : ℝ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ContDiff ℝ ∞ (jointAmplitude b))
    (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (hcover : ∀ p ∈ (tsupport χout ×ˢ tsupport χsource) ×ˢ tsupport β,
      ∃ i, ∃ R : ℝ, 1 ≤ R ∧ ∃ v ∈ Metric.closedBall (z i) (δ i),
        p = (v.1, R • v.2) ∧ 1 + ‖p.2‖ ≤ R)
    (hβbudget : ∀ i, BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i))
      (fullLowReserve (d + 1)) (jointMultiplier β))
    (hmap : ∀ r ∈ Icc 0 Δ, ∀ i,
      MapsTo (elapsedPoint r) (Metric.closedBall (z i) (δ i)) J)
    (o : ℕ) (hbbudget : BoundedTwoTimeOrderSeminorm o J (fullLowReserve (d + 1)) b)
    (χ : ℕ → E → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (hχcs : ∀ j, HasCompactSupport (χ j))
    (hcut : ∀ A : FullAmplitude (d + 1) q,
      (∀ x y ξ, ξ ∉ tsupport β → A x y ξ = 0) → ∀ j,
      frequencyCutFullAmplitude (χ j) A = frequencyCutFullAmplitude (complexPhysicalCutoff j) A)
    (r : ℝ) (hr : r ∈ Icc 0 Δ) (u : graphTestSpace (d + 1) q)
    (hstrong : ∃ R : ℕ → SpacetimeL2 d q,
      (∀ j, R j =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (χout x • graphOperator (Ψ (x 0) (x 0 - r))
          (fun y _ η ↦ b (x 0) (x 0 - r) y η)
          (cutPhysicalMultiplierSlice β (χ j)
            (graphTestToSchwartz (complexSourceMaskTest χsource hs u))
            hβ (hχ j) (hχcs j) (x 0 - r)) (spatialPart x))) ∧
      Tendsto R atTop (𝓝 (elapsedGraph Ψ b χout χsource β r (graphTestToLp u)))) :
    elapsedGraph Ψ b χout χsource β r (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (χout x • graphOperator (Ψ (x 0) (x 0 - r))
        (fun y _ η ↦ b (x 0) (x 0 - r) y η)
        (fun z ↦ physicalMultiplierIntegral β
          (graphTestToSchwartz (complexSourceMaskTest χsource hs u))
          (timeSpacePoint (x 0 - r) z)) (spatialPart x)) := by
  by_cases hm : (tsupport χout).Nonempty ∧ (tsupport χsource).Nonempty
  · apply elapsedGraph_eq_uncutSpatialGraph_of_finite_bounds_strongLimit
      Ψ b χout χsource β hs hβ
      (fun k ↦ ∑ i, normalizedSeminorm (Metric.closedBall (z i) (δ i)) k (jointMultiplier β))
      (norm_iteratedFDeriv_multiplier_le_primitive_joint_budgets
        z δ χout χsource β hβ hm.1 hm.2 hcover hβbudget)
      χ hχ hχcs hcut r u _ _
      (twoTimeOrderSeminorm o J (fullLowReserve (d + 1)) b) _ hstrong
    · intro x hx ξ hξ
      exact (hΨ r hr x hx ξ hξ).comp (f := fun ξ : E ↦
        ((x 0, x 0-r), (spatialPart x, spatialPart ξ)))
        (continuous_const.prodMk (continuous_const.prodMk continuous_spatialPart)).continuousAt
    · intro x _ ξ _
      exact (hb.continuous.comp
        ((continuous_const (y := (x 0, x 0-r, spatialPart x))).prodMk continuous_spatialPart)).continuousAt
    · intro x hx ξ hξ
      obtain ⟨y, hy⟩ := hm.2
      exact norm_elapsedSpatialAmplitude_le_orderSeminorm z δ hJ χout χsource β
        hcover r (hmap r hr) o _ b hb hbbudget hx hy hξ
  · have hz : (∀ x, χout x = 0) ∨ (∀ x, χsource x = 0) := by
      by_cases ho' : (tsupport χout).Nonempty
      · right
        intro x
        by_contra hx
        exact hm ⟨ho', x, subset_tsupport χsource hx⟩
      · left
        intro x
        by_contra hx
        exact ho' ⟨x, subset_tsupport χout hx⟩
    obtain ⟨R, hR, hlim⟩ := hstrong
    have he (j : ℕ) : R j = 0 := by
      apply Lp.ext
      filter_upwards [hR j, Lp.coeFn_zero (EuclideanSpace ℂ (Fin q)) 2 volume] with x hx hx0
      rw [hx, hx0]
      rcases hz with ho0 | hs0
      · simp [ho0]
      · have hu := graphTestToSchwartz_complexSourceMaskTest_eq_zero χsource hs hs0 u
        have hm (y : Euclidean d) : cutPhysicalMultiplierSlice β (χ j)
            (graphTestToSchwartz (complexSourceMaskTest χsource hs u))
            hβ (hχ j) (hχcs j) (x 0-r) y = 0 := by
          rw [cutPhysicalMultiplierSlice_apply, cutPhysicalMultiplier_eq_integral, hu]
          simp [sourceInputFourierTransform]
        simp [graphOperator, hm]
    have he0 : elapsedGraph Ψ b χout χsource β r (graphTestToLp u) = 0 :=
      tendsto_nhds_unique hlim (by
        rw [show R = fun _ ↦ 0 from funext he]
        exact tendsto_const_nhds)
    rw [he0]
    filter_upwards [Lp.coeFn_zero (EuclideanSpace ℂ (Fin q)) 2 volume] with x hx
    rw [hx]
    rcases hz with ho0 | hs0
    · simp [ho0]
    · have hu := graphTestToSchwartz_complexSourceMaskTest_eq_zero χsource hs hs0 u
      simp [hu, physicalMultiplierIntegral, sourceInputFourierTransform,
        Real.fourierInv_eq', graphOperator]

/-- The SAME Hilbert adjoint has the original reversed-triangle pairing.
The finite primitive budgets supply every analytic input, also for empty
masks. Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem retardedOperator_adjoint_pairing_reverseTriangle_of_primitive_budgets
    (z : ι → Point (d + 1)) (δ : ι → ℝ)
    {J : Set (TwoTimePoint d)} (hJ : IsCompact J)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ContDiff ℝ ∞ (jointAmplitude b))
    (ho : Continuous χout) (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (hocs : HasCompactSupport χout)
    (hcover : ∀ p ∈ (tsupport χout ×ˢ tsupport χsource) ×ˢ tsupport β,
      ∃ i, ∃ R : ℝ, 1 ≤ R ∧ ∃ v ∈ Metric.closedBall (z i) (δ i),
        p = (v.1, R • v.2) ∧ 1 + ‖p.2‖ ≤ R)
    (hβbudget : ∀ i, BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i))
      (fullLowReserve (d + 1)) (jointMultiplier β))
    (hmap : ∀ r ∈ Icc 0 Δ, ∀ i,
      MapsTo (elapsedPoint r) (Metric.closedBall (z i) (δ i)) J)
    (o : ℕ) (hbbudget : BoundedTwoTimeOrderSeminorm o J (fullLowReserve (d + 1)) b)
    (χ : ℕ → E → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (hχcs : ∀ j, HasCompactSupport (χ j))
    (hcut : ∀ A : FullAmplitude (d + 1) q,
      (∀ x y ξ, ξ ∉ tsupport β → A x y ξ = 0) → ∀ j,
      frequencyCutFullAmplitude (χ j) A = frequencyCutFullAmplitude (complexPhysicalCutoff j) A)
    (a : ℝ) (hout : ∀ x, χout x ≠ 0 → x 0 ∈ Icc a (a + Δ))
    (hzero : ∀ t s y η, s ≤ a → b t s y η = 0)
    (Q : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q) (u v : graphTestSpace (d + 1) q)
    (hstrong : ∃ R : ℕ → SpacetimeL2 d q,
      (∀ j, R j =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (cutReverseRetardedFourier Ψ b χout χsource β (χ j)
          (fun x ↦ (u.val x).ofLp) a (a + Δ) x)) ∧
      Tendsto R atTop (𝓝 (Q.adjoint (graphTestToLp u)))) :
    Integrable (fun ξ ↦ inner ℂ (WithLp.toLp 2 (sourceInputFourierTransform
      (graphTestToSchwartz (complexSourceMaskTest χsource hs v)) ξ))
      (WithLp.toLp 2 (reverseRetardedFrequency Ψ b χout β
        (fun x ↦ (u.val x).ofLp) a (a + Δ) ξ))) ∧
    inner ℂ (graphTestToLp v) (Q.adjoint (graphTestToLp u)) =
      ((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ * ∫ ξ,
        inner ℂ (WithLp.toLp 2 (sourceInputFourierTransform
          (graphTestToSchwartz (complexSourceMaskTest χsource hs v)) ξ))
          (WithLp.toLp 2 (reverseRetardedFrequency Ψ b χout β
            (fun x ↦ (u.val x).ofLp) a (a + Δ) ξ)) := by
  by_cases hm : (tsupport χout).Nonempty ∧ (tsupport χsource).Nonempty
  · have hbs : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
        ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
          b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0-r), (spatialPart x, spatialPart ξ)) := by
      intro r _ x _ ξ _
      exact (hb.comp ((contDiff_fst.fst.prodMk
        (contDiff_fst.snd.prodMk contDiff_snd.fst)).prodMk contDiff_snd.snd)).continuous.continuousAt
    apply retardedOperator_adjoint_pairing_reverseTriangle_of_strongLimit
      Ψ b χout χsource β Δ hΔ hΨ hbs ho hβ.continuous hocs hs
      (∑ i, normalizedSeminorm (Metric.closedBall (z i) (δ i)) 0 (jointMultiplier β))
      (twoTimeOrderSeminorm o J (fullLowReserve (d + 1)) b)
      (Finset.sum_nonneg fun _ _ ↦ normalizedSeminorm_nonneg _ _ _)
      (twoTimeOrderSeminorm_nonneg _ _ _ _) _ _ χ hχ hχcs hcut a hout hzero Q u v hstrong
    · intro ξ
      simpa only [norm_iteratedFDeriv_zero] using
        norm_iteratedFDeriv_multiplier_le_primitive_joint_budgets
          z δ χout χsource β hβ hm.1 hm.2 hcover hβbudget 0 (by omega) ξ
    · intro r hr x hx ξ hξ
      obtain ⟨y, hy⟩ := hm.2
      exact norm_elapsedSpatialAmplitude_le_orderSeminorm z δ hJ χout χsource β
        hcover r (hmap r hr) o _ b hb hbbudget hx hy hξ
  · have hz : (∀ x, χout x = 0) ∨ (∀ x, χsource x = 0) := by
      by_cases ho' : (tsupport χout).Nonempty
      · right
        intro x
        by_contra hx
        exact hm ⟨ho', x, subset_tsupport χsource hx⟩
      · left
        intro x
        by_contra hx
        exact ho' ⟨x, subset_tsupport χout hx⟩
    obtain ⟨R, hR, hlim⟩ := hstrong
    have he (j : ℕ) : R j = 0 := by
      apply Lp.ext
      filter_upwards [hR j, Lp.coeFn_zero (EuclideanSpace ℂ (Fin q)) 2 volume] with x hx hx0
      rw [hx, hx0]
      rcases hz with ho0 | hs0
      · simp [cutReverseRetardedFourier, reverseTimeFourierKernel, ho0]
      · simp [cutReverseRetardedFourier, hs0]
    have he0 : Q.adjoint (graphTestToLp u) = 0 := tendsto_nhds_unique hlim
      (by
        rw [show R = fun _ ↦ 0 from funext he]
        exact tendsto_const_nhds)
    rw [he0]
    rcases hz with ho0 | hs0
    · simp [reverseRetardedFrequency, reverseTimeFourierKernel, ho0]
    · have hv := graphTestToSchwartz_complexSourceMaskTest_eq_zero χsource hs hs0 v
      simp [hv, sourceInputFourierTransform]

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral
