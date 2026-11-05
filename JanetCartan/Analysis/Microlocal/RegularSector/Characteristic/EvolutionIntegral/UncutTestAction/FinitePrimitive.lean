module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.FiniteBudget

/-!
# Uncut retarded identification with all finite analytic inputs discharged

The same normalized multiplier reserve, spatial symbol budget and carrier map
as `PrimitiveRetarded` supply the bounds used by uncut inversion and cutoff
removal. Only its exact cutoff-preservation and strong-limit conclusions are
retained as operator hypotheses. The construction of that operator and its
integer estimates remain with the parent. Source:
`app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
open FourierIntegral FullLowBounds FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
open PrimitiveProfiles SymbolBudgets KernelIdentification LowBounds.FrequencyCutoff
variable {d q : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => Euclidean (d + 1)

/-- The parent's SAME retarded strong limit is the original uncut test action
from its original finite symbol budgets. The multiplier derivative bounds,
spatial amplitude bound, integrability, pointwise Fourier inversion and cutoff
passage are all discharged here, including empty-mask cases. `hcut` and
`hstrong` are precisely the conclusions of
`exists_retardedOperator_of_primitive_data`; no successful realization record,
uncut action or integrated Sobolev estimate is an input. The supported phase
continuity is produced there by its primitive phase smoothness. Source:
`app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem retardedOperator_eq_uncutPhysicalIntegral_of_primitive_budgets
    (z : ι → Point (d + 1)) (δ : ι → ℝ)
    {J : Set (TwoTimePoint d)} (hJ : IsCompact J)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ContDiff ℝ ∞ (jointAmplitude b))
    (ho : Continuous χout) (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
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
    (Q : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q) (u : graphTestSpace (d + 1) q)
    (hstrong : ∃ R : ℕ → SpacetimeL2 d q,
      (∀ j, R j =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (cutRetardedPhysical Ψ b χout χsource β (χ j) hs hβ (hχ j) (hχcs j) a u x)) ∧
      Tendsto R atTop (𝓝 (Q (graphTestToLp u)))) :
    Q (graphTestToLp u) =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (retardedPhysicalIntegral Ψ b χout χsource β hs a u x) := by
  by_cases hm : (tsupport χout).Nonempty ∧ (tsupport χsource).Nonempty
  · have hbs : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
        ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
          b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0-r), (spatialPart x, spatialPart ξ)) := by
      intro r _ x _ ξ _
      exact (hb.comp ((contDiff_fst.fst.prodMk
        (contDiff_fst.snd.prodMk contDiff_snd.fst)).prodMk contDiff_snd.snd)).continuous.continuousAt
    apply retardedOperator_eq_uncutPhysicalIntegral_of_strongLimit Ψ b χout χsource β Δ hΔ
      hΨ hbs ho hs hβ (fun k ↦ ∑ i, normalizedSeminorm
        (Metric.closedBall (z i) (δ i)) k (jointMultiplier β))
      (norm_iteratedFDeriv_multiplier_le_primitive_joint_budgets
        z δ χout χsource β hβ hm.1 hm.2 hcover hβbudget)
      hocs hscs (twoTimeOrderSeminorm o J (fullLowReserve (d + 1)) b)
      (twoTimeOrderSeminorm_nonneg _ _ _ _) _ χ hχ hχcs hcut a hout hzero Q u hstrong
    intro r hr x hx ξ hξ
    obtain ⟨z₀, hz₀⟩ := hm.2
    exact norm_elapsedSpatialAmplitude_le_orderSeminorm z δ hJ χout χsource β hcover r
      (hmap r hr) o (fullLowReserve (d + 1)) b hb hbbudget hx hz₀ hξ
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
    obtain ⟨s, _hs, hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
    filter_upwards [hsub, ae_all_iff.mpr hR] with x hx he
    have hzeroR (j : ℕ) : R j x = 0 := by
      rw [he j, cutRetardedPhysical_eq_zero_of_mask Ψ b χout χsource β (χ j)
        hs hβ (hχ j) (hχcs j) a u hz x]
      rfl
    have hx0 : Q (graphTestToLp u) x = 0 := tendsto_nhds_unique hx
      (by simpa only [hzeroR] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦
        (0 : EuclideanSpace ℂ (Fin q))) atTop (𝓝 0)))
    rw [hx0, retardedPhysicalIntegral_eq_zero_of_mask Ψ b χout χsource β hs a u hz x]
    rfl

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
