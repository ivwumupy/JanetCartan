module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Amplitude

/-!
# The original spatial amplitude is bounded on the multiplier support

The normalized carrier cover and elapsed chart inclusion used by
`PrimitiveRetarded` imply the pointwise bound needed for absolute convergence
of the uncut fixed-time Fourier kernel. Both order zero and order minus one
are covered by the same proof. Source: `app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction

open FourierIntegral FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
open PrimitiveProfiles SymbolBudgets
variable {d q : ℕ} {ι : Type*}
local notation "E" => Euclidean (d + 1)

/-- Evaluation of the original order-`-o` amplitude at a covered covector
is bounded by its original normalized seminorm. Consumer: uncut fixed-time
frequency integrability in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem norm_twoTimeAmplitude_le_orderSeminorm
    {J : Set (TwoTimePoint d)} (hJ : IsCompact J)
    (o N : ℕ) (b : TwoTimeAmplitude d q) (hb : ContDiff ℝ ∞ (jointAmplitude b))
    (hbudget : BoundedTwoTimeOrderSeminorm o J N b)
    {R : ℝ} (hR : 1 ≤ R) {p : TwoTimePoint d} (hp : p ∈ J) :
    ‖b p.1.1 p.1.2.1 p.1.2.2 (R • p.2)‖ ≤ twoTimeOrderSeminorm o J N b := by
  have hc : ContDiff ℝ N (twoTimeOrderField o R b) := by
    exact ((hb.comp (contDiff_fst.prodMk (contDiff_snd.const_smul R))).const_smul
      (R ^ o)).of_le (by simp)
  have h := norm_le_cNorm hJ hc hp
  change ‖(R ^ o) • b p.1.1 p.1.2.1 p.1.2.2 (R • p.2)‖ ≤ _ at h
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
  exact (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hR)).trans
    (h.trans (cNorm_twoTimeOrderField_le hbudget hR))

/-- The exact carrier cover and chart map from `PrimitiveRetarded` produce
the frequency bound on the original spatial amplitude. A source-support point
is used only to access that cover; when the source mask is identically zero,
the source-masked test action is zero. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem norm_elapsedSpatialAmplitude_le_orderSeminorm
    (z : ι → Point (d + 1)) (δ : ι → ℝ)
    {J : Set (TwoTimePoint d)} (hJ : IsCompact J)
    (χout χsource β : E → ℂ)
    (hcover : ∀ p ∈ (tsupport χout ×ˢ tsupport χsource) ×ˢ tsupport β,
      ∃ i, ∃ R : ℝ, 1 ≤ R ∧ ∃ v ∈ Metric.closedBall (z i) (δ i),
        p = (v.1, R • v.2) ∧ 1 + ‖p.2‖ ≤ R)
    (r : ℝ) (hmap : ∀ i, MapsTo (elapsedPoint r) (Metric.closedBall (z i) (δ i)) J)
    (o N : ℕ) (b : TwoTimeAmplitude d q) (hb : ContDiff ℝ ∞ (jointAmplitude b))
    (hbudget : BoundedTwoTimeOrderSeminorm o J N b)
    {x z₀ ξ : E} (hx : x ∈ tsupport χout) (hz₀ : z₀ ∈ tsupport χsource)
    (hξ : ξ ∈ tsupport β) :
    ‖b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)‖ ≤
      twoTimeOrderSeminorm o J N b := by
  obtain ⟨i, R, hR, v, hv, he, _⟩ := hcover ((x, z₀), ξ) ⟨⟨hx, hz₀⟩, hξ⟩
  have hxv : x = v.1.1 := congrArg (fun p : Point (d + 1) ↦ p.1.1) he
  have hξv : ξ = R • v.2 := congrArg Prod.snd he
  have h := norm_twoTimeAmplitude_le_orderSeminorm hJ o N b hb hbudget hR (hmap i hv)
  simpa only [elapsedPoint_eq, hxv, hξv, spatialPart_smul] using h

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
