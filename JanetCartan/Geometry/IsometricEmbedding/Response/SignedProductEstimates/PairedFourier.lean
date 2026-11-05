module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SourceBounds.PhysicalDiscrepancy.Negative
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.InactiveSource.Realization

/-!
# Frequency reflection of the actual angular source pair

Conjugation of the literal scalar physical Fourier operator reflects its symbol.
This identifies the second term of `physicalPairedSectorSum` without replacing
it by the first term or subtracting a second identity. Consumer: the signed
source angular defect in `app:ch_pairs:prop:pairs-lag-sum`, Steps 1–3.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
open MeasureTheory FourierTransform
open scoped JanetCartan.RegularSector.Realization
open JanetCartan
namespace JanetCartan.SignedProductEstimates
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect FourierIntegral.LowBounds
open RegularSector.Realization
variable {d r : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- Vector conjugation reflects the original physical Fourier integral
(`app:ch_regular_base:eq:energy-complete-residual`). -/
private theorem fourier_star_integral (u : E → V) (ξ : E) :
    𝓕 (fun y ↦ star (u y)) ξ = star (𝓕 u (-ξ)) := by
  simp only [Real.fourier_eq, Circle.smul_def, inner_neg_right, neg_neg]
  change _ = (starL' ℝ : V ≃L[ℝ] V) (∫ v : E, (Real.fourierChar (inner ℝ v ξ) : ℂ) • u v)
  rw [← (starL' ℝ : V ≃L[ℝ] V).integral_comp_comm]
  apply integral_congr_ae
  filter_upwards [] with y
  simp

/-- The same reflection identity on Lebesgue L², proved by density for the
actual physical source pair (`app:ch_regular_base:eq:energy-complete-residual`). -/
private theorem fourier_star_l2 (u : H) :
    (𝓕 (star u) : H) = star
      (Lp.compMeasurePreserving Neg.neg (Measure.measurePreserving_neg volume) (𝓕 u)) := by
  refine (SchwartzMap.denseRange_toLpCLM (F := V)
    (p := 2) ENNReal.ofNat_ne_top).induction_on u ?_ ?_
  · exact isClosed_eq (continuous_fourier.comp continuous_star)
      (continuous_star.comp
        ((Lp.isometry_compMeasurePreserving (Measure.measurePreserving_neg volume)).continuous.comp
          continuous_fourier))
  intro g
  let u : H := g.toLp 2
  have hu : Integrable (u : E → V) := g.integrable.congr (g.coeFn_toLp 2).symm
  have hstar : Integrable ((star u : H) : E → V) :=
    ((starL' ℝ : V ≃L[ℝ] V).toContinuousLinearMap.integrable_comp hu).congr
      (Lp.coeFn_star u).symm
  change (𝓕 (star u) : H) = star
    (Lp.compMeasurePreserving Neg.neg (Measure.measurePreserving_neg volume) (𝓕 u))
  apply Lp.ext
  filter_upwards [Localization.fourierTransform_coeFn_ae_integral_hilbert _ hstar,
    Lp.coeFn_star (Lp.compMeasurePreserving Neg.neg (Measure.measurePreserving_neg volume) (𝓕 u)),
    Lp.coeFn_compMeasurePreserving (𝓕 u) (Measure.measurePreserving_neg volume),
    (Measure.measurePreserving_neg (volume : Measure E)).quasiMeasurePreserving.ae
      (Localization.fourierTransform_coeFn_ae_integral_hilbert u hu)] with ξ hc hj hr hf
  rw [hc, Real.fourier_congr_ae (Lp.coeFn_star u) ξ]
  change 𝓕 (fun y ↦ star (u y)) ξ = _
  rw [fourier_star_integral, hj, Pi.star_apply, hr]
  exact congrArg star hf.symm

/-- The a.e. reflected Fourier representative retains the original measure
(`app:ch_regular_base:eq:energy-complete-residual`). -/
private theorem fourier_star_l2_ae (u : H) :
    (𝓕 (star u) : H) =ᵐ[volume] fun ξ ↦ star ((𝓕 u : H) (-ξ)) := by
  rw [fourier_star_l2]
  filter_upwards [Lp.coeFn_star
    (Lp.compMeasurePreserving Neg.neg (Measure.measurePreserving_neg volume) (𝓕 u)),
    Lp.coeFn_compMeasurePreserving (𝓕 u) (Measure.measurePreserving_neg volume)] with ξ hs hn
  rw [hs, Pi.star_apply, hn]
  rfl

/-- Whole-factor conjugation reflects the SAME real Fourier symbol. The
physical normalization `2πξ` and both orientations are retained; this supplies
the literal paired complement for `app:ch_pairs:prop:pairs-lag-sum`. -/
theorem boundedConjugate_scalarPhysicalFrequencyOperator_reflection
    (b : E → ℝ) (hb : Continuous b) (hbb : ∀ ξ, ‖b ξ‖ ≤ 1) :
    boundedConjugate (scalarPhysicalFrequencyOperator (r := r) b hb hbb) =
      scalarPhysicalFrequencyOperator (fun ξ ↦ b (-ξ))
        (hb.comp continuous_neg) (fun ξ ↦ hbb (-ξ)) := by
  ext1 u
  apply (Lp.fourierTransformₗᵢ E V).injective
  change (𝓕 (star (scalarPhysicalFrequencyOperator b hb hbb (star u))) : H) = _
  let T := scalarPhysicalFrequencyOperator (r := r) b hb hbb
  let Tn := scalarPhysicalFrequencyOperator (r := r) (fun ξ ↦ b (-ξ))
    (hb.comp continuous_neg) (fun ξ ↦ hbb (-ξ))
  have hfreq (b : E → ℝ) (hb : Continuous b) (hbb : ∀ ξ, ‖b ξ‖ ≤ 1) (u : H) :
      (𝓕 (scalarPhysicalFrequencyOperator b hb hbb u) : H) =ᵐ[volume]
        fun ξ ↦ (b ((2*Real.pi) • ξ) : ℂ) • (𝓕 u : H) ξ := by
    simp only [scalarPhysicalFrequencyOperator, ContinuousLinearMap.comp_apply,
      fourierInvCLM_apply, fourierCLM_apply, fourier_fourierInv_eq]
    exact sourceCutMultiplier_coeFn _ _ _ _
  apply Lp.ext
  filter_upwards [fourier_star_l2_ae (T (star u)),
    (Measure.measurePreserving_neg (volume : Measure E)).quasiMeasurePreserving.ae
      (hfreq b hb hbb (star u)),
    (Measure.measurePreserving_neg (volume : Measure E)).quasiMeasurePreserving.ae
      (fourier_star_l2_ae u),
    hfreq (fun ξ ↦ b (-ξ)) (hb.comp continuous_neg) (fun ξ ↦ hbb (-ξ)) u]
    with ξ hs ht hu hn
  change (𝓕 (star (T (star u))) : H) ξ = (𝓕 (Tn u) : H) ξ
  rw [hs, ht, hu, hn]
  simp only [smul_neg, neg_neg, star_smul, star_star, Complex.star_def, Complex.conj_ofReal]
end JanetCartan.SignedProductEstimates
