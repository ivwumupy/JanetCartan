module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.FullNormalKernel.Series

/-!
# Fourier expansion inside the normal kernel

The Fubini and Fourier summation step of
`app:ch_osc:eq:two-position-normal-bound` in `paper.tex`. These intermediate
lemmas assume integrability of the kernel weight; the final compact-kernel
theorem must discharge that premise.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff

namespace JanetCartan.AmplitudeBound

variable {d : ℕ} {U : Type*} [MeasurableSpace U] {μ : Measure U}

/-- The literal full normal kernel acting on a function, in the integration
order displayed in `app:ch_osc:eq:two-position-normal-bound`. -/
def fullNormalAmplitudeKernel
    (t : EuclideanSpace ℝ (Fin d) → U → ℂ)
    (c : U → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (g : U → ℂ) (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (x : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ∫ y, (∫ u, t x u * c u (pairedPosition x y) * star (t y u) * g u ∂μ) * f y

/-- Fourier expansion commutes with the full normal integral when its compact
kernel weight is integrable (`app:ch_osc:eq:two-position-normal-bound`).
Both applications of Fubini are justified by that integrability and the
physical coefficient bounds. -/
theorem hasSum_fullNormalAmplitudeKernel_of_integrable_weight [SFinite μ]
    (t : EuclideanSpace ℝ (Fin d) → U → ℂ)
    (c : U → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hc : StronglyMeasurable (Function.uncurry c)) (hd : 0 < d)
    {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
    (hs : ∀ u, SupportedInCenteredBox R (c u)) (hf : ∀ u, ContDiff ℝ ∞ (c u))
    {A : ℝ} (hzero : ∀ u z, ‖c u z‖ ≤ A)
    (hderiv : ∀ u i z,
      ‖euclideanCoordinateDerivList (List.replicate (2 * (d + 1)) i) (c u) z‖ ≤ A)
    (g : U → ℂ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (x : EuclideanSpace ℝ (Fin d))
    (hq : Integrable
      (fun p : EuclideanSpace ℝ (Fin d) × U ↦ t x p.2 * star (t p.1 p.2) * g p.2 * f p.1)
      (volume.prod μ)) :
    HasSum (fun k ↦ ∫ u, (∫ y,
      t x u * boxAmplitudeFourierTerm (c u) ℓ k x y * star (t y u) * g u * f y) ∂μ)
      (fullNormalAmplitudeKernel (μ := μ) t c g f x) := by
  let b : EuclideanSpace ℝ (Fin d) × U → EuclideanSpace ℝ (Fin (2 * d)) → ℂ :=
    fun p ↦ c p.2
  have hb : StronglyMeasurable (Function.uncurry b) :=
    hc.comp_measurable (measurable_fst.snd.prodMk measurable_snd)
  let q : EuclideanSpace ℝ (Fin d) × U → ℂ :=
    fun p ↦ t x p.2 * star (t p.1 p.2) * g p.2 * f p.1
  let F : (Fin (2 * d) → ℤ) → EuclideanSpace ℝ (Fin d) × U → ℂ :=
    fun k p ↦ boxAmplitudeFourierTerm (c p.2) ℓ k x p.1
  have hF (k) : StronglyMeasurable (F k) :=
    stronglyMeasurable_boxAmplitudeFourierTerm b hb ℓ k measurable_const measurable_fst
  have hFb (k) (p : EuclideanSpace ℝ (Fin d) × U) : ‖F k p‖ ≤
      (smoothCoefficientConstant d * (boxDerivativeFactor d ℓ * A)) * twoPositionWeight d k :=
    norm_boxAmplitudeFourierTerm_le hd hℓ hR (hs p.2) (hf p.2)
      (hzero p.2) (hderiv p.2) k x p.1
  have hFi (k) : Integrable (fun p ↦ F k p * q p) (volume.prod μ) :=
    hq.bdd_mul (hF k).aestronglyMeasurable (Eventually.of_forall (hFb k))
  have hrec (p : EuclideanSpace ℝ (Fin d) × U) :
      (∑' k, F k p) = c p.2 (pairedPosition x p.1) :=
    (hasSum_boxAmplitude_expansion hd hℓ hR (hs p.2) (hf p.2)
      (hzero p.2) (hderiv p.2) x p.1).tsum_eq
  have hcm : StronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin d) × U ↦ c p.2 (pairedPosition x p.1)) := by
    have hm : StronglyMeasurable (fun p ↦ ∑' k, F k p) := StronglyMeasurable.tsum hF
    simpa only [hrec] using hm
  have hci : Integrable (fun p ↦ c p.2 (pairedPosition x p.1) * q p) (volume.prod μ) :=
    hq.bdd_mul hcm.aestronglyMeasurable (Eventually.of_forall fun p ↦ hzero p.2 _)
  have hsum := hasSum_integral_boxAmplitude_expansion (μ := volume.prod μ) b hb hd hℓ hR
    (fun p ↦ hs p.2) (fun p ↦ hf p.2) (fun p ↦ hzero p.2) (fun p ↦ hderiv p.2)
    (x := fun _ ↦ x) (y := Prod.fst) measurable_const measurable_fst hq
  have hterm (k) : (∫ p, F k p * q p ∂volume.prod μ) =
      ∫ u, (∫ y, t x u * boxAmplitudeFourierTerm (c u) ℓ k x y *
        star (t y u) * g u * f y) ∂μ := by
    rw [integral_prod_symm _ (hFi k)]
    congr 1
    funext u
    congr 1
    funext y
    dsimp [F, q]
    ring
  have hlimit : (∫ p, c p.2 (pairedPosition x p.1) * q p ∂volume.prod μ) =
      fullNormalAmplitudeKernel (μ := μ) t c g f x := by
    rw [integral_prod _ hci]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    dsimp only
    rw [← integral_mul_const]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro u
    dsimp [q]
    ring
  change HasSum (fun k ↦ ∫ p, F k p * q p ∂volume.prod μ)
    (∫ p, c p.2 (pairedPosition x p.1) * q p ∂volume.prod μ) at hsum
  simpa only [hterm, hlimit] using hsum

end JanetCartan.AmplitudeBound
