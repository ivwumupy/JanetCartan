module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.NoncomparableGeometry
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.NoncomparableEstimates

/-!
# Physical phase inputs for graph shell decay

The consumer is `exists_regularizedShellKernel_dyadic_bounds` in the proof of
`app:ch_regular:eq:chain-tail`. Homogeneity connects its input-normalized phase
to the literal physical phase, so the noncomparable gap is proved from covector
comparison rather than assumed. Both orientations retain all three covectors.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.FiniteChain.Graph.KernelEstimates
open Noncomparable NoncomparableGeometry
variable {n : ℕ}

/-- The normalized shell phase is the literal physical base phase divided by
the larger radius (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem normalizedBasePhase_eq_physical (backward : Bool) (ρ R : ℝ)
    (Φ φ : Euclidean n → Euclidean n → ℝ) (x y : Euclidean n)
    (w : Euclidean n × Euclidean n × Euclidean n)
    (hhom : ∀ u, Φ u (ρ • w.1) = ρ * φ u w.1) :
    normalizedBasePhase backward ρ R φ x y w =
      R⁻¹ • basePhase backward Φ x y (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2) := by
  funext b
  have he : basePhase backward Φ x y (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2) b =
      ρ * jointPhase backward φ x y (b, w) := by
    cases backward
    · exact forwardPhase_rescale Φ φ ρ x y b.1 b.2 w.1 w.2.1 w.2.2 (hhom b.1)
    · exact reversePhase_rescale Φ φ ρ x y b.1 b.2 w.1 w.2.1 w.2.2 (hhom b.1)
  simp only [Pi.smul_apply, smul_eq_mul, he, normalizedBasePhase, div_eq_mul_inv]
  ring

/-- Primitive physical covector comparison discharges the normalized gap of
shell integration by parts (`app:ch_regular:eq:chain-tail`). -/
theorem normalizedBasePhase_gap_of_comparison {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eu : OrthonormalBasis ι ℝ (Euclidean n)) (ez : OrthonormalBasis κ ℝ (Euclidean n))
    (backward : Bool) (ρ : ℝ) {R c C : ℝ} (hR : 0 < R) (hc : 0 < c)
    (Φ φ : Euclidean n → Euclidean n → ℝ) (x y : Euclidean n)
    (w : Euclidean n × Euclidean n × Euclidean n) (b : Euclidean n × Euclidean n)
    (g : Euclidean n) (hhom : ∀ u, Φ u (ρ • w.1) = ρ * φ u w.1)
    (hφ : DifferentiableAt ℝ (fun u => Φ u (ρ • w.1)) b.1)
    (hg : fderiv ℝ (fun u => Φ u (ρ • w.1)) b.1 = innerSL ℝ g)
    (hlow : c * ‖ρ • w.1‖ ≤ ‖g‖) (hhigh : ‖g‖ ≤ C * ‖ρ • w.1‖)
    (hsep : OutsideInputAnnuli c C (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2))
    (hlarge : R ≤ largestFrequency (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2)) :
    gapCoefficient c C ≤ Localization.phaseGradientSquare (baseDirections eu ez)
      (normalizedBasePhase backward ρ R φ x y w) b := by
  rw [normalizedBasePhase_eq_physical backward ρ R Φ φ x y w hhom]
  exact basePhase_normalized_gradient_gap eu ez backward Φ x y _ _ _ g b
    hφ hg hc hR hlow hhigh hsep hlarge

/-- The first physical derivative bound scales to the normalized coefficient
bound needed by shell integration by parts (`app:ch_regular:eq:chain-tail`). -/
theorem norm_fderiv_normalizedBasePhase_le (backward : Bool) (ρ : ℝ) {R G : ℝ}
    (hR : 0 < R) (Φ φ : Euclidean n → Euclidean n → ℝ) (x y : Euclidean n)
    (w : Euclidean n × Euclidean n × Euclidean n) (b : Euclidean n × Euclidean n)
    (hhom : ∀ u, Φ u (ρ • w.1) = ρ * φ u w.1)
    (hφ : DifferentiableAt ℝ
      (basePhase backward Φ x y (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2)) b)
    (hbound : ‖fderiv ℝ
      (basePhase backward Φ x y (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2)) b‖ ≤ R * G) :
    ‖fderiv ℝ (normalizedBasePhase backward ρ R φ x y w) b‖ ≤ G := by
  rw [normalizedBasePhase_eq_physical backward ρ R Φ φ x y w hhom,
    fderiv_const_smul hφ, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hR).le]
  exact (mul_le_mul_of_nonneg_left hbound (inv_pos.mpr hR).le).trans_eq
    (by field_simp)

/-- Physical higher phase grades give normalized grades without an additional
power of the integration order (`app:ch_regular:eq:high-phase`). -/
theorem norm_iteratedFDeriv_normalizedBasePhase_le (backward : Bool) (ρ : ℝ)
    {R H : ℝ} (hR : 0 < R) (Φ φ : Euclidean n → Euclidean n → ℝ) (x y : Euclidean n)
    (w : Euclidean n × Euclidean n × Euclidean n) (b : Euclidean n × Euclidean n)
    (j : ℕ) (hhom : ∀ u, Φ u (ρ • w.1) = ρ * φ u w.1)
    (hφ : ContDiffAt ℝ j
      (basePhase backward Φ x y (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2)) b)
    (hbound : ‖iteratedFDeriv ℝ j
      (basePhase backward Φ x y (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2)) b‖ ≤ R * H) :
    ‖iteratedFDeriv ℝ j (normalizedBasePhase backward ρ R φ x y w) b‖ ≤ H := by
  rw [normalizedBasePhase_eq_physical backward ρ R Φ φ x y w hhom,
    iteratedFDeriv_const_smul_apply hφ, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hR).le]
  exact (mul_le_mul_of_nonneg_left hbound (inv_pos.mpr hR).le).trans_eq
    (by field_simp)

end JanetCartan.FiniteChain.Graph.KernelEstimates
