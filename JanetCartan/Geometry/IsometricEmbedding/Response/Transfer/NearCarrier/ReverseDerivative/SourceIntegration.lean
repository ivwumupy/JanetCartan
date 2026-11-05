module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ReverseDerivative.Phase
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Source integration by parts for the reverse near-carrier graph

The source integral in `app:ch_regular_base:eq:actual-adjoint-trade`, with the
averaged mixed matrix of `app:ch_response:eq:direct-envelope-profile`.
Only compact source support and primitive smoothness are used to remove boundary
terms. The inverse identity and phase gradient are needed only on that support.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.ReverseDerivative

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

/-- The source integration by parts required by
`app:ch_response:eq:direct-envelope-profile`. The test amplitude `g` can be
vector-valued and includes the datum and all physical masks. The derivative on
the right differentiates the inverse matrix as well as `g`. -/
theorem integral_oscillation_frequency_smul
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (y δ : Euclidean n) (j : Fin n)
    (B C : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (g : Euclidean n → F)
    (hS : ContDiff ℝ ∞ (fun x ↦ phaseIncrement S ζ ρ x δ))
    (hC : ∀ l, ContDiff ℝ ∞ (fun x ↦ C x j l))
    (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g)
    (hCB : ∀ x ∈ tsupport g, C x * B x = 1)
    (hgrad : ∀ x ∈ tsupport g, ∀ l,
      partialDeriv (fun z ↦ phaseIncrement S ζ ρ z δ) x l =
        (B x).mulVec (fun k ↦ δ k) l) :
    (∫ x, (oscillation S ζ ρ y x δ * Complex.I * (δ j : ℂ)) • g x) =
      ∑ l, ∫ x, oscillation S ζ ρ y x δ •
        partialDeriv (fun z ↦ (C z j l : ℂ) • g z) x l := by
  let e := fun x ↦ oscillation S ζ ρ y x δ
  let G := fun l x ↦ (C x j l : ℂ) • g x
  have he : ContDiff ℝ ∞ e :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.sub hS))).cexp
  have hG (l : Fin n) : ContDiff ℝ ∞ (G l) :=
    (Complex.ofRealCLM.contDiff.comp (hC l)).smul hg
  have hsG (l : Fin n) : HasCompactSupport (G l) := hgs.smul_left
  have hi (l : Fin n) : Integrable (fun x ↦ partialDeriv e x l • G l x) :=
    (((he.continuous_fderiv (by simp)).clm_apply continuous_const).smul
      (hG l).continuous).integrable_of_hasCompactSupport (hsG l).smul_left
  have hibp (l : Fin n) :
      (∫ x, e x • partialDeriv (G l) x l) =
        -(∫ x, partialDeriv e x l • G l x) := by
    apply integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (hi l)
    · exact (he.continuous.smul (((hG l).continuous_fderiv (by simp)).clm_apply
        continuous_const)).integrable_of_hasCompactSupport
          ((hsG l).fderiv_apply ℝ _).smul_left
    · exact (he.continuous.smul (hG l).continuous).integrable_of_hasCompactSupport
        (hsG l).smul_left
    · exact fun x _ ↦ he.differentiable (by simp) x
    · exact fun x _ ↦ (hG l).differentiable (by simp) x
  calc
    _ = ∫ x, -(∑ l, partialDeriv e x l • G l x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport g
      · rw [oscillation_phase_trade S ζ ρ y x δ j (B x) (C x) (hCB x hx)
          (hS.differentiable (by simp) x) (hgrad x hx)]
        simp only [neg_smul, Finset.sum_smul, G, smul_smul, e]
        congr 1
        apply Finset.sum_congr rfl
        intro l _
        rw [mul_comm]
      · have hz : g x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp only [G, hz, smul_zero, Finset.sum_const_zero, neg_zero]
    _ = -(∑ l, ∫ x, partialDeriv e x l • G l x) := by
      rw [integral_neg, integral_finsetSum _ (fun l _ ↦ hi l)]
    _ = _ := by simp only [Finset.sum_neg_distrib, hibp, e, G]

end JanetCartan.ResponseTransfer.ReverseDerivative
