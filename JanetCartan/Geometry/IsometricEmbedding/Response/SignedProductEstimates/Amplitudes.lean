module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.Sources
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial.Calculus
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# Full signed-product amplitude profiles

The Leibniz step of `app:ch_pairs:prop:pairs-lag-sum` uses the actual derivative
amplitudes, including their modulation and response terms. It also includes the
entire source cutoff. The existing total-order bilinear estimate gives one power
of the pair scale per derivative. The constants below precede that scale, the
sample family and every varying amplitude. These are source estimates, not
estimates for the response or its residual.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius

namespace JanetCartan.SignedProductEstimates

open RawPrimary.AmplitudeGrades.Polynomial

private def plusTensorBilinear (n N : ℕ) :
    Matrix (Fin N) (Fin n) ℂ →L[ℝ] Matrix (Fin N) (Fin n) ℂ →L[ℝ]
      Matrix (Fin n) (Fin n) ℂ :=
  (LinearMap.mk₂ ℝ (fun (A B : Matrix (Fin N) (Fin n) ℂ) ↦ symmetricBilinearTensor A B)
    symmetricBilinearTensor_add_left
    (by
      intro c A B
      change symmetricBilinearTensor ((c : ℂ) • A) B =
        (c : ℂ) • symmetricBilinearTensor A B
      exact symmetricBilinearTensor_smul_left _ _ _)
    symmetricBilinearTensor_add_right
    (by
      intro c A B
      change symmetricBilinearTensor A ((c : ℂ) • B) =
        (c : ℂ) • symmetricBilinearTensor A B
      exact symmetricBilinearTensor_smul_right _ _ _)).toContinuousBilinearMap

private def minusTensorBilinear (n N : ℕ) :
    Matrix (Fin N) (Fin n) ℂ →L[ℝ] Matrix (Fin N) (Fin n) ℂ →L[ℝ]
      Matrix (Fin n) (Fin n) ℂ :=
  (LinearMap.mk₂ ℝ (fun (A B : Matrix (Fin N) (Fin n) ℂ) ↦ symmetricBilinearTensor A (B.map conj))
    (fun _ _ _ ↦ symmetricBilinearTensor_add_left _ _ _)
    (by
      intro c A B
      change symmetricBilinearTensor ((c : ℂ) • A) (B.map conj) =
        (c : ℂ) • symmetricBilinearTensor A (B.map conj)
      exact symmetricBilinearTensor_smul_left _ _ _)
    (by
      intro A B C
      have he : (B + C).map conj = B.map conj + C.map conj := by ext i j; simp
      rw [he, symmetricBilinearTensor_add_right])
    (by
      intro c A B
      have he : (c • B).map conj = (c : ℂ) • B.map conj := by ext i j; simp
      rw [he, symmetricBilinearTensor_smul_right]
      rfl)).toContinuousBilinearMap

variable {n N : ℕ}

/-- The complete plus and minus tensor amplitudes inherit local smoothness
from the actual derivative amplitudes (`app:ch_pairs:lem:pairs-ledger`). The
consumer is the compact source-envelope construction. -/
theorem contDiffOn_signed_tensor_amplitudes
    {U : Set (Euclidean n)} {A B : Euclidean n → Matrix (Fin N) (Fin n) ℂ}
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) :
    ContDiffOn ℝ ∞ (fun x ↦ symmetricBilinearTensor (A x) (B x)) U ∧
      ContDiffOn ℝ ∞ (fun x ↦ symmetricBilinearTensor (A x) ((B x).map conj)) U :=
  ⟨(plusTensorBilinear n N).isBoundedBilinearMap.contDiff.comp_contDiffOn (hA.prodMk hB),
    (minusTensorBilinear n N).isBoundedBilinearMap.contDiff.comp_contDiffOn (hA.prodMk hB)⟩

/-- Constants for the full tensor-product jets of
`app:ch_pairs:prop:pairs-lag-sum`, Step 1. Both signed products use the same
profile before the varying scale and amplitudes. Only the original amplitude
jets are inputs; no bound on a signed product is assumed. -/
theorem exists_signed_tensor_jet_constants (C : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) :
    ∃ P : ℕ → ℝ, (∀ r, 0 ≤ P r) ∧
      ∀ (U : Set (Euclidean n)), IsOpen U → ∀ L : ℝ, 1 ≤ L →
      ∀ A B : Euclidean n → Matrix (Fin N) (Fin n) ℂ,
        ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
        (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r A x‖ ≤ C r * L ^ r) →
        (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r B x‖ ≤ C r * L ^ r) →
        ∀ x ∈ U, ∀ r,
          ‖iteratedFDeriv ℝ r (fun y ↦ symmetricBilinearTensor (A y) (B y)) x‖ ≤
              P r * L ^ r ∧
          ‖iteratedFDeriv ℝ r (fun y ↦ symmetricBilinearTensor (A y) ((B y).map conj)) x‖ ≤
              P r * L ^ r := by
  let P := productProfile (plusTensorBilinear n N) C C
  let M := productProfile (minusTensorBilinear n N) C C
  refine ⟨fun r ↦ max (P r) (M r), fun r ↦
    (productProfile_nonneg _ hC hC r).trans (le_max_left _ _), ?_⟩
  intro U hU L hL A B hAs hBs hA hB x hx r
  have hp := jet_bilinear_le (plusTensorBilinear n N) hU hAs hBs hx
    (b := 0) hL hC hC (hA x hx) (hB x hx) r
  have hm := jet_bilinear_le (minusTensorBilinear n N) hU hAs hBs hx
    (b := 0) hL hC hC (hA x hx) (hB x hx) r
  constructor
  · exact hp.trans (mul_le_mul_of_nonneg_right (le_max_left (P r) (M r))
      (pow_nonneg (zero_le_one.trans hL) r))
  · exact hm.trans (mul_le_mul_of_nonneg_right (le_max_right (P r) (M r))
      (pow_nonneg (zero_le_one.trans hL) r))

/-- The original source cutoff contributes to the fixed constants, with the
same total derivative power `L^r` for both complete tensor amplitudes
(`app:ch_pairs:prop:pairs-lag-sum`, Step 1). The constants are chosen before
the cutoff realization, amplitudes, scale, samples, target or finite history.
The resulting jets are the source-shell inputs for the fixed response. -/
theorem exists_cutoff_signed_tensor_jet_constants
    (X C : ℕ → ℝ) (hX : ∀ r, 0 ≤ X r) (hC : ∀ r, 0 ≤ C r) :
    ∃ P : ℕ → ℝ, (∀ r, 0 ≤ P r) ∧
      ∀ (U : Set (Euclidean n)), IsOpen U → ∀ L : ℝ, 1 ≤ L →
      ∀ (χ : Euclidean n → ℝ) (A B : Euclidean n → Matrix (Fin N) (Fin n) ℂ),
        ContDiffOn ℝ ∞ χ U → ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
        (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r χ x‖ ≤ X r * L ^ r) →
        (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r A x‖ ≤ C r * L ^ r) →
        (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r B x‖ ≤ C r * L ^ r) →
        ∀ x ∈ U, ∀ r,
          ‖iteratedFDeriv ℝ r (fun y ↦ χ y • symmetricBilinearTensor (A y) (B y)) x‖ ≤
              P r * L ^ r ∧
          ‖iteratedFDeriv ℝ r
            (fun y ↦ χ y • symmetricBilinearTensor (A y) ((B y).map conj)) x‖ ≤
              P r * L ^ r := by
  obtain ⟨P, hP, hproduct⟩ := exists_signed_tensor_jet_constants (n := n) (N := N) C hC
  let smulMap := (ContinuousLinearMap.lsmul ℝ ℝ :
    ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
  refine ⟨productProfile smulMap X P, productProfile_nonneg _ hX hP, ?_⟩
  intro U hU L hL χ A B hχ hAs hBs hχb hA hB x hx r
  have hp := (plusTensorBilinear n N).isBoundedBilinearMap.contDiff.comp_contDiffOn
    (hAs.prodMk hBs)
  have hm := (minusTensorBilinear n N).isBoundedBilinearMap.contDiff.comp_contDiffOn
    (hAs.prodMk hBs)
  constructor
  · exact jet_bilinear_le smulMap hU hχ hp hx (b := 0) hL hX hP
      (hχb x hx) (fun k ↦ (hproduct U hU L hL A B hAs hBs hA hB x hx k).1) r
  · exact jet_bilinear_le smulMap hU hχ hm hx (b := 0) hL hX hP
      (hχb x hx) (fun k ↦ (hproduct U hU L hL A B hAs hBs hA hB x hx k).2) r

end JanetCartan.SignedProductEstimates
