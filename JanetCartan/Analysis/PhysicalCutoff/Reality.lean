module

public import JanetCartan.Analysis.PhysicalCutoff.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Reality and exact physical Fourier support

Paper-v2 §15, Step 6: evenness of the real symbol preserves the conjugate
symmetry of the Fourier transform of the original real Schwartz field.
Consequently the real-part construction discards nothing, and its Fourier
transform is exactly the prescribed radian multiplier.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap ComplexConjugate RealInnerProductSpace

namespace JanetCartan.PhysicalCutoff

variable {n N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "C" => EuclideanSpace ℂ (Fin N)
local notation "V" => EuclideanSpace ℝ (Fin N)

private theorem fourier_coordinate (f : 𝓢(E, C)) (ξ : E) (i : Fin N) :
    𝓕 f ξ i = 𝓕 (fun x ↦ f x i) ξ := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq, Real.fourier_eq,
    eval_integral_piLp ((Real.fourierIntegral_convergent_iff ξ).2 f.integrable).eval_piLp]
  rfl

private theorem fourierInv_coordinate (f : 𝓢(E, C)) (x : E) (i : Fin N) :
    𝓕⁻ f x i = 𝓕⁻ (fun ξ ↦ f ξ i) x := by
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg,
    Real.fourierInv_eq_fourier_neg]
  exact fourier_coordinate f (-x) i

/-- The original real field has conjugate-symmetric Fourier coordinates
(§15, Step 6). -/
theorem conj_fourier_complexify (u : 𝓢(E, V)) (ξ : E) (i : Fin N) :
    conj (𝓕 (complexify u) ξ i) = 𝓕 (complexify u) (-ξ) i := by
  simp only [fourier_coordinate, Real.fourier_eq, Circle.smul_def, smul_eq_mul,
    complexify_apply, euclideanComplexInclusion_apply, inner_neg_right, neg_neg]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp

/-- The actual truncated Fourier field retains conjugate symmetry
(§15, Step 6). -/
theorem conj_filteredFourier (R : ℝ) (u : 𝓢(E, V)) (ξ : E) (i : Fin N) :
    conj (filteredFourier R u ξ i) = filteredFourier R u (-ξ) i := by
  simp only [filteredFourier_apply, PiLp.smul_apply, symbol_neg]
  change conj ((symbol R ξ : ℂ) * 𝓕 (complexify u) ξ i) =
    (symbol R ξ : ℂ) * 𝓕 (complexify u) (-ξ) i
  simp only [map_mul, Complex.conj_ofReal, conj_fourier_complexify]

/-- The inverse transform of the actual filtered field is real coordinatewise
(§15, Step 6). -/
theorem conj_complexTruncate (R : ℝ) (u : 𝓢(E, V)) (x : E) (i : Fin N) :
    conj (complexTruncate R u x i) = complexTruncate R u x i := by
  change conj (𝓕⁻ (filteredFourier R u) x i) = 𝓕⁻ (filteredFourier R u) x i
  simp only [fourierInv_coordinate, Real.fourierInv_eq, Circle.smul_def, smul_eq_mul]
  rw [← integral_conj, ← integral_neg_eq_self
    (fun ξ : E ↦ (Real.fourierChar ⟪ξ, x⟫ : ℂ) * filteredFourier R u ξ i) volume]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [map_mul, conj_filteredFourier, inner_neg_left,
    AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

/-- Taking real part discards nothing: this is the SAME physical field
(§15, Step 6). -/
theorem complexify_truncate (R : ℝ) (u : 𝓢(E, V)) :
    complexify (truncate R u) = complexTruncate R u := by
  ext x i
  change ((complexTruncate R u x i).re : ℂ) = complexTruncate R u x i
  exact Complex.conj_eq_iff_re.mp (conj_complexTruncate R u x i)

/-- Exact Fourier identity for the norm-preserving complex inclusion of the
actual real Schwartz increment (§15, Step 6). -/
theorem fourier_truncate (R : ℝ) (u : 𝓢(E, V)) (ξ : E) :
    𝓕 (fun x ↦ euclideanComplexInclusion (truncate R u x)) ξ =
      symbol R ξ • 𝓕 (fun x ↦ euclideanComplexInclusion (u x)) ξ := by
  change 𝓕 (complexify (truncate R u)) ξ = symbol R ξ • 𝓕 (complexify u) ξ
  rw [complexify_truncate, fourier_complexTruncate, filteredFourier_apply]

/-- The constructed real increment is literally bandlimited in the shared
physical convention, with fixed outer multiplier constant `2` (§15, Step 6). -/
theorem hasFourierSupport_truncate {R : ℝ} (hR : 0 < R) (u : 𝓢(E, V)) :
    PhysicalBernstein.HasFourierSupport (2 * R) (truncate R u) := by
  intro ξ hξ
  rw [fourier_truncate, symbol_eq_zero hR hξ.le, zero_smul]

end JanetCartan.PhysicalCutoff
