module

public import JanetCartan.Analysis.PhysicalBernstein.FourierEstimate

/-!
# Physical Bernstein for the same real global increment

This proves paper-v2 `new:lem:bernstein(ii)` and the analytic input of
`main:eq:final-Cr` for Euclidean real vector-valued Schwartz increments.
The support, derivatives, and physical L² norm belong to the SAME global
function. No accuracy, stage, periodic extension, or derivative estimate is
an input. Fourier inversion and Plancherel are applied after the existing
norm-preserving complex inclusion.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace JanetCartan.PhysicalBernstein

variable {n N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The complex Hilbert-valued Euclidean estimate underlying the real
physical Bernstein theorem (`new:lem:bernstein(ii)`). The support variable
uses the physical covector `2πξ`, while the norm is Lebesgue L². -/
theorem norm_iteratedFDeriv_le_of_complex_fourier_support
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (f : SchwartzMap E F) {Λ : ℝ} (hΛ : 0 < Λ)
    (hs : ∀ ξ, Λ < ‖(2 * Real.pi) • ξ‖ → 𝓕 (f : E → F) ξ = 0)
    (r : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ r (f : E → F) x‖ ≤
      bernsteinConstant n r * Λ ^ ((r : ℝ) + (n : ℝ) / 2) * ‖f.toLp 2 volume‖ := by
  let g : SchwartzMap E F := 𝓕⁻ f
  have hg : ∀ ξ, Λ < ‖ξ‖ → g ξ = 0 := by
    intro ξ hξ
    change (𝓕⁻ f) ξ = 0
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
    apply hs (-ξ)
    have hπ : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
    calc
      Λ < ‖ξ‖ := hξ
      _ ≤ ‖(2 * Real.pi) • (-ξ)‖ := by
        rw [norm_smul, norm_neg, Real.norm_of_nonneg (by positivity)]
        nlinarith [norm_nonneg ξ]
  have hfourier : 𝓕 (g : E → F) = (f : E → F) := by
    rw [← SchwartzMap.fourier_coe]
    exact congrArg (fun h : SchwartzMap E F ↦ (h : E → F)) (fourier_fourierInv_eq f)
  have hnorm : ‖g.toLp 2 volume‖ = ‖f.toLp 2 volume‖ := by
    have h := SchwartzMap.norm_fourier_toL2_eq g
    simpa only [g, fourier_fourierInv_eq] using h.symm
  simpa only [hfourier, hnorm] using norm_iteratedFDeriv_fourier_le g hΛ hg r x

/-- Physical Bernstein for real Euclidean Schwartz increments. This is the
same-function estimate required by paper-v2 `new:lem:bernstein(ii)` and
`main:eq:final-Cr`, with the sharp exponent `r + n/2`. Its constant depends
only on dimension and derivative order, not on output dimension, bandwidth,
accuracy, or stage. -/
theorem norm_iteratedFDeriv_le
    (u : SchwartzMap E (EuclideanSpace ℝ (Fin N))) {Λ : ℝ} (hΛ : 0 < Λ)
    (hs : HasFourierSupport Λ u) (r : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ r (u : E → EuclideanSpace ℝ (Fin N)) x‖ ≤
      bernsteinConstant n r * Λ ^ ((r : ℝ) + (n : ℝ) / 2) * physicalL2Norm u := by
  let f : SchwartzMap E (EuclideanSpace ℂ (Fin N)) :=
    SchwartzMap.postcompCLM euclideanComplexInclusion u
  let L : EuclideanSpace ℝ (Fin N) →ₗᵢ[ℝ] EuclideanSpace ℂ (Fin N) :=
    ⟨euclideanComplexInclusion.toLinearMap, euclideanComplexInclusion_norm⟩
  have hderiv : ‖iteratedFDeriv ℝ r (f : E → EuclideanSpace ℂ (Fin N)) x‖ =
      ‖iteratedFDeriv ℝ r (u : E → EuclideanSpace ℝ (Fin N)) x‖ := by
    exact L.norm_iteratedFDeriv_comp_left (u.smooth ⊤).contDiffAt (by simp)
  have hnorm : ‖f.toLp 2 volume‖ = physicalL2Norm u := by
    rw [SchwartzMap.norm_toLp]
    unfold physicalL2Norm
    congr 1
    exact eLpNorm_congr_norm_ae f.continuous.aestronglyMeasurable
      u.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y ↦ euclideanComplexInclusion_norm (u y)))
  have hsupport : ∀ ξ, Λ < ‖(2 * Real.pi) • ξ‖ →
      𝓕 (f : E → EuclideanSpace ℂ (Fin N)) ξ = 0 := hs
  simpa only [hderiv, hnorm] using
    norm_iteratedFDeriv_le_of_complex_fourier_support f hΛ hsupport r x

end JanetCartan.PhysicalBernstein
