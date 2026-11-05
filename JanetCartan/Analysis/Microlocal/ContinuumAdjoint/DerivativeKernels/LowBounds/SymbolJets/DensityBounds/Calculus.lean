module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets.PrimitiveBounds

/-!
# Cancellation of the half-order factors in finite density jets

This is the product step of `app:ch_background:prop:bg-adjoint`. The estimates
on individual composed factors are conclusions of the primitive composition
and reciprocal determinant calculations; they are not primitive hypotheses
for the final density theorem.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol

open NormalComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite complex product estimate used for the two half-order amplitudes
and the squared regularizer in `app:ch_background:prop:bg-adjoint`. -/
theorem norm_iteratedFDeriv_complexProduct_le
    {U : Set E} (hU : IsOpen U) {f g : E → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {N : ℕ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {p : E} (hp : p ∈ U)
    (hfjet : ∀ i ≤ N, ‖iteratedFDeriv ℝ i f p‖ ≤ A)
    (hgjet : ∀ i ≤ N, ‖iteratedFDeriv ℝ i g p‖ ≤ B)
    {j : ℕ} (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j (fun q ↦ f q * g q) p‖ ≤ (2 : ℝ)^N * A * B := by
  apply (InverseChartJet.norm_iteratedFDeriv_bilinear_on_open_le
    (ContinuousLinearMap.mul ℝ ℂ) (ContinuousLinearMap.opNorm_mul_le ℝ ℂ)
    hU hf hg hA hp j (fun i hi ↦ hfjet i (hi.trans hj))
    (fun i hi ↦ hgjet i (hi.trans hj))).trans
  gcongr
  norm_num

/-- Every derivative in the finite reserve retains the cancellation
`(sqrt r)^2/r = 1`. This is the quantitative product step for
`app:ch_background:prop:bg-adjoint`, including two regularizer factors and
the complex conjugate in the left amplitude. -/
theorem norm_iteratedFDeriv_weightedPair_le
    {U : Set E} (hU : IsOpen U) {d : E → ℝ} {u f g : E → ℂ}
    (hd : ContDiffOn ℝ ∞ d U) (hu : ContDiffOn ℝ ∞ u U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {N : ℕ} {D M A r : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hr : 0 < r) {p : E} (hp : p ∈ U)
    (hdjet : ∀ i ≤ N, ‖iteratedFDeriv ℝ i d p‖ ≤ D / r)
    (hujet : ∀ i ≤ N, ‖iteratedFDeriv ℝ i u p‖ ≤ M)
    (hfjet : ∀ i ≤ N, ‖iteratedFDeriv ℝ i f p‖ ≤ A * Real.sqrt r)
    (hgjet : ∀ i ≤ N, ‖iteratedFDeriv ℝ i g p‖ ≤ A * Real.sqrt r)
    {j : ℕ} (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j (fun q ↦ d q • (u q ^ 2 * (star (f q) * g q))) p‖ ≤
      ((2 : ℝ)^N)^4 * D * M^2 * A^2 := by
  let P : ℝ := (2 : ℝ)^N
  have hP : 0 ≤ P := by positivity
  have hAr : 0 ≤ A * Real.sqrt r := mul_nonneg hA (Real.sqrt_nonneg _)
  have hu2 : ContDiffOn ℝ ∞ (fun q ↦ u q ^ 2) U := hu.pow 2
  have hfc : ContDiffOn ℝ ∞ (fun q ↦ star (f q)) U :=
    Complex.conjCLE.contDiff.comp_contDiffOn hf
  have hu2jet (i) (hi : i ≤ N) :
      ‖iteratedFDeriv ℝ i (fun q ↦ u q ^ 2) p‖ ≤ P * M * M := by
    simpa only [pow_two] using
      norm_iteratedFDeriv_complexProduct_le hU hu hu hM hM hp hujet hujet hi
  have hfgjet (i) (hi : i ≤ N) :
      ‖iteratedFDeriv ℝ i (fun q ↦ star (f q) * g q) p‖ ≤
        P * (A * Real.sqrt r) * (A * Real.sqrt r) := by
    apply norm_iteratedFDeriv_complexProduct_le hU hfc hg hAr hAr hp _ hgjet hi
    intro k hk
    exact (Complex.conjLIE.norm_iteratedFDeriv_comp_left f p k).trans_le (hfjet k hk)
  have hprod (i) (hi : i ≤ N) :
      ‖iteratedFDeriv ℝ i (fun q ↦ u q ^ 2 * (star (f q) * g q)) p‖ ≤
        P * (P * M * M) * (P * (A * Real.sqrt r) * (A * Real.sqrt r)) :=
    norm_iteratedFDeriv_complexProduct_le hU hu2 (hfc.mul hg)
      (by positivity) (by positivity) hp hu2jet hfgjet hi
  have hbound := InverseChartJet.norm_iteratedFDeriv_bilinear_on_open_le
    (ContinuousLinearMap.lsmul ℝ ℝ) ContinuousLinearMap.opNorm_lsmul_le
    hU hd (hu2.mul (hfc.mul hg)) (div_nonneg hD hr.le) hp j
    (fun i hi ↦ hdjet i (hi.trans hj)) (fun i hi ↦ hprod i (hi.trans hj))
  apply hbound.trans
  calc
    _ ≤ P * (D / r) *
        (P * (P * M * M) * (P * (A * Real.sqrt r) * (A * Real.sqrt r))) := by
      gcongr
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
    _ = P^4 * D * M^2 * A^2 := by
      have hs := Real.sq_sqrt hr.le
      field_simp
      rw [hs]
      ring

end JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol
