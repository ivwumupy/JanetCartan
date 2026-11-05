module

public import JanetCartan.Analysis.Sobolev.Local.Fourier.CoordinateWeakDerivative

/-!
# Genuine weak jets at the order-one endpoint

The first-order weak Fréchet derivative supplies a normalized finite weak jet
with exactly the sum of the function and derivative L² norms. This construction
is used by the Fourier-to-restriction H¹ comparison in
`app:ch_regular_base:eq:sector-theorem-residual` and
`app:ch_regular:thm:exact-correction`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Function Filter

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The normalized value and first derivative jet for `app:not:fourier`. -/
def firstWeakJet (f : E → F) (D : E → E →L[ℝ] F) :
    (j : ℕ) → E → E [×j]→L[ℝ] F
  | 0 => iteratedFDeriv ℝ 0 f
  | 1 => fun x ↦ (continuousMultilinearCurryFin1 ℝ E F).symm (D x)
  | _ + 2 => fun _ ↦ 0

/-- A genuine first weak derivative supplies an actual weak jet
through order one (`app:not:fourier`). -/
theorem hasWeakJetOn_firstWeakJet {f : E → F} {D : E → E →L[ℝ] F}
    (h : Mollification.HasWeakFDerivOn volume f D univ) :
    Mollification.HasWeakJetOn volume f (firstWeakJet f D) univ 1 := by
  refine ⟨rfl, fun j hj ↦ ?_⟩
  have hj0 : j = 0 := by omega
  subst j
  let L := (continuousMultilinearCurryFin0 ℝ E F).symm
    |>.toContinuousLinearEquiv.toContinuousLinearMap
  convert h.comp_clm_univ L using 1
  · rfl
  · ext x z w
    simp [firstWeakJet, L, continuousMultilinearCurryFin1_symm_apply]

omit [CompleteSpace F] in
/-- Every component of the constructed first jet is genuinely L²
(`app:not:fourier`). -/
theorem memLp_firstWeakJet {f : E → F} {D : E → E →L[ℝ] F} (hf : MemLp f 2 volume)
    (hD : MemLp D 2 volume) (j : ℕ) (hj : j ≤ 1) :
    MemLp (firstWeakJet f D j) 2 volume := by
  interval_cases j
  · exact (continuousMultilinearCurryFin0 ℝ E F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hf
  · exact (continuousMultilinearCurryFin1 ℝ E F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hD

omit [CompleteSpace F] in
/-- The first weak jet has precisely the sum of the value and derivative
L² operator norms (`app:not:fourier`). -/
theorem firstWeakJet_normSum {f : E → F} {D : E → E →L[ℝ] F} (hf : MemLp f 2 volume)
    (hD : MemLp D 2 volume) :
    (∑ j ∈ Finset.range 2, (eLpNorm (firstWeakJet f D j) 2 volume).toReal) =
      (eLpNorm f 2 volume).toReal + (eLpNorm D 2 volume).toReal := by
  have h0 : eLpNorm (firstWeakJet f D 0) 2 volume = eLpNorm f 2 volume := by
    apply eLpNorm_congr_norm_ae
      ((continuousMultilinearCurryFin0 ℝ E F).symm
        |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hf).aestronglyMeasurable
      hf.aestronglyMeasurable
    exact Eventually.of_forall fun x ↦ norm_iteratedFDeriv_zero
  have h1 : eLpNorm (firstWeakJet f D 1) 2 volume = eLpNorm D 2 volume := by
    apply eLpNorm_congr_norm_ae
      ((continuousMultilinearCurryFin1 ℝ E F).symm
        |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hD).aestronglyMeasurable
      hD.aestronglyMeasurable
    exact Eventually.of_forall fun x ↦
      (continuousMultilinearCurryFin1 ℝ E F).symm.norm_map _
  simp [Finset.sum_range_succ, h0, h1]

end JanetCartan.LocalSobolev
