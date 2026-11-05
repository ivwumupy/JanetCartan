module

public import JanetCartan.Analysis.Calculus.CompactParameterIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.Basic

/-! # Differentiation of the bounded frequency integral
For the correction following `app:ch_background:eq:bg-symbol`.
-/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction
variable {n : ℕ}
/-- Every joint physical derivative commutes with the compact frequency integral.
The consumer is the correction kernel estimate after `app:ch_background:eq:bg-symbol`.
Compactness supplies all local domination required for differentiation. -/
theorem iteratedFDeriv_frequencyIntegral {K : Set (Euclidean n)} (hK : IsCompact K)
    (j : ℕ) {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {f : (Euclidean n × Euclidean n) × Euclidean n → G} (hf : ContDiff ℝ ∞ f) (x : Euclidean n × Euclidean n) :
    iteratedFDeriv ℝ j (fun y ↦ ∫ v in K, f (y, v)) x =
      ∫ v in K, iteratedFDeriv ℝ j (fun y ↦ f (y, v)) x := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  induction j generalizing G with
  | zero =>
    let L := (continuousMultilinearCurryFin0 ℝ (Euclidean n × Euclidean n) G).symm
    exact (L.toContinuousLinearEquiv.integral_comp_comm _).symm
  | succ j ih =>
    let g : (Euclidean n × Euclidean n) × Euclidean n → Euclidean n × Euclidean n →L[ℝ] G :=
      fun p ↦ fderiv ℝ (fun y ↦ f (y, p.2)) p.1
    have hg : ContDiff ℝ ∞ g := by
      apply contDiffOn_univ.mp
      simpa only [univ_prod_univ] using
        contDiffOn_parameterFDeriv (U := univ) (V := univ) isOpen_univ isOpen_univ
          hf.contDiffOn
    have he : fderiv ℝ (fun y ↦ ∫ v in K, f (y, v)) =
        fun y ↦ ∫ v in K, g (y, v) := by
      funext y
      exact fderiv_compactParameterIntegral (U := univ) (V := univ)
        isOpen_univ isOpen_univ hK (subset_univ K) hf.contDiffOn (mem_univ y)
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, he, ih hg]
    let L := (continuousMultilinearCurryRightEquiv' ℝ j (Euclidean n × Euclidean n) G).symm
    change L (∫ v in K, iteratedFDeriv ℝ j (fun y ↦ g (y, v)) x) = _
    calc
      _ = ∫ v in K, L (iteratedFDeriv ℝ j (fun y ↦ g (y, v)) x) :=
        (ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ)
          (E := (Euclidean n × Euclidean n) [×j]→L[ℝ] Euclidean n × Euclidean n →L[ℝ] G)
          (F := (Euclidean n × Euclidean n) [×(j + 1)]→L[ℝ] G) L.toContinuousLinearEquiv _).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with v
        exact (iteratedFDeriv_succ_eq_comp_right (f := fun y ↦ f (y, v))).symm

/-- Joint smoothness of the physical jets gives measurable, integrable frequency
sections for the correction kernel (`app:ch_background:eq:bg-symbol`). -/
theorem contDiff_frequencyJet (r : ℕ)
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : (Euclidean n × Euclidean n) × Euclidean n → G} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      iteratedFDeriv ℝ r (fun y ↦ f (y, p.2)) p.1) := by
  induction r generalizing G with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ (Euclidean n × Euclidean n) G).symm.contDiff.comp hf
  | succ r ih =>
    let g : (Euclidean n × Euclidean n) × Euclidean n → (Euclidean n × Euclidean n) →L[ℝ] G :=
      fun p ↦ fderiv ℝ (fun y ↦ f (y, p.2)) p.1
    have hg : ContDiff ℝ ∞ g := by
      apply contDiffOn_univ.mp
      simpa only [univ_prod_univ] using
        contDiffOn_parameterFDeriv (U := univ) (V := univ) isOpen_univ isOpen_univ hf.contDiffOn
    simpa only [iteratedFDeriv_succ_eq_comp_right, Function.comp_def, g] using
      (continuousMultilinearCurryRightEquiv' ℝ r (Euclidean n × Euclidean n) G).symm.contDiff.comp
        (ih hg)

/-- Absolute integrability of every physical jet on the fixed frequency ball;
no domination is postulated (`app:ch_background:eq:bg-symbol`). -/
theorem integrableOn_frequencyJet (r : ℕ)
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : (Euclidean n × Euclidean n) × Euclidean n → G} (hf : ContDiff ℝ ∞ f)
    {K : Set (Euclidean n)} (hK : IsCompact K) (x : Euclidean n × Euclidean n) :
    IntegrableOn (fun k ↦ iteratedFDeriv ℝ r (fun y ↦ f (y, k)) x) K := by
  exact ((contDiff_frequencyJet r hf).continuous.comp
    (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hK

end JanetCartan.ContinuumRow.TransportKernel
