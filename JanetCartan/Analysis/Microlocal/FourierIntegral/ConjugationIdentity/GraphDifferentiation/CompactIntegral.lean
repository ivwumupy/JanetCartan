module

public import JanetCartan.Analysis.Calculus.CompactParameterIntegral
public import JanetCartan.Analysis.Microlocal.FourierIntegral.Differential
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Compact integrals for the direct graph identity

Local common compact support supplies every integrability and differentiation
hypothesis needed by `physicalOperator_graphOperator` in
`app:ch_regular_base:eq:direct-graph-identity`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.GraphDifferentiation

variable {n r : ℕ} {Z F : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z] [BorelSpace Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure Z} [IsFiniteMeasureOnCompacts μ]
  {U : Set (Euclidean n)} {K : Set Z} {f : Euclidean n × Z → F}

omit [NormedSpace ℝ Z] [NormedSpace ℝ F] in
/-- Compact support gives integrability of each output section, for
`app:ch_regular_base:eq:direct-graph-identity`. -/
theorem integrable_section (hK : IsCompact K)
    (hf : ContinuousOn f (U ×ˢ univ))
    (hs : ∀ x ∈ U, ∀ z ∉ K, f (x, z) = 0) {x : Euclidean n} (hx : x ∈ U) :
    Integrable (fun z ↦ f (x, z)) μ := by
  have hc : Continuous (fun z ↦ f (x, z)) := continuousOn_univ.mp
    (hf.comp (continuous_const.prodMk continuous_id).continuousOn (by simp [hx]))
  apply hc.integrable_of_hasCompactSupport
  exact hK.of_isClosed_subset (isClosed_tsupport _) (closure_minimal
    (fun z hz ↦ by by_contra hn; exact hz (hs x hx z hn)) hK.isClosed)

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z] [BorelSpace Z] in
/-- Output derivatives vanish outside the same frequency/source carrier in
`app:ch_regular_base:eq:direct-graph-identity`. -/
theorem fderiv_section_eq_zero (hU : IsOpen U)
    (hs : ∀ x ∈ U, ∀ z ∉ K, f (x, z) = 0) {x : Euclidean n} (hx : x ∈ U)
    {z : Z} (hz : z ∉ K) : fderiv ℝ (fun y ↦ f (y, z)) x = 0 := by
  have he : (fun y ↦ f (y, z)) =ᶠ[𝓝 x] fun _ ↦ (0 : F) := by
    filter_upwards [hU.mem_nhds hx] with y hy using hs y hy z hz
  rw [he.fderiv_eq]
  simp

/-- Differentiation through the full integral follows from the compact carrier
lemma; no domination or derivative-interchange premise is added
(`app:ch_regular_base:eq:direct-graph-identity`). -/
theorem hasFDerivAt_integral [CompleteSpace F] (hU : IsOpen U) (hK : IsCompact K)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ))
    (hs : ∀ x ∈ U, ∀ z ∉ K, f (x, z) = 0) {x : Euclidean n} (hx : x ∈ U) :
    HasFDerivAt (fun y ↦ ∫ z, f (y, z) ∂μ)
      (∫ z, fderiv ℝ (fun y ↦ f (y, z)) x ∂μ) x := by
  let : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have he : (fun y ↦ ∫ z, f (y, z) ∂μ) =ᶠ[𝓝 x]
      fun y ↦ ∫ z in K, f (y, z) ∂μ := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (hs y hy)).symm
  apply he.hasFDerivAt_iff.mpr
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun z hz ↦ fderiv_section_eq_zero hU hs hx hz)]
  exact hasFDerivAt_compactParameterIntegral hU isOpen_univ hK (subset_univ _) hf hx

/-- The finite-dimensional matrix action used to move coefficients through the
literal integral in `app:ch_regular_base:eq:direct-graph-identity`. -/
def matrixAction (M : Matrix (Fin r) (Fin r) ℂ) : (Fin r → ℂ) →L[ℂ] (Fin r → ℂ) :=
  (Matrix.mulVecLin M).toContinuousLinearMap

/-- Integrability of the differentiated integrand in the direct graph identity. -/
theorem integrable_physicalOperator (hU : IsOpen U) (hK : IsCompact K)
    {f : Euclidean n × Z → Fin r → ℂ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ))
    (hs : ∀ x ∈ U, ∀ z ∉ K, f (x, z) = 0)
    (A : Euclidean n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (B : Euclidean n → Matrix (Fin r) (Fin r) ℂ) {x : Euclidean n} (hx : x ∈ U) :
    Integrable (fun z ↦ physicalOperator A B (fun y ↦ f (y, z)) x) μ := by
  have hd := integrable_section (μ := μ) hK
    (contDiffOn_parameterFDeriv hU isOpen_univ hf).continuousOn
    (fun y hy z hz ↦ fderiv_section_eq_zero hU hs hy hz) hx
  have hv := integrable_section (μ := μ) hK hf.continuousOn hs hx
  unfold physicalOperator
  refine Integrable.smul (-Complex.I) ?_
  apply Integrable.add _ ((matrixAction (B x)).integrable_comp hv)
  apply integrable_finsetSum Finset.univ
  intro j _
  exact (matrixAction (A x j)).integrable_comp
    ((ContinuousLinearMap.apply ℝ (Fin r → ℂ) (EuclideanSpace.single j 1)).integrable_comp hd)

/-- The literal first-order physical operator passes through the integral when
joint smoothness and a common compact carrier hold. This is the analytic step
consumed by `physicalOperator_graphOperator`
(`app:ch_regular_base:eq:direct-graph-identity`). -/
theorem physicalOperator_integral (hU : IsOpen U) (hK : IsCompact K)
    {f : Euclidean n × Z → Fin r → ℂ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ))
    (hs : ∀ x ∈ U, ∀ z ∉ K, f (x, z) = 0)
    (A : Euclidean n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (B : Euclidean n → Matrix (Fin r) (Fin r) ℂ) {x : Euclidean n} (hx : x ∈ U) :
    physicalOperator A B (fun y ↦ ∫ z, f (y, z) ∂μ) x =
      ∫ z, physicalOperator A B (fun y ↦ f (y, z)) x ∂μ := by
  have hd := integrable_section (μ := μ) hK
    (contDiffOn_parameterFDeriv hU isOpen_univ hf).continuousOn
    (fun y hy z hz ↦ fderiv_section_eq_zero hU hs hy hz) hx
  have hv := integrable_section (μ := μ) hK hf.continuousOn hs hx
  have hj (j : Fin n) : Integrable (fun z ↦ (A x j).mulVec
      (partialDeriv (fun y ↦ f (y, z)) x j)) μ :=
    (matrixAction (A x j)).integrable_comp
      ((ContinuousLinearMap.apply ℝ (Fin r → ℂ) (EuclideanSpace.single j 1)).integrable_comp hd)
  have hb : Integrable (fun z ↦ (B x).mulVec (f (x, z))) μ :=
    (matrixAction (B x)).integrable_comp hv
  simp only [physicalOperator, partialDeriv,
    (hasFDerivAt_integral hU hK hf hs hx).fderiv,
    ContinuousLinearMap.integral_apply hd, integral_smul]
  simp only [partialDeriv] at hj
  rw [integral_add (integrable_finsetSum Finset.univ fun j _ ↦ hj j) hb,
    integral_finsetSum Finset.univ fun j _ ↦ hj j]
  congr 1
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    exact ((matrixAction (A x j)).integral_comp_comm
      ((ContinuousLinearMap.apply ℝ (Fin r → ℂ) (EuclideanSpace.single j 1)).integrable_comp hd)).symm
  · exact ((matrixAction (B x)).integral_comp_comm hv).symm

end JanetCartan.FourierIntegral.GraphDifferentiation
