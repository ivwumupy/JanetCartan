module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.FiniteIdentification.Locality

/-!
# Source-first action of the global transferred full normal

The smooth-test interface for `app:ch_background:prop:bg-frame`, Step 1,
including the uncut full symbol and the actual physical source profiles.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
open AmplitudeBound Pseudodifferential PeriodicLocalL2 ContinuumNormalReduction TransportKernel TestChartTransfer
variable {n N : ℕ}

/-- The uncut transferred full PDO acts on smooth real torus tests by the
chart-indicated source-first physical action. Only the primitive measurement
support, chart identities and finite PDO derivative budget are inputs; no
convergence or source Fourier integrability is assumed.
Source: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`. -/
theorem transfer_fullReflectedMatrixOperator_ae_testAction
    (hn : 0 < n) (R : ℝ) (d : CarrierData n N)
    {K : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    (hchart : d.outputChart = torusChart K)
    (hpoint : ∀ z ∈ d.outputChart, d.chartPoint z = centeredTorusRepresentative z)
    (χ : Euclidean n → ℝ) (hχ : ∀ y ∉ K, χ y = 0)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (hχone : ∀ y, a.measurement y ≠ 0 → χ y = 1)
    (hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude a J u Ω S)))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ fullReflectedMatrixAmplitude a J u Ω S ξ z i j))
    (B : ℝ) (hB : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ fullReflectedMatrixAmplitude a J u Ω S ξ z i j) (2 * (n + 1)) B)
    (w : OutputL2 n) (w₀ : Torus n → Euclidean n)
    (hw₀ : IsSmoothPeriodic w₀) (hw : w =ᵐ[volume] w₀) :
    transferOperator
      (vectorTwoPositionL2Operator hn R (fullReflectedMatrixAmplitude a J u Ω S) hb hs B hB)
      (l2ComplexInclusion volume w) =ᵐ[volume]
      d.outputChart.indicator (fun x ↦ reflectedMatrixTestAction a J u Ω S
        (fun j ↦ physicalSourceProfile χ (fun z ↦ (w₀ z j : ℂ))) (d.chartPoint x)) := by
  let f := physicalSourceProfile χ (fun z ↦ euclideanComplexInclusion (w₀ z))
  have hc : ContDiff ℝ ∞ f := physicalSourceProfile_contDiff hχsmooth
    ⟨euclideanComplexInclusion.continuous.comp hw₀.1,
      (euclideanComplexInclusion (ι := Fin n)).contDiff.comp hw₀.2⟩
  have hfc : HasCompactSupport f := physicalSourceProfile_hasCompactSupport hχcompact _
  have hf : MemLp f 2 := hc.continuous.memLp_of_hasCompactSupport hfc
  let A := vectorTwoPositionL2Operator hn R (fullReflectedMatrixAmplitude a J u Ω S) hb hs B hB
  have hsource : A (toEuclidean (𝕜 := ℂ) (l2ComplexInclusion volume w)) = A (hf.toLp f) := by
    apply fullReflectedMatrixOperator_congr_on_measurement
    have hwc : l2ComplexInclusion volume w =ᵐ[volume]
        fun z ↦ euclideanComplexInclusion (w₀ z) := by
      filter_upwards [(euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL w, hw]
        with z hz hwz
      exact hz.trans (congrArg euclideanComplexInclusion hwz)
    have hp := (ae_restrict_iff' measurableSet_halfOpenCell).mp
      (measurePreserving_quotient.quasiMeasurePreserving.ae hwc)
    filter_upwards [toEuclidean_coe (𝕜 := ℂ) (l2ComplexInclusion volume w), hf.coeFn_toLp, hp]
      with y hy hfy hpy hm
    have hKy : y ∈ K := by
      by_contra hnot
      exact zero_ne_one ((hχ y hnot).symm.trans (hχone y hm))
    rw [hy, indicator_of_mem (hcell hKy), hfy]
    simpa [f, physicalSourceProfile, periodicLift, hχone y hm] using hpy (hcell hKy)
  have haction : A (hf.toLp f) =ᵐ[volume] reflectedMatrixTestAction a J u Ω S
      (fun j ↦ physicalSourceProfile χ (fun z ↦ (w₀ z j : ℂ))) := by
    have he := vectorTwoPositionL2Operator_ae_matrixFullAmplitudeOperator hn R _ hb hs B hB
      f hf (fun j ↦ ((contDiff_piLp 2).mp hc j).of_le (by simp))
      (fun j ↦ hfc.comp_left (g := fun v : EuclideanSpace ℂ (Fin n) ↦ v j) rfl)
    filter_upwards [he] with x hx
    rw [hx]
    apply PiLp.ext
    intro i
    exact matrixFullAmplitudeOperator_fullReflectedMatrixAmplitude a J u Ω S _ x i
  change toTorus (𝕜 := ℂ) (A (toEuclidean (𝕜 := ℂ) (l2ComplexInclusion volume w))) =ᵐ[volume] _
  rw [hsource]
  filter_upwards [toTorus_coe (𝕜 := ℂ) (A (hf.toLp f)),
    measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp haction.restrict]
    with z hz haz
  rw [hz, haz]
  by_cases hzK : z ∈ d.outputChart
  · rw [indicator_of_mem hzK, hpoint z hzK]
    rfl
  · rw [indicator_of_notMem hzK]
    apply reflectedMatrixTestAction_eq_zero_of_output_measurement
    by_contra hm
    have hnot : centeredTorusRepresentative z ∉ K := by
      simpa only [hchart, torusChart, mem_preimage] using hzK
    exact zero_ne_one ((hχ _ hnot).symm.trans (hχone _ hm))
end JanetCartan.ContinuumRow.CarrierNormalRealization
