module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.FiniteIdentification.TestAction
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.FiniteIdentification.Frequency
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Density

/-!
# Global identification of the finite carrier normal

For `app:ch_background:prop:bg-frame`, Step 1, identify the actual finite
real-quadrature normal with the globally transferred full PDO. The source-first
action theorem also applies to the uncut symbol, independently of convergence.

The actual finite-mask, chart and coefficient matches remain inputs from the
parent carrier construction. Smoothness and the exact per-entry PDO derivative
budget are the independent primitive-budget producer’s inputs. The radial
mask support and inverse-frequency comparison justify Fubini internally.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
open AmplitudeBound Pseudodifferential PeriodicLocalL2 ContinuumNormalReduction TransportKernel TestChartTransfer
variable {n N : ℕ}

/-- Equality of GLOBAL bounded operators for the finite carrier normal in
`app:ch_background:prop:bg-frame`, Step 1. Parameter truncation is applied only
to the finite carrier operator; the chart and symbol inputs retain the original
radial mask. The reflected amplitude already contains the real-quadrature
factor four. The finite PDO budget is produced by the independent primitive
budget construction; source integrability, limits and normal identities are
not premises. -/
theorem regularized_realNormal_eq_transfer_fullReflectedMatrixOperator
    (hn : 0 < n) {d : CarrierData n N} {m : CarrierVariable n → ℝ}
    {Z : Set CarrierParameter} {Rmask M Cmask : ℝ}
    (hZ : ∀ z ∉ Z, ∀ η, d.angularCutoff z η = 0)
    (h : CarrierRegularization.MaskHypotheses d (parameterTruncatedMask Z m) Z Rmask M Cmask)
    {K : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    (hchart : d.outputChart = torusChart K)
    (hpoint : ∀ z ∈ d.outputChart, d.chartPoint z = centeredTorusRepresentative z)
    (χ : Euclidean n → ℝ) (hχ : ∀ y ∉ K, χ y = 0)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (hχone : ∀ y, a.measurement y ≠ 0 → χ y = 1)
    (charts : ∀ x ∈ d.outputChart, ∀ y ∈ d.outputChart, ChartInputs d m x y)
    (symbols : ∀ x hx y hy, SymbolInputs (charts x hx y hy))
    (ha : ∀ x hx y hy, (symbols x hx y hy).coefficients = a)
    (hJ : ∀ x hx y hy, (symbols x hx y hy).jacobian = J)
    (hu : ∀ x hx y hy, (symbols x hx y hy).inverse = u)
    (hΩ : ∀ x hx y hy, (symbols x hx y hy).domain = Ω)
    (hS : ∀ x hx y hy, (symbols x hx y hy).spectatorSupport = S)
    (hhigh : HasCompactSupport a.high) {Cfreq : ℝ} (hCfreq : 0 ≤ Cfreq)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ Cfreq * ‖(u p).2‖)
    (Rbox : ℝ)
    (hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude a J u Ω S)))
    (hs : ∀ ξ i j, SupportedInCenteredBox Rbox
      (fun z ↦ fullReflectedMatrixAmplitude a J u Ω S ξ z i j))
    (B : ℝ) (hB : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ fullReflectedMatrixAmplitude a J u Ω S ξ z i j) (2 * (n + 1)) B) :
    (realQuadratureChannel h.operator).comp (realQuadratureChannel h.operator).adjoint =
      realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator hn Rbox (fullReflectedMatrixAmplitude a J u Ω S) hb hs B hB)) := by
  apply DFunLike.coe_injective
  apply (PeriodicSobolevSpace.denseRange_toL2_ofSmooth (n := n) (F := Euclidean n) 0).equalizer
    (map_continuous _) (map_continuous _)
  funext wtest
  let w := PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.ofSmooth 0 wtest.val wtest.property)
  have hw : w =ᵐ[volume] wtest.val := PeriodicSobolevSpace.toL2_ofSmooth_ae 0 _ _
  have hnormal := regularized_realNormal_ae_physicalKernelAction hZ h hcell hchart hpoint
    χ hχ a J u Ω S hχone charts symbols ha hJ hu hΩ hS w
  let f := physicalSourceProfile χ (fun z ↦ euclideanComplexInclusion (wtest.val z))
  have hc : ContDiff ℝ ∞ f := physicalSourceProfile_contDiff hχsmooth
    ⟨euclideanComplexInclusion.continuous.comp wtest.property.1,
      (euclideanComplexInclusion (ι := Fin n)).contDiff.comp wtest.property.2⟩
  have hfc : HasCompactSupport f := physicalSourceProfile_hasCompactSupport hχcompact _
  have hswap (x : Euclidean n) : reflectedMatrixKernelAction a J u Ω S
      (fun j ↦ physicalSourceProfile χ (fun z ↦ (wtest.val z j : ℂ))) x =
      reflectedMatrixTestAction a J u Ω S
      (fun j ↦ physicalSourceProfile χ (fun z ↦ (wtest.val z j : ℂ))) x :=
    reflectedMatrixKernelAction_eq_testAction_of_compact_high a J u Ω S hhigh hCfreq
      hcomparison Rbox hs hb.continuous f hc.continuous hfc x
  have hprofile (j : Fin n) : physicalSourceProfile χ (fun z ↦ (w z j : ℂ)) =ᵐ[volume]
      physicalSourceProfile χ (fun z ↦ (wtest.val z j : ℂ)) := by
    have hp := (ae_restrict_iff' measurableSet_halfOpenCell).mp
      (measurePreserving_quotient.quasiMeasurePreserving.ae hw)
    filter_upwards [hp] with y hy
    by_cases hyK : y ∈ K
    · simp only [physicalSourceProfile, periodicLift, Function.comp_apply, hy (hcell hyK)]
    · simp [physicalSourceProfile, hχ y hyK]
  have hkernel (x : Euclidean n) : reflectedMatrixKernelAction a J u Ω S
      (fun j ↦ physicalSourceProfile χ (fun z ↦ (w z j : ℂ))) x =
      reflectedMatrixTestAction a J u Ω S
      (fun j ↦ physicalSourceProfile χ (fun z ↦ (wtest.val z j : ℂ))) x := by
    rw [← hswap]
    apply PiLp.ext
    intro i
    change (∑ j : Fin n, _) = _
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [hprofile j] with y hy
    rw [hy]
  have hpdo := transfer_fullReflectedMatrixOperator_ae_testAction hn Rbox d hcell hchart hpoint
    χ hχ hχsmooth hχcompact a J u Ω S hχone hb hs B hB w wtest.val wtest.property hw
  let A := transferOperator
    (vectorTwoPositionL2Operator hn Rbox (fullReflectedMatrixAmplitude a J u Ω S) hb hs B hB)
  let Q := realQuadratureChannel h.operator
  change Q (Q.adjoint w) = l2RealPart volume (A (l2ComplexInclusion volume w))
  apply Lp.ext
  filter_upwards [hnormal, hpdo,
    (euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL (Q (Q.adjoint w)),
    (euclideanRealPart (ι := Fin n)).coeFn_compLpL (A (l2ComplexInclusion volume w))]
    with x hx hp hi hr
  change l2ComplexInclusion volume (Q (Q.adjoint w)) x = _ at hi
  change l2RealPart volume (A (l2ComplexInclusion volume w)) x = _ at hr
  have he : euclideanComplexInclusion (Q (Q.adjoint w) x) = A (l2ComplexInclusion volume w) x := by
    rw [← hi, hx, hp]
    by_cases hxc : x ∈ d.outputChart
    · simp only [indicator_of_mem hxc, hkernel]
    · simp only [indicator_of_notMem hxc]
  rw [hr, ← he]
  apply PiLp.ext
  intro i
  simp
end JanetCartan.ContinuumRow.CarrierNormalRealization
