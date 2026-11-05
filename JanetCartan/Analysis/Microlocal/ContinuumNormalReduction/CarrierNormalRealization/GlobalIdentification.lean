module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.GlobalTestLimit
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.LiteralAdjoint

/-!
# Global uncut carrier normal identification

The two limits of the actual finite normal pairings identify the normal of the
same carrier extension with the global transferred full PDO. Smooth torus test
density extends the identity to all output L² data. The primitive construction
in `GlobalConstruction` supplies every analytic input used here.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
open AmplitudeBound Pseudodifferential PeriodicLocalL2 ContinuumNormalReduction
  TransportKernel
variable {n N : ℕ}

/-- The normal of the SAME uncut carrier extension equals the global full
reflected matrix PDO on all real output L² data. The two independently proved
finite-normal limits agree on smooth tests, and density closes the equality.
`GlobalConstruction` supplies the finite complex-normal bound and source/PDO
jets from primitive norms. No uncut normal identity or adjoint membership is
assumed. The reflected amplitude already includes the quadrature factor four.
Source: `app:ch_background:prop:bg-frame`, Step 1,
`app:ch_background:eq:bg-full-complex-amplitude`, and `bg-real-symbol`. -/
theorem carrierRealization_realNormal_eq_transfer_fullReflectedMatrixOperator
    (hn : 0 < n) {d : CarrierData n N}
    (κ : ℝ → ℝ) (_hκsmooth : ContDiff ℝ ∞ κ) (hκcompact : HasCompactSupport κ)
    (hκone : ∀ t ∈ Icc (0 : ℝ) 1, κ t = 1)
    {Z : Set CarrierParameter} {R : ℕ → ℝ} {M Cmask : ℝ}
    (hZ : ∀ z ∉ Z, ∀ η, d.angularCutoff z η = 0)
    (hmask : ∀ k : ℕ, CarrierRegularization.MaskHypotheses d
      (parameterTruncatedMask Z (radialCarrierMask κ ((k : ℝ) + 1))) Z (R k) M Cmask)
    {K : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    (hchart : d.outputChart = torusChart K)
    (hpoint : ∀ z ∈ d.outputChart, d.chartPoint z = centeredTorusRepresentative z)
    (χ : Euclidean n → ℝ) (hχ : ∀ y ∉ K, χ y = 0)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (hχone : ∀ y, a.measurement y ≠ 0 → χ y = 1)
    (charts : ∀ k : ℕ, ∀ x ∈ d.outputChart, ∀ y ∈ d.outputChart,
      ChartInputs d (radialCarrierMask κ ((k : ℝ) + 1)) x y)
    (symbols : ∀ k x hx y hy, SymbolInputs (charts k x hx y hy))
    (ha : ∀ k x hx y hy, (symbols k x hx y hy).coefficients =
      TransportSymbol.regularizedCoefficients a κ ((k : ℝ) + 1))
    (hJ : ∀ k x hx y hy, (symbols k x hx y hy).jacobian = J)
    (hu : ∀ k x hx y hy, (symbols k x hx y hy).inverse = u)
    (hΩ : ∀ k x hx y hy, (symbols k x hx y hy).domain = Ω)
    (hS : ∀ k x hx y hy, (symbols k x hx y hy).spectatorSupport = S)
    {Cfreq Cupper : ℝ} (hCfreq : 0 ≤ Cfreq)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ Cfreq * ‖(u p).2‖)
    (hupper : ∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖)
    (hc : ∀ Q : ℝ, 1 ≤ Q → ∀ i j : Fin n,
      ContDiff ℝ ∞ (fun p : TransportSymbol.Variables n ↦
        (reflectedSymbolAmplitude (TransportSymbol.regularizedCoefficients a κ Q) J u Ω S
          (p.1, p.2.1, (2 * Real.pi) • p.2.2) i j : ℂ)))
    (Msource : Fin n → Fin n → ℕ → ℝ)
    (hMsource : ∀ Q : ℝ, 1 ≤ Q → ∀ i j x y ξ k, k ≤ n + 1 →
      ‖iteratedFDeriv ℝ k (fun p : TransportSymbol.Variables n ↦
        (reflectedSymbolAmplitude (TransportSymbol.regularizedCoefficients a κ Q) J u Ω S
          (p.1, p.2.1, (2 * Real.pi) • p.2.2) i j : ℂ)) (x, y, ξ)‖ ≤ Msource i j k)
    (Rbox : ℝ) (hsupport : ∀ x, a.measurement x ≠ 0 → ∀ j, |x j| ≤ Rbox)
    (hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude a J u Ω S)))
    (hs : ∀ ξ i j, SupportedInCenteredBox Rbox
      (fun z ↦ fullReflectedMatrixAmplitude a J u Ω S ξ z i j))
    (B : ℝ) (hB : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ fullReflectedMatrixAmplitude a J u Ω S ξ z i j) (2 * (n + 1)) B)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ v : carrierInitialTestSpace n,
      U (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral d v.val)
    (Bnormal : ℝ) (hBnormal : 0 ≤ Bnormal)
    (hnormal : ∀ k, ‖(hmask k).operator.comp (hmask k).operator.adjoint‖ ≤ Bnormal) :
    (realQuadratureChannel U).comp (realQuadratureChannel U).adjoint =
      realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator hn Rbox (fullReflectedMatrixAmplitude a J u Ω S)
          hb hs B hB)) := by
  apply DFunLike.coe_injective
  apply (PeriodicSobolevSpace.denseRange_toL2_ofSmooth (n := n) (F := Euclidean n) 0).equalizer
    (map_continuous _) (map_continuous _)
  funext wtest
  apply (PeriodicSobolevSpace.denseRange_toL2_ofSmooth (n := n) (F := Euclidean n) 0).eq_of_inner_right ℝ
  intro vtest
  let v := PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.ofSmooth 0 vtest.val vtest.property)
  let w := PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.ofSmooth 0 wtest.val wtest.property)
  have hv : v =ᵐ[volume] vtest.val := PeriodicSobolevSpace.toL2_ofSmooth_ae 0 _ _
  have hw : w =ᵐ[volume] wtest.val := PeriodicSobolevSpace.toL2_ofSmooth_ae 0 _ _
  exact tendsto_nhds_unique
    (parameterRegularizedOperator_realNormal_tendsto hZ hκone hmask U hU hBnormal hnormal v w)
    (regularized_realNormal_pairing_tendsto_global_fullReflectedMatrixOperator
      hn κ _hκsmooth hκcompact hκone hZ hmask hcell hchart hpoint χ hχ hχsmooth hχcompact
      a J u Ω S hχone charts symbols ha hJ hu hΩ hS hCfreq hcomparison hupper
      hc Msource hMsource Rbox hsupport hb hs B hB v w vtest.val wtest.val
      vtest.property wtest.property hv hw)

end JanetCartan.ContinuumRow.CarrierNormalRealization
