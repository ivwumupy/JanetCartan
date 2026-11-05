module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.Construction
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.GlobalTestLimit.Pairing
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.SourceConvergence

/-!
# Actual finite carrier pairings converge to the global full PDO

For `app:ch_background:prop:bg-frame`, Step 1, the finite operators use compact
parameter truncations of the original radial masks. Their physical actions use
the original squared radial cutoffs. Source Fourier convergence, composed with
the radii `k + 1`, identifies their smooth torus test limit with the globally
transferred uncut full PDO. Its reflected amplitude includes the quadrature
factor four already.

The source smoothness and uniform entry jets are exactly the outputs of
`SourceConvergence.exists_reflected_regularized_source_bounds_of_primitiveNorms`.
The uncut smoothness and physical PDO entry budget are supplied by
`exists_fullReflectedMatrixAmplitude_bounds_of_primitiveNorms` in
`CarrierNormalRealization.PrimitiveBudget`. Measurement support, actual chart
identities, inverse-frequency comparisons, and the physical and radial cutoffs
remain the parent's geometric inputs; `exists_radialCarrierMask_hypotheses`
constructs the masks. The parent retains primitive instantiation and equality
of bounded operators. No uncut adjoint or normal identity is used here.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
open AmplitudeBound Pseudodifferential PeriodicLocalL2 ContinuumNormalReduction ContinuumNormal
  TransportKernel TestChartTransfer
variable {n N : ℕ}

/-- The actual finite real-normal pairings converge, on smooth real torus
tests, to the GLOBAL transferred uncut full reflected PDO. The source jets are
uniform in every real radius at least one, and concern exactly the cycle-scaled
reflected entries. No source integrability, distributional limit, operator norm,
or uncut normal identity is an input. Both matrix sums and the output conjugation
are retained, with no additional factor four on the PDO side.
Source: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`, `app:ch_background:prop:bg-frame`, Step 1. -/
theorem regularized_realNormal_pairing_tendsto_global_fullReflectedMatrixOperator
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
    (v w : OutputL2 n) (v₀ w₀ : Torus n → Euclidean n)
    (hv₀ : IsSmoothPeriodic v₀) (hw₀ : IsSmoothPeriodic w₀)
    (hv : v =ᵐ[volume] v₀) (hw : w =ᵐ[volume] w₀) :
    Tendsto (fun k : ℕ ↦ inner ℝ v
      (realQuadratureChannel (hmask k).operator
        ((realQuadratureChannel (hmask k).operator).adjoint w))) atTop
      (𝓝 (inner ℝ v (realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator hn Rbox (fullReflectedMatrixAmplitude a J u Ω S)
          hb hs B hB)) w))) := by
  classical
  let f := fun j ↦ physicalSourceProfile χ (fun z ↦ (w₀ z j : ℂ))
  let g := fun i x ↦ starRingEnd ℂ (physicalSourceProfile χ (fun z ↦ (v₀ z i : ℂ)) x)
  let G := fun b : TransportSymbol.Coefficients n N ↦ reflectedMatrixTestAction b J u Ω S f
  have hf (j : Fin n) := real_source_profiles_regular hχsmooth hχcompact hw₀ j
  have hg (i : Fin n) := real_source_profiles_regular hχsmooth hχcompact hv₀ i
  have hinner (b : TransportSymbol.Coefficients n N) (x : Euclidean n) :
      inner ℂ (physicalSourceProfile χ (fun z ↦ euclideanComplexInclusion (v₀ z)) x)
        (G b x) = ∑ i : Fin n, g i x * G b x i := by
    simp [PiLp.inner_apply, RCLike.inner_apply, g, physicalSourceProfile, periodicLift, mul_comm]
  have ht := SourceConvergence.tendsto_integral_reflectedMatrixTestAction_carrierCutoff
    a J u Ω S κ hκone hupper hc Msource hMsource f g
    (fun j ↦ (hf j).1.of_le (by simp)) (fun j ↦ (hf j).2)
    (fun i ↦ Complex.continuous_conj.comp (hg i).1.continuous)
    (fun i ↦ (hg i).2.comp_left (g := starRingEnd ℂ) (by simp))
  have hradius : Tendsto (fun k : ℕ ↦ (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hphysical : Tendsto (fun k : ℕ ↦ ∫ x,
      inner ℂ (physicalSourceProfile χ (fun z ↦ euclideanComplexInclusion (v₀ z)) x)
        (G (TransportSymbol.regularizedCoefficients a κ ((k : ℝ) + 1)) x)) atTop
      (𝓝 (∫ x, inner ℂ
        (physicalSourceProfile χ (fun z ↦ euclideanComplexInclusion (v₀ z)) x) (G a x))) := by
    simpa only [hinner, G, Function.comp_def] using ht.comp hradius
  have hcontinuous (Q : ℝ) (hQ : 1 ≤ Q) : Continuous
      (Function.uncurry (fullReflectedMatrixAmplitude
        (TransportSymbol.regularizedCoefficients a κ Q) J u Ω S)) := by
    have hentry (i j : Fin n) : Continuous
        (fun p : Euclidean n × Euclidean (2 * n) ↦
          fullReflectedMatrixAmplitude (TransportSymbol.regularizedCoefficients a κ Q)
            J u Ω S p.1 p.2 i j) :=
      (hc Q hQ i j).continuous.comp
        ((freezingOutputProjection.continuous.comp continuous_snd).prodMk
          ((freezingSourceProjection.continuous.comp continuous_snd).prodMk continuous_fst))
    have he : Function.uncurry (fullReflectedMatrixAmplitude
        (TransportSymbol.regularizedCoefficients a κ Q) J u Ω S) =
        fun p : Euclidean n × Euclidean (2 * n) ↦ ∑ i : Fin n, ∑ j : Fin n,
          fullReflectedMatrixAmplitude (TransportSymbol.regularizedCoefficients a κ Q)
            J u Ω S p.1 p.2 i j • (Matrix.single i j 1 : Matrix (Fin n) (Fin n) ℂ) := by
      funext p
      ext i j
      simp [Matrix.single, Matrix.sum_apply, ite_and, Function.uncurry_def]
    rw [he]
    exact continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
      (hentry i j).smul continuous_const
  have hfinite (k : ℕ) : inner ℝ v
      (realQuadratureChannel (hmask k).operator
        ((realQuadratureChannel (hmask k).operator).adjoint w)) =
      (∫ x, inner ℂ
        (physicalSourceProfile χ (fun z ↦ euclideanComplexInclusion (v₀ z)) x)
        (G (TransportSymbol.regularizedCoefficients a κ ((k : ℝ) + 1)) x)).re := by
    have haction := regularized_realNormal_ae_physicalTestAction hZ (hmask k)
      hcell hchart hpoint χ hχ hχsmooth hχcompact
      (TransportSymbol.regularizedCoefficients a κ ((k : ℝ) + 1)) J u Ω S hχone
      (charts k) (symbols k) (ha k) (hJ k) (hu k) (hΩ k) (hS k)
      (regularizedCoefficients_high_hasCompactSupport a hκcompact (by positivity))
      hCfreq hcomparison Rbox
      (fullReflectedMatrixAmplitude_supportedInCenteredBox _ J u Ω S Rbox hsupport)
      (hcontinuous _ (le_add_of_nonneg_left (Nat.cast_nonneg k))) w w₀ hw₀ hw
    have he := inner_realPart_eq_re_physicalProfile_pairing d hcell hchart hpoint χ hχ
      v v₀ hv _ (G (TransportSymbol.regularizedCoefficients a κ ((k : ℝ) + 1))) haction
      (fun y hy ↦ hχone y (fun hz ↦ hy
        (reflectedMatrixTestAction_eq_zero_of_output_measurement _ J u Ω S f hz)))
    simpa only [RegularSector.Realization.realPart_inclusion] using he
  have haction := transfer_fullReflectedMatrixOperator_ae_testAction hn Rbox d hcell hchart
    hpoint χ hχ hχsmooth hχcompact a J u Ω S hχone hb hs B hB w w₀ hw₀ hw
  have hlimit := inner_realPart_eq_re_physicalProfile_pairing d hcell hchart hpoint χ hχ
    v v₀ hv _ (G a) haction
    (fun y hy ↦ hχone y (fun hz ↦ hy
      (reflectedMatrixTestAction_eq_zero_of_output_measurement a J u Ω S f hz)))
  have htReal := (Complex.continuous_re.tendsto _).comp hphysical
  simpa only [Function.comp_def, ← hfinite, ← hlimit, realOutputCompression,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars'] using htReal

end JanetCartan.ContinuumRow.CarrierNormalRealization
