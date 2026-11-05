module

public import JanetCartan.Iteration.PhysicalMean.MomentMatrix
public import JanetCartan.Iteration.PhysicalMean.Localization
public import JanetCartan.Analysis.Operator.RealQuadratures
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.OutputTransfer

/-!
# The same real adjoint on a compact smooth physical source

For `app:ch_mean_pairs:eq:raw-adjoint-moments`, output transfer feeds the
actual adjoint the sharp cell lift of the periodic source. That lift is NOT
a globally smooth source. We prove that the ORIGINAL supported adjoint is
unchanged when it receives the existing compact smooth localization instead.
The exact real quadrature factor is two, on the original native raw space.
No new inverse, source, kernel, cutoff-dependent operator or sample is chosen.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff BigOperators

namespace JanetCartan.PhysicalMean

open CurrentMean SmoothPeriodicFamily PeriodicLocalL2 Pseudodifferential
open AmplitudeBound.PaperEstimates

variable {n : ℕ} {X I J : Type*} [Fintype I] [Fintype J]
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

/-- The actual compact native matrix adjoint depends only on the datum on
its original physical support. This is an equality of the original Hilbert
adjoints, proved from their literal kernels, not a replacement construction
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem nativeSampledMatrixRow_adjoint_eq_of_local_data
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (B : I → J → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (κ : I → J → Euclidean n → X → ℂ)
    (hκc : ∀ i j, Continuous (Function.uncurry (κ i j)))
    (hκs : ∀ i j, HasCompactSupport (Function.uncurry (κ i j)))
    (hB : ∀ i j (f : Lp ℂ 2 μ), B i j f =ᵐ[volume] fun x ↦ ∫ u, κ i j x u * f u ∂μ)
    {K : Set (Euclidean n)} (hK : ∀ i j x, x ∉ K → ∀ u, κ i j x u = 0)
    (v w : Lp (EuclideanSpace ℂ I) 2 (volume : Measure (Euclidean n)))
    (hvw : ∀ᵐ x ∂volume, x ∈ K → v x = w x) :
    (nativeMatrixRowOperator μ volume B).adjoint v =
      (nativeMatrixRowOperator μ volume B).adjoint w := by
  classical
  have hc (i : I) : ∀ᵐ x ∂volume, x ∈ K →
      finiteL2CoordinateIsometry volume v i x = finiteL2CoordinateIsometry volume w i x := by
    filter_upwards [finiteL2Coordinates_apply_ae volume v i,
      finiteL2Coordinates_apply_ae volume w i, hvw] with x hv hw hx
    intro hxK
    exact hv.trans ((congrArg (fun z : EuclideanSpace ℂ I ↦ z i) (hx hxK)).trans hw.symm)
  apply (finiteL2CoordinateIsometry μ).injective
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [nativeSampledMatrixRow_adjoint_coordinate_kernel μ volume B κ hκc hκs hB v j,
    nativeSampledMatrixRow_adjoint_coordinate_kernel μ volume B κ hκc hκs hB w j] with u hv hw
  rw [hv, hw]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [hc i] with x hx
  by_cases hxK : x ∈ K
  · rw [hx hxK]
  · rw [hK i j x hxK u, star_zero, zero_mul, zero_mul]

omit [Fintype I] [Fintype J] [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] in
/-- The sharp cell lift and the already constructed compact smooth physical
source agree on the original plateau, in their actual L² representatives.
They are not asserted to agree outside that support or to be globally smooth
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem toEuclidean_smoothResidual_eq_cut_on
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    {K : Set (Euclidean n)} (hKcell : K ⊆ halfOpenCell n)
    (hχK : ∀ x ∈ K, χ x = 1) (r : SmoothResidual n) :
    ∀ᵐ x ∂volume, x ∈ K →
      toEuclidean (𝕜 := ℝ) (smoothResidualToL2 n r) x =
        (cutSmoothResidual χ hχ hχs r).toLp 2 volume x := by
  have hr : (smoothResidualToL2 n r : Torus n → Euclidean n) =ᵐ[volume] fun y ↦ r.val y () :=
    componentL2_coe_ae () r
  have hlift := (ae_restrict_iff' measurableSet_halfOpenCell).mp
    (measurePreserving_quotient.quasiMeasurePreserving.ae_eq_comp hr)
  filter_upwards [toEuclidean_coe (𝕜 := ℝ) (smoothResidualToL2 n r),
    (cutSmoothResidual χ hχ hχs r).coeFn_toLp 2 volume, hlift] with x hx hcut hval
  intro hxK
  rw [hx, hcut, indicator_of_mem (hKcell hxK), cutSmoothResidual_apply, hχK x hxK, one_smul]
  exact hval (hKcell hxK)

omit [Fintype I] in
/-- The SAME original real `2 Re` matrix row has exactly twice the complex
adjoint applied to the compact smooth localization of its original source.
The raw space and native measure are unchanged; the sharp cell lift has been
removed only by support locality, not by a false global source identity
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem nativeRealRow_adjoint_eq_cutSmoothResidual
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (B : Fin n → J → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (κ : Fin n → J → Euclidean n → X → ℂ)
    (hκc : ∀ i j, Continuous (Function.uncurry (κ i j)))
    (hκs : ∀ i j, HasCompactSupport (Function.uncurry (κ i j)))
    (hB : ∀ i j (f : Lp ℂ 2 μ), B i j f =ᵐ[volume] fun x ↦ ∫ u, κ i j x u * f u ∂μ)
    {K : Set (Euclidean n)} (hK : ∀ i j x, x ∉ K → ∀ u, κ i j x u = 0)
    (hKcell : K ⊆ halfOpenCell n)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχK : ∀ x ∈ K, χ x = 1) (r : SmoothResidual n) :
    let S := nativeMatrixRowOperator μ volume B
    (transferOutputOperator (realQuadratureChannel S)).adjoint (smoothResidualToL2 n r) =
      (2 : ℝ) • S.adjoint (l2ComplexInclusion volume ((cutSmoothResidual χ hχ hχs r).toLp 2 volume)) := by
  dsimp only
  rw [transferOutputOperator_adjoint, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, realQuadratureChannel_adjoint_apply]
  congr 1
  apply nativeSampledMatrixRow_adjoint_eq_of_local_data μ B κ hκc hκs hB hK
  filter_upwards [toEuclidean_smoothResidual_eq_cut_on χ hχ hχs hKcell hχK r,
    (euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL
      (toEuclidean (𝕜 := ℝ) (smoothResidualToL2 n r)),
    (euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL
      ((cutSmoothResidual χ hχ hχs r).toLp 2 volume)] with x hx hleft hright
  intro hxK
  exact hleft.trans ((congrArg euclideanComplexInclusion (hx hxK)).trans hright.symm)

end JanetCartan.PhysicalMean
