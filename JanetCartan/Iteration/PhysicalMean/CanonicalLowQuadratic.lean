module

public import JanetCartan.Iteration.PhysicalMean.CanonicalQuadraticProfile

/-!
# The actual low quadratic Picard estimate from native primitives

The full original lower field stays outside the SAME native weighted row;
all refined-shell cross terms stay inside their original sample. The constant
is fixed before all sample/current/source data, and the endpoint is exactly
`H^0(u) * H^(n/2+2)(v)`. This is an independent numerical deduction from the
actual primitive interfaces, not an assertion that their original-data factory
or the unconditional uniform correction has been completed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.PhysicalMean

namespace JanetCartan.PhysicalMean
open CurrentMean SmoothPeriodicFamily PhysicalForwardMean PhysicalSamplingShells RawInputRealization
open RawInputPartition ContinuumRow PeriodicLocalL2 Pseudodifferential RawPrimary.SliceBounds
open BallExtension LocalSobolev NormalComparison

/-- The exact full grouped quadratic is one native measured cross with the
FULL original lower field and the original weighted aggregate higher input.
No shell triangle inequality, shell count or inverse weight occurs; zero weights
are valid (`app:ch_mean_pairs:eq:block-bilinear`). -/
theorem groupedQuadratic_eq_nativeLowCross {n N : ℕ} {ν β : Type*}
    [Fintype ν] [Fintype β]
    [MetricSpace ν] [DiscreteTopology ν] [MeasurableSpace ν] [BorelSpace ν]
    [MetricSpace β] [DiscreteTopology β] [MeasurableSpace β] [BorelSpace β]
    (radius : ν × β → ℝ) (weight : ν → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (φ : ((ν × β) × Euclidean (n-1)) → Euclidean n → ℝ)
    (m : ((ν × β) × Euclidean (n-1)) → ℝ)
    (A : Fin N → Fin n → ((ν × β) × Euclidean (n-1)) → Euclidean n → ℂ)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (f g : ∀ i : ν × β, Lp ℂ 2 (annularMeasure n (radius i))) :
    groupedAnnularWeightedQuadratic radius φ m A weight C f g =
      annularMeasuredCross radius φ (fun z ↦ Real.sqrt (weight z.1.1)*m z) C
        (fun i ↦ groupedAnnularForwardField radius φ m A g i.1)
        (fun z x a c ↦ A a c z x)
        (weightedAnnularInput radius (fun i ↦ weight i.1) f) := by
  funext x
  rw [annularMeasuredCross_weighted_eq radius φ m C
    (fun i ↦ groupedAnnularForwardField radius φ m A g i.1)
    (fun z x a c ↦ A a c z x) (fun i ↦ weight i.1) (fun i ↦ hweight i.1) f x]
  have hfield (i : ν × β) :
      (∫ η, (((m (i,η) : ℂ)*oscillatoryFactor 1 (φ (i,η) x)*f i η) •
        ((fun a c ↦ A a c (i,η) x) : Matrix (Fin N) (Fin n) ℂ)) ∂annularMeasure n (radius i) :
          Matrix (Fin N) (Fin n) ℂ) =
      annularForwardField radius φ m A f i x := by
    unfold annularForwardField
    apply integral_congr_ae
    filter_upwards [] with η
    ext a c
    change ((m (i,η) : ℂ)*oscillatoryFactor 1 (φ (i,η) x)*f i η)*A a c (i,η) x = _
    simp only [physicalForwardKernel, sampledMomentKernel, star_star]
    ring
  simp_rw [hfield]
  change C x (∑ i, weight i • hermitianContinuousBilinear
      (groupedAnnularForwardField radius φ m A f i x)
      (groupedAnnularForwardField radius φ m A g i x)) = _
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  change weight i • hermitianContinuousBilinear
      (groupedAnnularForwardField radius φ m A f i x)
      (groupedAnnularForwardField radius φ m A g i x) =
    ∑ j : β, weight i • hermitianContinuousBilinear
      (groupedAnnularForwardField radius φ m A g i x) (annularForwardField radius φ m A f (i,j) x)
  rw [← Finset.smul_sum, ← map_sum]
  exact congrArg (fun M ↦ weight i • M) (mixedHermitianTensor_comm _ _)


/-- The derivative-free balanced native row constant, selected before any
original samples or current coefficients (`app:ch_mean_pairs:eq:block-bilinear`). -/
def nativeLowCrossConstant (n N : ℕ) (Rbox : ℝ) (aC aG p : ℕ → ℝ) : ℝ :=
  Real.sqrt (n : ℝ)*modifiedCrossRowConstant n N Rbox*
    (∑ j ∈ Finset.range (n/2+1+1), aC j)*
      matrixForwardBranchConstant n N (n/2+1) aG p (default : SliceDerivativeBranch 0)*((n/2+1 : ℕ)+1)

/-- Nonnegativity of the fixed zero-derivative row constant. -/
theorem nativeLowCrossConstant_nonneg (n N : ℕ) (Rbox : ℝ) (aC aG p : ℕ → ℝ)
    (haC : ∀ j, 0 ≤ aC j) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j) :
    0 ≤ nativeLowCrossConstant n N Rbox aC aG p := by
  have hr := modifiedCrossRowConstant_nonneg n N Rbox
  have hm := matrixForwardBranchConstant_nonneg n N (n/2+1) (default : SliceDerivativeBranch 0) haG hp
  have hs : 0 ≤ ∑ j ∈ Finset.range (n/2+1+1), aC j := Finset.sum_nonneg fun j _ ↦ haC j
  dsimp only [nativeLowCrossConstant]
  positivity

/-- The actual lower FULL original field needs exactly `H^(ell+1)` of the
source: `2*D(ell)*(sum_{k≤ell+1} Cinv k)*Cbare²`. The bare tester cap is fixed
predata, not a conclusion about the quadratic (`app:ch_mean_pairs:eq:block-bilinear`). -/
def nativeLowLowerConstant (n N : ℕ) (Rbox : ℝ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n)
    (aG p Badj Cinv : ℕ → ℝ) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hBadj : ∀ j, 0 ≤ Badj j) (Cbare : ℝ) : ℝ :=
  2*individualNativeFieldConstant n N (n/2+1) Rbox χ hχ hχs hχcell aG p Badj haG hp hBadj*
    (∑ j ∈ Finset.range (n/2+3), Cinv j)*Cbare^2

/-- Nonnegativity of the fixed original lower-field coefficient. -/
theorem nativeLowLowerConstant_nonneg (n N : ℕ) (Rbox : ℝ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n)
    (aG p Badj Cinv : ℕ → ℝ) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hBadj : ∀ j, 0 ≤ Badj j) (hCinv : ∀ j, 0 ≤ Cinv j) (Cbare : ℝ) :
    0 ≤ nativeLowLowerConstant n N Rbox χ hχ hχs hχcell aG p Badj Cinv haG hp hBadj Cbare := by
  have hD := individualNativeFieldConstant_nonneg n N (n/2+1) Rbox χ hχ hχs hχcell aG p Badj haG hp hBadj
  have hI : 0 ≤ ∑ j ∈ Finset.range (n/2+3), Cinv j := Finset.sum_nonneg fun j _ ↦ hCinv j
  dsimp only [nativeLowLowerConstant]
  positivity

/-- The low Picard constant precedes the sample type, band count, weights,
current, frequency scale and both sources. Its two tester caps have distinct
primitive origins. The coordinate-transfer factor is order ZERO and contains
no original-sample or shell cardinality (`new:eq:source-bound`). -/
def canonicalLowQuadraticConstant (n N : ℕ) (Rbox : ℝ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n)
    (aC aG p Badj Cinv : ℕ → ℝ) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hBadj : ∀ j, 0 ≤ Badj j) (Cbare Ctest : ℝ) : ℝ :=
  (Real.sqrt ((0 : ℕ).factorial : ℝ)*((sobolevMultiindices n 0).card : ℝ))*
    (nativeLowCrossConstant n N Rbox aC aG p*Ctest*
      nativeLowLowerConstant n N Rbox χ hχ hχs hχcell aG p Badj Cinv haG hp hBadj Cbare*
        nativeAggregateSourceConstant χ hχ hχs hχcell Rbox Badj Cinv 0*Ctest)

/-- The actual primitive predata give a nonnegative low Picard constant. -/
theorem canonicalLowQuadraticConstant_nonneg (n N : ℕ) (Rbox : ℝ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n)
    (aC aG p Badj Cinv : ℕ → ℝ) (haC : ∀ j, 0 ≤ aC j) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hBadj : ∀ j, 0 ≤ Badj j) (hCinv : ∀ j, 0 ≤ Cinv j) (Cbare Ctest : ℝ) (hCtest : 0 ≤ Ctest) :
    0 ≤ canonicalLowQuadraticConstant n N Rbox χ hχ hχs hχcell aC aG p Badj Cinv haG hp hBadj Cbare Ctest := by
  have hB := nativeLowCrossConstant_nonneg n N Rbox aC aG p haC haG hp
  have hD := nativeLowLowerConstant_nonneg n N Rbox χ hχ hχs hχcell aG p Badj Cinv haG hp hBadj hCinv Cbare
  have hW := nativeAggregateSourceConstant_nonneg χ hχ hχs hχcell Rbox Badj Cinv hBadj hCinv 0
  dsimp only [canonicalLowQuadraticConstant]
  positivity

/-- Direct asymmetric low Picard estimate for the SAME actual canonical
quadratic, retaining the full original lower sample before all shell pairing.
Consumer: `sourceResidual_fixedCutoff_middle_le`, its `hlowQuadratic` input.

The proof PRODUCES the lower H^ell budget from `IndividualSource` at ell=n/2+1
and the aggregate input L² budget from `AggregateSource` at q=0, then applies
the MIDDLE sharp `BalancedIntegral` bound at dc=dt=dr=[]. No MB/MW/Q bound,
source high-profile M, source amplitude h or scale R is assumed. The source
orders are exactly 0 for u and m0=ell+1 for v, never m0+1. All qualitative kernel
jets and branch regularity are constructed from the primitive full kernels.

The current inverse norm premises are the positive-CURRENT `bg-r-inverse`
profile (24/44), NOT the v=0 initializer bound. The actual corrected-raw factory
(13) and ONE common original tester event (26) still supply the primitive
kernels, realizations and predata tester caps. Their actual instantiation is
a parent obligation, not asserted by this numerical deduction
(`app:ch_mean_pairs:eq:block-bilinear`, `new:eq:source-bound`). -/
theorem fixedSourceQuadratic_low_bound
    (n N : ℕ) (Rbox : ℝ) (hRbox : Rbox < 1/2)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n)
    (aC aG p Badj Cinv : ℕ → ℝ) (haC : ∀ j, 0 ≤ aC j) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hBadj : ∀ j, 0 ≤ Badj j) (hCinv : ∀ j, 0 ≤ Cinv j)
    (Cbare Ctest : ℝ) (hCtest : 0 ≤ Ctest)
    {ν : Type*} [Fintype ν] [MetricSpace ν] [DiscreteTopology ν] [MeasurableSpace ν] [BorelSpace ν]
    (J : ℕ) (weight : ν → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (φ : ((ν × RefinedIndex J) × Euclidean (n-1)) → Euclidean n → ℝ)
    (Φ : ν × RefinedIndex J → Euclidean (n-1) → Euclidean n → ℝ)
    (amp : Fin N → Fin n → ν × RefinedIndex J → Euclidean (n-1) → Euclidean n → ℂ)
    (ameas : Fin n → ν × RefinedIndex J → Euclidean (n-1) → Euclidean n → ℂ)
    (L : ν × RefinedIndex J → Euclidean (n-1) → Euclidean (n-1) → Euclidean n → Euclidean n)
    (m : ((ν × RefinedIndex J) × Euclidean (n-1)) → ℝ)
    (hφ : Continuous (Function.uncurry φ)) (hφs : ∀ z, ContDiff ℝ ∞ (φ z))
    (hΦ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (Φ i)))
    (hamp : ∀ a c i, ContDiff ℝ ∞ (Function.uncurry (amp a c i)))
    (ha : ∀ a i, ContDiff ℝ ∞ (Function.uncurry (ameas a i)))
    (hL : ∀ i v, ContDiff ℝ ∞ (fun z : Euclidean (n-1) × Euclidean n ↦ L i z.1 v z.2))
    (hm : Continuous m) (hms : HasCompactSupport m) (hhigh : ∀ z, ‖z.2‖ ≤ 1 → m z = 0)
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hampK : ∀ a c i η, tsupport (amp a c i η) ⊆ K) (haK : ∀ a i η, tsupport (ameas a i η) ⊆ K)
    (hagree : ∀ z, m z ≠ 0 → ∀ x ∈ K, φ z x = Φ z.1 z.2 x)
    (hphase : ∀ z, m z ≠ 0 → ∀ v x, x ∈ K → inner ℝ v z.2 = fderiv ℝ (φ z) x (L z.1 z.2 v x))
    (hχK : ∀ x ∈ K, χ x = 1) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : ContDiff ℝ ∞ C)
    (Cp : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hCp : IsSmoothPeriodic Cp)
    (hCeq : ∀ z, Cp z = C (AmplitudeBound.centeredTorusRepresentative z))
    {T : ℝ} (hT : 1 ≤ T)
    (hCj : ∀ x ∈ K, ∀ j, ‖iteratedFDeriv ℝ j C x‖ ≤ aC j*T^(j-(2*(n/2+2)+(n/2+1))))
    (hGj : ∀ a c i η, m (i,η) ≠ 0 → ∀ x ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (amp a c i η) x‖ ≤ aG j*T^(j-(2*(n/2+2)+(n/2+1))))
    (hΦj : ∀ i η, m (i,η) ≠ 0 → ∀ x ∈ K, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ j (fun y ↦ Φ i η y/‖η‖) x‖ ≤ p j*T^(j-1-(2*(n/2+2)+(n/2+1))))
    (haj : ∀ a i η, m (i,η) ≠ 0 → ∀ x ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (ameas a i η) x‖ ≤ Badj j*T^(j-(2*(n/2+2)+(n/2+1))))
    (hLj : ∀ i η, m (i,η) ≠ 0 → ∀ v, ‖v‖ ≤ 1 → ∀ x ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (L i η v) x‖ ≤ Badj j*T^(j-(2*(n/2+2)+(n/2+1))))
    (Tbare : ν → Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hTbare : ∀ i f, Tbare i f =ᵐ[volume] fun x ↦ ∫ z,
      sampledMomentKernel (fun z ↦ φ ((i,z.1),z.2)) (fun z ↦ m ((i,z.1),z.2))
        (fun _ y ↦ (χ y : ℂ)) x z*f z ∂annularShellMeasure (n := n) (refinedRadius (J := J)))
    (hTbareBound : ∀ i, ‖Tbare i‖ ≤ Cbare)
    (An : ν → Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (hAn : ∀ i f a0, finiteL2CoordinateIsometry volume (An i f) a0 =ᵐ[volume] fun x ↦ ∫ z,
      sampledMomentKernel (fun z ↦ φ ((i,z.1),z.2)) (halfWeightedMomentMask (fun z ↦ m ((i,z.1),z.2)))
        (fun z y ↦ ameas a0 (i,z.1) z.2 y) x z*f z ∂annularShellMeasure (n := n) (refinedRadius (J := J)))
    (A : ν → Input n (refinedRadius (J := J)) →L[ℝ] OutputL2 n)
    (hArep : ∀ i, (A i).comp
      ((annularShellEquiv (V := ℂ) (refinedRadius (J := J))).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) =
      transferOutputOperator (realQuadratureChannel (An i)))
    (G : ν → Input n (refinedRadius (J := J)) →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (hG : ∀ i w z, (G i w).val z () = ∑ j : RefinedIndex J,
      (∫ η, ((fun a c ↦ physicalForwardKernel (fun η ↦ φ ((i,j),η)) (fun η ↦ m ((i,j),η)*Real.sqrt ‖η‖)
        (amp a c (i,j)) (AmplitudeBound.centeredTorusRepresentative z) η*w j η) : Matrix (Fin N) (Fin n) ℂ)
        ∂annularMeasure n (refinedRadius j) : Matrix (Fin N) (Fin n) ℂ))
    (Tfull : Lp ℂ 2 (sampledShellMeasure (ι := ν) n J) →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hTfull : ∀ f, Tfull f =ᵐ[volume] fun x ↦ ∫ z,
      sampledMomentKernel φ (originalWeightedHalfMask weight m) (fun _ y ↦ (χ y : ℂ)) x z*f z
        ∂sampledShellMeasure (ι := ν) n J)
    (hTfullBound : ‖Tfull‖ ≤ Ctest)
    (hrow : (CanonicalRow.weightedRow weight A).comp
      ((sampledShellEquiv (V := ℂ) (ι := ν) n J).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) =
      transferOutputOperator (realQuadratureChannel (nativeMeasuredRow (sampledShellMeasure (ι := ν) n J) φ
        (originalWeightedHalfMask weight m) ameas hφ (originalWeightedHalfMask_continuous weight m hm)
        (originalWeightedHalfMask_hasCompactSupport weight m hms) ha hK haK)))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (u v : SmoothResidual n)
    (hregu : ∀ j, Q₀ (smoothResidualToL2 n u) ∈ periodicSobolevLevel n (Euclidean n) j)
    (hregv : ∀ j, Q₀ (smoothResidualToL2 n v) ∈ periodicSobolevLevel n (Euclidean n) j)
    (hinverseu : ∀ j : ℕ, j ≤ 0 → periodicSobolevNorm j (Q₀ (smoothResidualToL2 n u)) ≤
      Cinv j*(periodicSobolevNorm j (smoothResidualToL2 n u)+T^(j-2*(n/2+2))*‖smoothResidualToL2 n u‖))
    (hinversev : ∀ j : ℕ, j ≤ n/2+2 → periodicSobolevNorm j (Q₀ (smoothResidualToL2 n v)) ≤
      Cinv j*(periodicSobolevNorm j (smoothResidualToL2 n v)+T^(j-2*(n/2+2))*‖smoothResidualToL2 n v‖)) :
    residualSobolevSeminorm n 0 (fixedSourceQuadratic weight Cp hCp A G Q₀ u v) ≤
      canonicalLowQuadraticConstant n N Rbox χ hχ hχs hχcell aC aG p Badj Cinv haG hp hBadj Cbare Ctest*
        residualSobolevSeminorm n 0 u*residualSobolevSeminorm n (n/2+2) v := by
  let radius : ν × RefinedIndex J → ℝ := fun ij ↦ refinedRadius ij.2
  let mf := fun z : (ν × RefinedIndex J) × Euclidean (n-1) ↦ m z*Real.sqrt ‖z.2‖
  let Af := fun a c (z : (ν × RefinedIndex J) × Euclidean (n-1)) y ↦ amp a c z.1 z.2 y
  let θ := fun z : (ν × RefinedIndex J) × Euclidean (n-1) ↦ normalizedForwardPhase (Φ z.1) z.2
  obtain ⟨hθ, hnormalized, hjets, hbc, hθeq⟩ :=
    originalSampledForward_qualitative φ Φ amp m hΦ hamp hm hhigh hampK hagree
  have hθj (z : (ν × RefinedIndex J) × Euclidean (n-1)) (hz : m z ≠ 0)
      (x : Euclidean n) (hx : x ∈ K) (j : ℕ) (hj : 1 ≤ j) :
      ‖iteratedFDeriv ℝ j (θ z) x‖ ≤ p j*T^(j-1-(2*(n/2+2)+(n/2+1))) := by
    rw [hθeq z hz j x]
    exact hΦj z.1 z.2 hz x hx j hj
  let f := canonicalAnnularInputs radius A Q₀ u
  let g := canonicalAnnularInputs radius A Q₀ v
  let CB := nativeLowLowerConstant n N Rbox χ hχ hχs hχcell aG p Badj Cinv haG hp hBadj Cbare
  let CW := nativeAggregateSourceConstant χ hχ hχs hχcell Rbox Badj Cinv 0
  let CQ := nativeLowCrossConstant n N Rbox aC aG p
  have hCB : 0 ≤ CB := nativeLowLowerConstant_nonneg n N Rbox χ hχ hχs hχcell aG p Badj Cinv haG hp hBadj hCinv Cbare
  have hCW : 0 ≤ CW := nativeAggregateSourceConstant_nonneg χ hχ hχs hχcell Rbox Badj Cinv hBadj hCinv 0
  have hCQ : 0 ≤ CQ := nativeLowCrossConstant_nonneg n N Rbox aC aG p haC haG hp
  have hu0 : 0 ≤ residualSobolevSeminorm n 0 u := apply_nonneg _ _
  have hvm : 0 ≤ residualSobolevSeminorm n (n/2+2) v := apply_nonneg _ _
  have hinsert (i : ν) : Continuous (fun z : (RefinedIndex J × Euclidean (n-1)) × Euclidean n ↦
      (((i,z.1.1),z.1.2),z.2)) := ((continuous_const.prodMk continuous_fst.fst).prodMk continuous_fst.snd).prodMk continuous_snd
  have hφi (i : ν) : Continuous (Function.uncurry (fun z : RefinedIndex J × Euclidean (n-1) ↦ φ ((i,z.1),z.2))) :=
    hφ.comp (hinsert i)
  have hmi (i : ν) : Continuous (fun z : RefinedIndex J × Euclidean (n-1) ↦ m ((i,z.1),z.2)) :=
    hm.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
  have hmsi (i : ν) : HasCompactSupport (fun z : RefinedIndex J × Euclidean (n-1) ↦ m ((i,z.1),z.2)) := by
    apply HasCompactSupport.of_support_subset_isCompact (hms.image (continuous_fst.snd.prodMk continuous_snd))
    intro z hz
    exact ⟨((i,z.1),z.2), subset_tsupport m hz, rfl⟩
  have hGc (a c) : Continuous (Function.uncurry (Af a c)) := continuous_originalSampledAmplitude (amp a c) (hamp a c)
  have hGci (i : ν) (a c) : Continuous (fun z : (RefinedIndex J × Euclidean (n-1)) × Euclidean n ↦ amp a c (i,z.1.1) z.1.2 z.2) :=
    (hGc a c).comp (hinsert i)
  have hBi (i : ν) := individualNativeInverseField_bounds n N (n/2+1) Rbox χ hχ hχs hχcell
    aG p Badj haG hp hBadj Cinv hCinv J
    (fun z ↦ φ ((i,z.1),z.2)) (fun j ↦ Φ (i,j)) (fun a c j ↦ amp a c (i,j))
    (fun a j ↦ ameas a (i,j)) (fun j ↦ L (i,j)) (fun z ↦ m ((i,z.1),z.2))
    (hφi i) (fun z ↦ hφs ((i,z.1),z.2)) (fun j ↦ hΦ (i,j)) (fun a c j ↦ hamp a c (i,j))
    (fun a j ↦ ha a (i,j)) (fun j ↦ hL (i,j)) (hmi i) (hmsi i) (fun z ↦ hhigh ((i,z.1),z.2))
    hK (fun a c j ↦ hampK a c (i,j)) (fun a j ↦ haK a (i,j))
    (fun z ↦ hagree ((i,z.1),z.2)) (fun z ↦ hphase ((i,z.1),z.2)) hχK hbox hT
    (fun a c j ↦ hGj a c (i,j)) (fun j ↦ hΦj (i,j)) (fun a j ↦ haj a (i,j)) (fun j ↦ hLj (i,j))
    (Tbare i) (hTbare i) (An i) (hAn i) Q₀ (smoothResidualToL2 n v) hregv hinversev
  have hBeq (i : ν) : groupedAnnularForwardField radius φ mf Af g i =
      individualNativeInverseField (fun z ↦ φ ((i,z.1),z.2)) (fun z ↦ m ((i,z.1),z.2))
        (fun a c j ↦ amp a c (i,j)) (An i) Q₀ (smoothResidualToL2 n v) :=
    groupedOriginalCurrentField_eq_individualNativeInverseField
      (fun i z ↦ φ ((i,z.1),z.2)) (fun i z ↦ m ((i,z.1),z.2)) (fun i a c j ↦ amp a c (i,j))
      hφi hmi hmsi hGci hK (fun i a c j ↦ hampK a c (i,j)) A An hArep Q₀ (smoothResidualToL2 n v) i
  have hBmem (i : ν) (j : ℕ) (hj : j ≤ n/2+1) :
      MemLp (iteratedFDeriv ℝ j (groupedAnnularForwardField radius φ mf Af g i)) 2 volume := by
    rw [hBeq i]
    exact (hBi i).2.2.1 j hj
  have hBbound (i : ν) :
      (∑ j ∈ Finset.range (n/2+1+1), lpNorm (iteratedFDeriv ℝ j (groupedAnnularForwardField radius φ mf Af g i)) 2 volume) ≤
        CB*residualSobolevSeminorm n (n/2+2) v := by
    rw [hBeq i]
    have hb := (hBi i).2.2.2.1 (by omega) (smoothResidualToL2_mem v (n/2+2))
    have hD := individualNativeFieldConstant_nonneg n N (n/2+1) Rbox χ hχ hχs hχcell aG p Badj haG hp hBadj
    have hI : 0 ≤ ∑ j ∈ Finset.range (n/2+3), Cinv j := Finset.sum_nonneg fun j _ ↦ hCinv j
    have hs : ‖Tbare i‖^2 ≤ Cbare^2 := pow_le_pow_left₀ (norm_nonneg _) (hTbareBound i) 2
    apply hb.trans
    have horder : ((n/2+1 : ℕ) : ℝ)+1 = ((n/2+2 : ℕ) : ℝ) := by push_cast; ring
    rw [horder, ← residualSobolevSeminorm_eq_periodicSobolevNorm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by positivity)) hvm
  have hW : ‖weightedAnnularInput radius (fun i ↦ weight i.1) f‖ ≤
      CW*Ctest*residualSobolevSeminorm n 0 u := by
    have he := weightedAnnularInput_eq_nativeAdjoint weight A _ hrow Q₀ (smoothResidualToL2 n u)
    change weightedAnnularInput radius (fun i ↦ weight i.1) f = _ at he
    rw [he, Lp.norm_def, toReal_eLpNorm]
    have hb := nativeRealMeasuredInverseAdjoint_radial_bounds
      (sampledShellMeasure (ι := ν) n J) φ (originalWeightedHalfMask weight m) ameas hφ
      (originalWeightedHalfMask_continuous weight m hm) (originalWeightedHalfMask_hasCompactSupport weight m hms)
      ha hK haK L hL χ hχ hχs hχcell hχK Rbox hbox Tfull hTfull hφs
      (fun z hz ↦ hphase z (fun hzero ↦ hz (by simp [originalWeightedHalfMask, hzero])))
      Badj hBadj 0 (2*(n/2+2)) hT
      (fun a i η hi ↦ haj a i η (fun hzero ↦ hi (by simp [originalWeightedHalfMask, hzero])))
      (fun i η hi ↦ hLj i η (fun hzero ↦ hi (by simp [originalWeightedHalfMask, hzero])))
      Q₀ (smoothResidualToL2 n u) hregu Cinv hCinv hinverseu
    have hb0 := hb.2.1
    simp only [pow_zero, one_mul, Nat.zero_add, Finset.sum_range_one,
      Nat.zero_sub] at hb0
    rw [← residualSobolevSeminorm_eq_periodicSobolevNorm] at hb0
    exact hb0.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTfullBound hCW) hu0)
  have hBs (i : ν) : ContDiff ℝ ∞ (groupedAnnularForwardField radius φ mf Af g i) := by
    rw [hBeq i]
    exact (hBi i).1
  have hAs (a c) (z : (ν × RefinedIndex J) × Euclidean (n-1)) : ContDiff ℝ ∞ (Af a c z) := by
    have hs : ContDiff ℝ ∞ (fun x : Euclidean n ↦ (z.2,x)) := contDiff_const.prodMk contDiff_id
    exact (hamp a c z.1).comp hs
  let Qfield := groupedAnnularWeightedQuadratic radius φ mf Af weight C f g
  let w := weightedAnnularInput radius (fun i ↦ weight i.1) f
  have hQeq : Qfield = annularMeasuredCross radius φ (originalWeightedHalfMask weight m) C
      (fun i ↦ groupedAnnularForwardField radius φ mf Af g i.1)
      (fun z x a c ↦ Af a c z x) w :=
    groupedQuadratic_eq_nativeLowCross radius weight hweight φ mf Af C f g
  have hc := annularMeasuredCross_balanced_L2_bound radius φ θ (originalWeightedHalfMask weight m)
    hφ (originalWeightedHalfMask_continuous weight m hm) (originalWeightedHalfMask_hasCompactSupport weight m hms)
    C (fun i ↦ groupedAnnularForwardField radius φ mf Af g i.1) Af hC (fun i ↦ hBs i.1) hθ hAs
    hK (fun a c z ↦ hampK a c z.1 z.2) [] [] [] (default : SliceDerivativeBranch 0)
    (fun a c ↦ hbc [] a c (default : SliceDerivativeBranch 0)) χ hχ.continuous hχs hχK Rbox hbox aC aG p haC haG hp hT (2*(n/2+2))
    (fun x hx j _ ↦ hCj x hx j)
    (fun a c z hz x hx j _ ↦ hGj a c z.1 z.2 (fun hzero ↦ hz (by simp [originalWeightedHalfMask, hzero])) x hx j)
    (fun z hz x hx j hj _ ↦ hθj z (fun hzero ↦ hz (by simp [originalWeightedHalfMask, hzero])) x hx j hj)
    (mul_nonneg hCB hvm) (fun i j hj ↦ hBmem i.1 j hj) (fun i ↦ hBbound i.1) Tfull hTfull w
  have hQmem : MemLp Qfield 2 volume := by
    rw [hQeq]
    exact hc.1
  have hc0 := hc.2.1
  change lpNorm (annularMeasuredCross radius φ (originalWeightedHalfMask weight m) C
      (fun i ↦ groupedAnnularForwardField radius φ mf Af g i.1) (fun z x a c ↦ Af a c z x) w) 2 volume ≤
    CQ*‖Tfull‖*T^(0-2*(n/2+2))*(CB*residualSobolevSeminorm n (n/2+2) v)*‖w‖ at hc0
  have hQbound : lpNorm Qfield 2 volume ≤
      CQ*Ctest*CB*CW*Ctest*residualSobolevSeminorm n 0 u*residualSobolevSeminorm n (n/2+2) v := by
    rw [hQeq]
    have hb : lpNorm (annularMeasuredCross radius φ (originalWeightedHalfMask weight m) C
        (fun i ↦ groupedAnnularForwardField radius φ mf Af g i.1) (fun z x a c ↦ Af a c z x) w) 2 volume ≤
        CQ*‖Tfull‖*(CB*residualSobolevSeminorm n (n/2+2) v)*‖w‖ := by
      simpa only [Nat.zero_sub, pow_zero, mul_one] using hc0
    have ht : CQ*‖Tfull‖*(CB*residualSobolevSeminorm n (n/2+2) v) ≤
        CQ*Ctest*(CB*residualSobolevSeminorm n (n/2+2) v) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTfullBound hCQ) (mul_nonneg hCB hvm)
    exact hb.trans ((mul_le_mul ht hW (norm_nonneg w) (by positivity)).trans_eq (by ring))
  have hins (i : ν × RefinedIndex J) : Continuous (fun z : Euclidean (n-1) × Euclidean n ↦ ((i,z.1),z.2)) :=
    (continuous_const.prodMk continuous_fst).prodMk continuous_snd
  have hφshell (i : ν × RefinedIndex J) : Continuous (fun z : Euclidean (n-1) × Euclidean n ↦ φ (i,z.1) z.2) :=
    hφ.comp (hins i)
  have hmf : Continuous mf := hm.mul continuous_snd.norm.sqrt
  have hmfs : HasCompactSupport mf := hms.mul_right
  have hmshell (i : ν × RefinedIndex J) : Continuous (fun η ↦ mf (i,η)) :=
    hmf.comp (continuous_const.prodMk continuous_id)
  have hmsshell (i : ν × RefinedIndex J) : HasCompactSupport (fun η ↦ mf (i,η)) := by
    apply HasCompactSupport.of_support_subset_isCompact (hmfs.image continuous_snd)
    intro η hη
    exact ⟨(i,η), subset_tsupport _ hη, rfl⟩
  have hAcshell (a : Fin N) (c : Fin n) (i : ν × RefinedIndex J) :
      Continuous (fun z : Euclidean (n-1) × Euclidean n ↦ Af a c (i,z.1) z.2) := (hGc a c).comp (hins i)
  have hshellfields (t : ∀ i, Lp ℂ 2 (annularMeasure n (radius i))) (i : ν × RefinedIndex J) :=
    annularForwardField_smooth_supported radius φ θ mf Af hφshell hmshell hmsshell hAcshell hθ hAs
      hK (fun a c z ↦ hampK a c z.1 z.2)
      (fun z hz ↦ hnormalized z (fun hzero ↦ hz (by simp [mf, hzero]))) hjets t i
  have hfields (t : ∀ i, Lp ℂ 2 (annularMeasure n (radius i))) (i : ν) :=
    groupedAnnularForwardField_smooth_supported radius φ mf Af t hK.isClosed (hshellfields t) i
  have hQsm : ContDiff ℝ ∞ Qfield := by
    apply hC.clm_apply
    apply ContDiff.sum
    intro i _
    exact (((hermitianContinuousBilinear (m := Fin N) (n := Fin n)).contDiff.comp
      (hfields f i).1).clm_apply (hfields g i).1).const_smul (weight i)
  have hQK : tsupport Qfield ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    have hz (i : ν) : groupedAnnularForwardField radius φ mf Af f i x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht ↦ hxK ((hfields f i).2 ht))
    apply hx
    simp [Qfield, groupedAnnularWeightedQuadratic, hz]
  have hQbox : tsupport Qfield ⊆ {x | ∀ i, |x i| ≤ Rbox} := fun x hx ↦ hbox x (hQK hx)
  have hM : 0 ≤ CQ*Ctest*CB*CW*Ctest*residualSobolevSeminorm n 0 u*residualSobolevSeminorm n (n/2+2) v := by
    positivity
  have hcoord (ds : List (Fin n)) (hds : ds.length ≤ 0) :
      MemLp (cartesianCoordinateDerivList ds Qfield) 2 volume ∧
        lpNorm (cartesianCoordinateDerivList ds Qfield) 2 volume ≤
          CQ*Ctest*CB*CW*Ctest*residualSobolevSeminorm n 0 u*residualSobolevSeminorm n (n/2+2) v := by
    have hd : ds = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hds)
    subst ds
    exact ⟨hQmem, hQbound⟩
  have hp0 := periodicSobolevNorm_vectorPeriodization_le_coordinate_bound 0 hRbox hM Qfield hQsm hQbox hcoord
  rw [fixedSourceQuadratic_sobolev_eq_grouped radius weight φ mf Af C Cp hCp hCeq A G hG Q₀ u v 0]
  exact hp0.trans_eq (by dsimp only [canonicalLowQuadraticConstant, CB, CW, CQ]; ring)


end JanetCartan.PhysicalMean
