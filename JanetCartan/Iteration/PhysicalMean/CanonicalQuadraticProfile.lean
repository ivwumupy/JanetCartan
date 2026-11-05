module

public import JanetCartan.Iteration.PhysicalMean.CanonicalQuadratic
public import JanetCartan.Iteration.PhysicalMean.GroupedCurrent
public import JanetCartan.Iteration.PhysicalMean.AggregateSourceProfiles
public import JanetCartan.Iteration.PhysicalMean.NativeTopology
public import JanetCartan.Iteration.PhysicalMean.CanonicalRegularity

/-!
# Actual canonical quadratic source profile from primitive native data

This is the direct `hquadratic` producer for the fixed-source finite Picard
recurrence. It uses the same original `A`, full smooth `Graw`, coefficient,
weights and current inverse. IndividualSource and AggregateSource PRODUCE the
lower/full-input budgets inside the proof; neither budget nor the quadratic
bound is a premise (`new:eq:source-bound`, `app:ch_mean_pairs:eq:block-bilinear`).
The actual corrected-raw factory and the ONE common original scalar sampling
event remain the original-data producers of the stated primitive kernels and
tester bounds; this deduction does not assert that factory's existence.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.PhysicalMean

namespace JanetCartan.PhysicalMean
open CurrentMean SmoothPeriodicFamily PhysicalForwardMean PhysicalSamplingShells RawInputRealization
open RawInputPartition ContinuumRow PeriodicLocalL2 Pseudodifferential RawPrimary.SliceBounds

/-- Literal original square-root sample weight and full half derivative. -/
def originalWeightedHalfMask {n : ℕ} {ν β : Type*} (weight : ν → ℝ)
    (m : (ν × β) × Euclidean (n-1) → ℝ) (z : (ν × β) × Euclidean (n-1)) : ℝ :=
  Real.sqrt (weight z.1.1)*(m z*Real.sqrt ‖z.2‖)

/-- Discrete original weights do not change joint continuity of the full mask. -/
theorem originalWeightedHalfMask_continuous {n : ℕ} {ν β : Type*}
    [TopologicalSpace ν] [DiscreteTopology ν] [TopologicalSpace β]
    (weight : ν → ℝ) (m : (ν × β) × Euclidean (n-1) → ℝ) (hm : Continuous m) :
    Continuous (originalWeightedHalfMask weight m) :=
  ((continuous_of_discreteTopology : Continuous (fun i : ν ↦ Real.sqrt (weight i))).comp
    continuous_fst.fst).mul (hm.mul continuous_snd.norm.sqrt)

/-- The complete weighted mask retains the original compact frequency support. -/
theorem originalWeightedHalfMask_hasCompactSupport {n : ℕ} {ν β : Type*}
    [TopologicalSpace ν] [TopologicalSpace β]
    (weight : ν → ℝ) (m : (ν × β) × Euclidean (n-1) → ℝ) (hm : HasCompactSupport m) :
    HasCompactSupport (originalWeightedHalfMask weight m) := (hm.mul_right).mul_left

/-- The fixed quadratic source profile is chosen BEFORE the original sample,
current phase, inverse, source and scales. The bare and half-weighted tester
constants retain their distinct roles. -/
def canonicalQuadraticSourceProfileConstant (n N : ℕ) (Rbox : ℝ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n)
    (aC aG p Badj Cinv M : ℕ → ℝ) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hBadj : ∀ j, 0 ≤ Badj j) (Cbare Ctest : ℝ) (s : ℕ) : ℝ :=
  quadraticSobolevProfileConstant n N Rbox aC aG p
    (nativeLowerSourceProfileConstant n N Rbox χ hχ hχs hχcell aG p Badj Cinv M haG hp hBadj Cbare)
    (nativeAggregateSourceProfileConstant χ hχ hχs hχcell Rbox Badj Cinv M Ctest) s*Ctest

/-- Nonnegativity of the predata canonical quadratic source constant. -/
theorem canonicalQuadraticSourceProfileConstant_nonneg (n N : ℕ) (Rbox : ℝ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n)
    (aC aG p Badj Cinv M : ℕ → ℝ) (haC : ∀ j, 0 ≤ aC j) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hBadj : ∀ j, 0 ≤ Badj j) (hCinv : ∀ j, 0 ≤ Cinv j) (hM : ∀ j, 0 ≤ M j)
    (Cbare Ctest : ℝ) (hCtest : 0 ≤ Ctest) (s : ℕ) :
    0 ≤ canonicalQuadraticSourceProfileConstant n N Rbox χ hχ hχs hχcell aC aG p Badj Cinv M haG hp hBadj Cbare Ctest s := by
  have hMB := nativeLowerSourceProfileConstant_nonneg n N Rbox χ hχ hχs hχcell
    aG p Badj Cinv M haG hp hBadj hCinv hM Cbare
  have hMW := nativeAggregateSourceProfileConstant_nonneg χ hχ hχs hχcell Rbox Badj Cinv M hBadj hCinv hM Ctest hCtest
  have hQ := quadraticOrderProfileConstant_nonneg n N Rbox aC aG p _ _ haC haG hp hMB hMW s
  dsimp only [canonicalQuadraticSourceProfileConstant, quadraticSobolevProfileConstant,
    quadraticCoordinateProfileConstant]
  positivity

/-- DIRECT same-current canonical quadratic source estimate. Full lower
fields and original aggregate inputs are computed from the actual source by
the previously checked primitive kernel theorems INSIDE this proof. All
cross-shell terms remain; only source derivative orders enter the constant. -/
theorem fixedSourceQuadratic_source_profile
    (n N : ℕ) (Rbox : ℝ) (hRbox : Rbox < 1/2)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n)
    (aC aG p Badj Cinv M : ℕ → ℝ) (haC : ∀ j, 0 ≤ aC j) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hBadj : ∀ j, 0 ≤ Badj j) (hCinv : ∀ j, 0 ≤ Cinv j) (hM : ∀ j, 0 ≤ M j)
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
    {T R h : ℝ} (hT : 1 ≤ T) (hR : 1 ≤ R) (hTR : T ≤ R) (hh : 0 ≤ h)
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
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (u : SmoothResidual n)
    (hreg : ∀ j, Q₀ (smoothResidualToL2 n u) ∈ periodicSobolevLevel n (Euclidean n) j)
    (hinverse : ∀ j : ℕ, periodicSobolevNorm j (Q₀ (smoothResidualToL2 n u)) ≤
      Cinv j*(periodicSobolevNorm j (smoothResidualToL2 n u)+T^(j-2*(n/2+2))*‖smoothResidualToL2 n u‖))
    (hsource : ∀ j, residualSobolevSeminorm n j u ≤ M j*h*R^(j-2*(n/2+2))) (s : ℕ) :
    residualSobolevSeminorm n s (fixedSourceQuadratic weight Cp hCp A G Q₀ u u) ≤
      canonicalQuadraticSourceProfileConstant n N Rbox χ hχ hχs hχcell
        aC aG p Badj Cinv M haG hp hBadj Cbare Ctest s*h^2*R^(s-2*(n/2+2)) := by
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
  let MB := nativeLowerSourceProfileConstant n N Rbox χ hχ hχs hχcell aG p Badj Cinv M haG hp hBadj Cbare
  let MW := nativeAggregateSourceProfileConstant χ hχ hχs hχcell Rbox Badj Cinv M Ctest
  have hMB := nativeLowerSourceProfileConstant_nonneg n N Rbox χ hχ hχs hχcell aG p Badj Cinv M haG hp hBadj hCinv hM Cbare
  have hMW := nativeAggregateSourceProfileConstant_nonneg χ hχ hχs hχcell Rbox Badj Cinv M hBadj hCinv hM Ctest hCtest
  have hu : ∀ j : ℕ, periodicSobolevNorm j (smoothResidualToL2 n u) ≤ M j*h*R^(j-2*(n/2+2)) := by
    simpa only [residualSobolevSeminorm_eq_periodicSobolevNorm] using hsource
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
  have hB (t : ℕ) (_ht : t ≤ s) (i : ν) :
      (∑ j ∈ Finset.range (n/2+1+t+1), lpNorm (iteratedFDeriv ℝ j (groupedAnnularForwardField radius φ mf Af f i)) 2 volume) ≤
        MB t*h*R^(t-(n/2+2)) := by
    have he := groupedOriginalCurrentField_eq_individualNativeInverseField
      (fun i z ↦ φ ((i,z.1),z.2)) (fun i z ↦ m ((i,z.1),z.2)) (fun i a c j ↦ amp a c (i,j))
      hφi hmi hmsi hGci hK (fun i a c j ↦ hampK a c (i,j)) A An hArep Q₀ (smoothResidualToL2 n u) i
    change groupedAnnularForwardField radius φ mf Af f i = _ at he
    rw [he]
    exact (individualNativeInverseField_source_profile n N t Rbox χ hχ hχs hχcell
      aG p Badj Cinv M haG hp hBadj hCinv hM Cbare J
      (fun z ↦ φ ((i,z.1),z.2)) (fun j ↦ Φ (i,j)) (fun a c j ↦ amp a c (i,j))
      (fun a j ↦ ameas a (i,j)) (fun j ↦ L (i,j)) (fun z ↦ m ((i,z.1),z.2))
      (hφi i) (fun z ↦ hφs ((i,z.1),z.2)) (fun j ↦ hΦ (i,j)) (fun a c j ↦ hamp a c (i,j))
      (fun a j ↦ ha a (i,j)) (fun j ↦ hL (i,j)) (hmi i) (hmsi i) (fun z ↦ hhigh ((i,z.1),z.2))
      hK (fun a c j ↦ hampK a c (i,j)) (fun a j ↦ haK a (i,j))
      (fun z ↦ hagree ((i,z.1),z.2)) (fun z ↦ hphase ((i,z.1),z.2)) hχK hbox hT hR hTR hh
      (fun a c j ↦ hGj a c (i,j)) (fun j ↦ hΦj (i,j)) (fun a j ↦ haj a (i,j)) (fun j ↦ hLj (i,j))
      (Tbare i) (hTbare i) (hTbareBound i) (An i) (hAn i) Q₀ (smoothResidualToL2 n u) hreg
      (fun j _ ↦ hinverse j) (fun j _ ↦ hu j)).2.2.2
  have hW (k : ℕ) (_hk : k ≤ s) : lpNorm (fun z ↦ (‖z.2‖ : ℂ)^k*
      weightedAnnularInput radius (fun i ↦ weight i.1) f z) 2 (annularShellMeasure radius) ≤ MW k*h*R^(k-2*(n/2+2)) := by
    have he := weightedAnnularInput_eq_nativeAdjoint weight A _ hrow Q₀ (smoothResidualToL2 n u)
    change weightedAnnularInput radius (fun i ↦ weight i.1) f = _ at he
    rw [he]
    exact (nativeRealMeasuredInverseAdjoint_source_profile χ hχ hχs hχcell Rbox Badj Cinv M hBadj hCinv hM Ctest k (2*(n/2+2))
      (sampledShellMeasure (ι := ν) n J) φ (originalWeightedHalfMask weight m) ameas L hφ
      (originalWeightedHalfMask_continuous weight m hm) (originalWeightedHalfMask_hasCompactSupport weight m hms)
      ha hL hK haK hχK hbox Tfull hTfull hTfullBound hφs
      (fun z hz ↦ hphase z (fun hzero ↦ hz (by simp [originalWeightedHalfMask, hzero]))) hT hR hTR hh
      (fun a i η hi ↦ haj a i η (fun hzero ↦ hi (by simp [originalWeightedHalfMask, hzero])))
      (fun i η hi ↦ hLj i η (fun hzero ↦ hi (by simp [originalWeightedHalfMask, hzero])))
      Q₀ (smoothResidualToL2 n u) hreg (fun k _ ↦ hinverse k) (fun k _ ↦ hu k)).2
  have hQ := groupedAnnularWeightedQuadratic_sobolev_profile radius weight hweight φ θ mf Af hφ
    (hm.mul continuous_snd.norm.sqrt) hms.mul_right hGc hθ
    (fun a c z ↦ (hamp a c z.1).comp (contDiff_const.prodMk contDiff_id)) hK (fun a c z ↦ hampK a c z.1 z.2)
    (fun z hz ↦ hnormalized z (fun hzero ↦ hz (by simp [mf, hzero]))) hjets C hC f f s (n/2+2) hbc
    χ hχ.continuous hχs hχK Rbox hRbox hbox aC aG p MB MW haC haG hp hMB hMW hT hR hTR hh
    (fun x hx j _ ↦ hCj x hx j)
    (fun a c z hz x hx j _ ↦ hGj a c z.1 z.2 (fun hzero ↦ hz (by simp [mf, hzero])) x hx j)
    (fun z hz x hx j hj _ ↦ hθj z (fun hzero ↦ hz (by simp [mf, hzero])) x hx j hj)
    hB hB hW hW Tfull hTfull
  rw [fixedSourceQuadratic_sobolev_eq_grouped radius weight φ mf Af C Cp hCp hCeq A G hG Q₀ u u s]
  apply hQ.2.2.trans
  have hQ0 := quadraticOrderProfileConstant_nonneg n N Rbox aC aG p MB MW haC haG hp hMB hMW s
  have hQS : 0 ≤ quadraticSobolevProfileConstant n N Rbox aC aG p MB MW s := by
    dsimp only [quadraticSobolevProfileConstant, quadraticCoordinateProfileConstant]
    positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hTfullBound hQS) (sq_nonneg h)) (pow_nonneg (zero_le_one.trans hR) _)

end JanetCartan.PhysicalMean
