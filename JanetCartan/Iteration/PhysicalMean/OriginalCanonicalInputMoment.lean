module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInputMassTemplate
public import JanetCartan.Iteration.PhysicalMean.InverseMomentProfile
public import JanetCartan.Iteration.PhysicalMean.LinearProfiles

/-!
# Same unweighted input: original adjoint moment to Fourier mass

The actual consumer is the supplied-source physical wave of
`OriginalSampledPhysicalSourceTemplate`, with detector bound ONE. The phase,
scalar An representation, testers, and grades come from the sole task89 tuple;
the all-order regularity of the same Q0 source comes from task100. There is no
mass hypothesis, sample-weight division, new Fourier normalization, or prefix
loss. Actual native instantiation and the full-forcing Picard profile remain
separate parent obligations (`app:ch_mean_pairs:eq:raw-adjoint-moments`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff

@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalCanonicalInput
open RawInputRealization RawInputPartition PhysicalSamplingShells CurrentMean PeriodicLocalL2 FixedSourceFourierMass
open Pseudodifferential AmplitudeBound.PaperEstimates

local instance (J : ℕ) : MetricSpace (RefinedIndex J) :=
  TopologicalSpace.metrizableSpaceMetric (RefinedIndex J)

/-- Compose the SAME scalar annular representation with the original individual
adjoint theorem at q=n+1, then apply the sharp Fourier-mass estimate to the fixed
prefix. All analytic fields are precisely those already proved by the original
primitive tuple and inverse; the estimate has no L, cardinality or sample-weight
factor (`main:eq:primary-fixed-scales`). -/
theorem wideInput_fourierMass_le_source_moments {n J : ℕ} {ι : Type*} (hn : 1 ≤ n)
    (φ : RefinedIndex J × Euclidean (n - 1) → Euclidean n → ℝ)
    (m : RefinedIndex J × Euclidean (n - 1) → ℝ)
    (a : Fin n → RefinedIndex J → Euclidean (n - 1) → Euclidean n → ℂ)
    (trade : RefinedIndex J → Euclidean (n - 1) → Euclidean (n - 1) → Euclidean n → Euclidean n)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (hhigh : ∀ z, ‖z.2‖ ≤ 1 → m z = 0)
    (ha : ∀ i j, ContDiff ℝ ∞ (Function.uncurry (a i j)))
    (htrade : ∀ i h, ContDiff ℝ ∞ (fun p : Euclidean (n - 1) × Euclidean n ↦ trade i p.1 h p.2))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (has : ∀ i j η, tsupport (a i j η) ⊆ K)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ halfOpenCell n) (hχK : ∀ x ∈ K, χ x = 1)
    (Rbox : ℝ) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
    (Tbare : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hTbare : ∀ f : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))),
      Tbare f =ᵐ[volume] fun x ↦ ∫ z,
        sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)) x z * f z
          ∂annularShellMeasure (n := n) (refinedRadius (J := J)))
    (hφsmooth : ∀ z, ContDiff ℝ ∞ (φ z))
    (hphase : ∀ z, m z ≠ 0 → ∀ h x, x ∈ K →
      inner ℝ h z.2 = fderiv ℝ (φ z) x (trade z.1 z.2 h x))
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (r₀ : ℕ) {T : ℝ} (hT : 1 ≤ T)
    (hamp : ∀ i j η, m (j, η) ≠ 0 → ∀ x ∈ K, ∀ s,
      ‖iteratedFDeriv ℝ s (a i j η) x‖ ≤ B s * T ^ (s - (r₀ + (n / 2 + 1))))
    (hcoeff : ∀ j η, m (j, η) ≠ 0 → ∀ h, ‖h‖ ≤ 1 → ∀ x ∈ K, ∀ s,
      ‖iteratedFDeriv ℝ s (trade j η h) x‖ ≤ B s * T ^ (s - (r₀ + (n / 2 + 1))))
    (A : ι → RefinedInput n J →L[ℝ] ContinuumRow.OutputL2 n)
    (Q0 : ContinuumRow.OutputL2 n →L[ℝ] ContinuumRow.OutputL2 n)
    (e : SmoothResidual n) (i : ι) (cutoff : ℕ)
    (An : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (hAn : ∀ f c, finiteL2CoordinateIsometry volume (An f) c =ᵐ[volume] fun x ↦ ∫ z,
      sampledMomentKernel φ (halfWeightedMomentMask m) (fun z y ↦ a c z.1 z.2 y) x z * f z
        ∂annularShellMeasure (n := n) (refinedRadius (J := J)))
    (hArep : ∀ v, A i v = (transferOutputOperator (realQuadratureChannel An))
      ((annularShellEquiv (refinedRadius (J := J))).symm v))
    (hu : ∀ s, Q0 (smoothResidualToL2 n e) ∈ periodicSobolevLevel n (Euclidean n) s)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hbound : ∀ η, ‖d η‖ ≤ M) :
    (∫ η, ‖weightedWideDensity d (wideInput A Q0 cutoff e i) η‖) ≤
      ((2 * M * Real.sqrt (unitBallVolume n)) * 2 ^ (n + 1)) *
        (nativeRealMomentConstant χ hχ hc hs Rbox B (n + 1) * ‖Tbare‖ *
          ∑ k ∈ Finset.range (n + 1 + 1), T ^ (n + 1 - k - r₀) *
            periodicSobolevNorm k (Q0 (smoothResidualToL2 n e))) := by
  let μ := annularShellMeasure (n := n) (refinedRadius (J := J))
  let am : Fin n → Unit → RefinedIndex J → Euclidean (n - 1) → Euclidean n → ℂ :=
    fun c _ ↦ a c
  have hscalar := scalarAnnularAdjoint_eq_matrixCoordinate φ m a hφ hm hms ha hK has An hAn
    (Q0 (smoothResidualToL2 n e))
  have hnative := nativeInput_eq_adjoint A Q0 e i
    (transferOutputOperator (realQuadratureChannel An)) hArep
  have he := hnative.trans hscalar
  have hmoment := nativeRealIndividualAdjoint_moment_L2_bound μ φ m am trade hφ hm hms hhigh
    (fun c _ j ↦ ha c j) htrade hK (fun c _ j η ↦ has c j η)
    χ hχ hc hs hχK Rbox hbox Tbare hTbare hφsmooth hphase B hB (n + 1) r₀ hT
    (fun c _ j η ↦ hamp c j η) hcoeff (Q0 (smoothResidualToL2 n e)) hu ()
  have hexp : ((n + 1 : ℕ) : ℝ) - 1 / 2 = (n : ℝ) + 1 / 2 := by
    push_cast
    ring
  dsimp only at hmoment
  rw [hexp, ← he] at hmoment
  exact (wideInput_fourierMass_le_halfMoment hn A Q0 cutoff e i hd hM hbound hmoment.1).trans
    (mul_le_mul_of_nonneg_left hmoment.2 (by positivity))

/-- The Fourier-mass cost is fixed before the history, original sample, prefix
and source. Its moment order is exactly n+1, below the v2 reserve 2*m0. -/
def sourceMassConstant (n : ℕ) (Rbox : ℝ) (χ : Euclidean n → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n) (Badj Cinv : ℕ → ℝ) (Cbare : ℝ) : ℝ :=
  ((2 * Real.sqrt (unitBallVolume n)) * 2 ^ (n + 1)) *
    nativeRealMomentConstant χ hχ hχs hχcell Rbox Badj (n + 1) * |Cbare| *
      (2 * ∑ k ∈ Finset.range (n + 1 + 1), Cinv k)

private theorem nativeMomentCost_nonneg (n : ℕ) (Rbox : ℝ) (χ : Euclidean n → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n) (Badj : ℕ → ℝ)
    (hBadj : ∀ k, 0 ≤ Badj k) (q : ℕ) :
    0 ≤ nativeRealMomentConstant χ hχ hχs hχcell Rbox Badj q :=
  mul_nonneg (mul_nonneg (by norm_num)
    (sampledRadialMomentConstant_nonneg n Rbox Badj hBadj q))
    (sourceMomentConstant_nonneg χ hχ hχs hχcell q)

/-- The prehistory mass cost uses only nonnegative original primitive budgets. -/
theorem sourceMassConstant_nonneg (n : ℕ) (Rbox : ℝ) (χ : Euclidean n → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n) (Badj Cinv : ℕ → ℝ)
    (hBadj : ∀ k, 0 ≤ Badj k) (hCinv : ∀ k, 0 ≤ Cinv k) (Cbare : ℝ) :
    0 ≤ sourceMassConstant n Rbox χ hχ hχs hχcell Badj Cinv Cbare := by
  have hM := nativeMomentCost_nonneg n Rbox χ hχ hχs hχcell Badj hBadj (n + 1)
  have hI : 0 ≤ ∑ k ∈ Finset.range (n + 1 + 1), Cinv k :=
    Finset.sum_nonneg (fun k _ ↦ hCinv k)
  unfold sourceMassConstant
  positivity

/-- Direct consumer of the original shared sampled tuple and SAME global Q0
source profile. The detector bound is the original ONE; the estimate concerns
the unweighted individual input, uniformly in sample and fixed prefix. Every
analytic field is produced by tasks89/100/86, not by a successful-source or mass
hypothesis (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem sampled_wideInput_fourierMass_le
    (n : ℕ) (hn : 1 ≤ n) (Rbox : ℝ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n)
    (Badj Cinv : ℕ → ℝ) (hBadj : ∀ k, 0 ≤ Badj k) (hCinv : ∀ k, 0 ≤ Cinv k)
    (Cbare : ℝ) {ν : Type*} [MetricSpace ν] (J : ℕ)
    (φ : ((ν × RefinedIndex J) × Euclidean (n - 1)) → Euclidean n → ℝ)
    (ameas : Fin n → ν × RefinedIndex J → Euclidean (n - 1) → Euclidean n → ℂ)
    (L : ν × RefinedIndex J → Euclidean (n - 1) → Euclidean (n - 1) → Euclidean n → Euclidean n)
    (m : ((ν × RefinedIndex J) × Euclidean (n - 1)) → ℝ)
    (hφ : Continuous (Function.uncurry φ)) (hφs : ∀ z, ContDiff ℝ ∞ (φ z))
    (ha : ∀ a i, ContDiff ℝ ∞ (Function.uncurry (ameas a i)))
    (hL : ∀ i v, ContDiff ℝ ∞ (fun z : Euclidean (n - 1) × Euclidean n ↦ L i z.1 v z.2))
    (hm : Continuous m) (hms : HasCompactSupport m) (hhigh : ∀ z, ‖z.2‖ ≤ 1 → m z = 0)
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (haK : ∀ a i η, tsupport (ameas a i η) ⊆ K)
    (hphase : ∀ z, m z ≠ 0 → ∀ v x, x ∈ K →
      inner ℝ v z.2 = fderiv ℝ (φ z) x (L z.1 z.2 v x))
    (hχK : ∀ x ∈ K, χ x = 1) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
    {T : ℝ} (hT : 1 ≤ T)
    (haj : ∀ a i η, m (i, η) ≠ 0 → ∀ x ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (ameas a i η) x‖ ≤ Badj j * T ^ (j - (2 * (n / 2 + 2) + (n / 2 + 1))))
    (hLj : ∀ i η, m (i, η) ≠ 0 → ∀ v, ‖v‖ ≤ 1 → ∀ x ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (L i η v) x‖ ≤ Badj j * T ^ (j - (2 * (n / 2 + 2) + (n / 2 + 1))))
    (Tbare : ν → Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hTbare : ∀ i f, Tbare i f =ᵐ[volume] fun x ↦ ∫ z,
      sampledMomentKernel (fun z ↦ φ ((i, z.1), z.2)) (fun z ↦ m ((i, z.1), z.2))
        (fun _ y ↦ (χ y : ℂ)) x z * f z ∂annularShellMeasure (n := n) (refinedRadius (J := J)))
    (hTbareBound : ∀ i, ‖Tbare i‖ ≤ Cbare)
    (An : ν → Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (hAn : ∀ i f a, finiteL2CoordinateIsometry volume (An i f) a =ᵐ[volume] fun x ↦ ∫ z,
      sampledMomentKernel (fun z ↦ φ ((i, z.1), z.2)) (halfWeightedMomentMask (fun z ↦ m ((i, z.1), z.2)))
        (fun z y ↦ ameas a (i, z.1) z.2 y) x z * f z ∂annularShellMeasure (n := n) (refinedRadius (J := J)))
    (A : ν → RefinedInput n J →L[ℝ] ContinuumRow.OutputL2 n)
    (hArep : ∀ i, (A i).comp
      ((annularShellEquiv (V := ℂ) (refinedRadius (J := J))).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) =
        transferOutputOperator (realQuadratureChannel (An i)))
    (Q₀ : ContinuumRow.OutputL2 n →L[ℝ] ContinuumRow.OutputL2 n) (e : SmoothResidual n)
    (hreg : ∀ j, Q₀ (smoothResidualToL2 n e) ∈ periodicSobolevLevel n (Euclidean n) j)
    (hinverse : ∀ j : ℕ, j ≤ n + 1 → periodicSobolevNorm j (Q₀ (smoothResidualToL2 n e)) ≤
      Cinv j * (periodicSobolevNorm j (smoothResidualToL2 n e) +
        T ^ (j - 2 * (n / 2 + 2)) * ‖smoothResidualToL2 n e‖))
    (cutoff : ℕ) (i : ν) (d : Euclidean (n - 1) → ℂ)
    (hd : Measurable d) (hb : ∀ η, ‖d η‖ ≤ 1) :
    (∫ η, ‖weightedWideDensity d (wideInput A Q₀ cutoff e i) η‖) ≤
      sourceMassConstant n Rbox χ hχ hχs hχcell Badj Cinv Cbare * residualSobolevSeminorm n (n + 1) e := by
  have hφi : Continuous (Function.uncurry (fun z : RefinedIndex J × Euclidean (n - 1) ↦ φ ((i, z.1), z.2))) :=
    hφ.comp (((continuous_const.prodMk continuous_fst.fst).prodMk continuous_fst.snd).prodMk continuous_snd)
  have hmi : Continuous (fun z : RefinedIndex J × Euclidean (n - 1) ↦ m ((i, z.1), z.2)) :=
    hm.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
  have hmsi : HasCompactSupport (fun z : RefinedIndex J × Euclidean (n - 1) ↦ m ((i, z.1), z.2)) := by
    apply HasCompactSupport.of_support_subset_isCompact (hms.image (continuous_fst.snd.prodMk continuous_snd))
    intro z hz
    exact ⟨((i, z.1), z.2), subset_tsupport m hz, rfl⟩
  have harep (v : RefinedInput n J) : A i v = (transferOutputOperator (realQuadratureChannel (An i)))
      ((annularShellEquiv (refinedRadius (J := J))).symm v) := by
    have h := congrArg (fun H ↦ H ((annularShellEquiv (refinedRadius (J := J))).symm v)) (hArep i)
    simpa using h
  have hmass := wideInput_fourierMass_le_source_moments hn
    (fun z ↦ φ ((i, z.1), z.2)) (fun z ↦ m ((i, z.1), z.2)) (fun a j ↦ ameas a (i, j))
    (fun j ↦ L (i, j)) hφi hmi hmsi (fun z ↦ hhigh ((i, z.1), z.2))
    (fun a j ↦ ha a (i, j)) (fun j ↦ hL (i, j)) hK (fun a j ↦ haK a (i, j))
    χ hχ hχs hχcell hχK Rbox hbox (Tbare i) (hTbare i)
    (fun z ↦ hφs ((i, z.1), z.2)) (fun z ↦ hphase ((i, z.1), z.2))
    Badj hBadj (2 * (n / 2 + 2)) hT (fun a j ↦ haj a (i, j)) (fun j ↦ hLj (i, j))
    A Q₀ e i cutoff (An i) (hAn i) harep hreg hd (by norm_num : (0 : ℝ) ≤ 1) hb
  let P := ((2 * Real.sqrt (unitBallVolume n)) * 2 ^ (n + 1))
  let M := nativeRealMomentConstant χ hχ hχs hχcell Rbox Badj (n + 1)
  let S := ∑ k ∈ Finset.range (n + 1 + 1), T ^ (n + 1 - k - 2 * (n / 2 + 2)) *
    periodicSobolevNorm k (Q₀ (smoothResidualToL2 n e))
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hM : 0 ≤ M := nativeMomentCost_nonneg n Rbox χ hχ hχs hχcell Badj hBadj (n + 1)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k _ ↦
    mul_nonneg (pow_nonneg (zero_le_one.trans hT) _) (Real.sqrt_nonneg _))
  have hs := inverseSource_low_moment_sum_le Q₀ (smoothResidualToL2 n e) Cinv hCinv
    (n + 1) (2 * (n / 2 + 2)) (by omega) T (smoothResidualToL2_mem e (n + 1)) hinverse
  have hb' : ‖Tbare i‖ ≤ |Cbare| := (hTbareBound i).trans (le_abs_self _)
  have hm' : (∫ η, ‖weightedWideDensity d (wideInput A Q₀ cutoff e i) η‖) ≤ P * (M * ‖Tbare i‖ * S) := by
    simpa only [mul_one] using hmass
  calc
    _ ≤ P * (M * ‖Tbare i‖ * S) := hm'
    _ ≤ P * (M * |Cbare| * S) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb' hM) hS) hP
    _ ≤ P * (M * |Cbare| * ((2 * ∑ k ∈ Finset.range (n + 1 + 1), Cinv k) *
        periodicSobolevNorm (n + 1 : ℕ) (smoothResidualToL2 n e))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (mul_nonneg hM (abs_nonneg _))) hP
    _ = _ := by
      rw [residualSobolevSeminorm_eq_periodicSobolevNorm]
      dsimp only [P, M, sourceMassConstant]
      ring

end JanetCartan.PhysicalMean.OriginalCanonicalInput
end
