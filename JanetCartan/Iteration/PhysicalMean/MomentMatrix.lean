module

public import JanetCartan.Iteration.PhysicalMean.MomentRadial

/-!
# Native matrix-row adjoint moments on the original sampled measure

The scalar input of each original raw atom has finitely many measured output
coordinates. Apply the literal scalar moment estimate to those coordinates,
and sum only this FIXED physical rank. The operator below is the same native
matrix row with the same entry kernels; no new raw input or adjoint is selected.
This supplies the complex kernel part of
`app:ch_mean_pairs:eq:raw-adjoint-moments`, before the existing exact real
quadrature/output-localization bridge is applied.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff BigOperators

namespace JanetCartan.PhysicalMean

open ContinuumAdjoint.DerivativeKernels AmplitudeBound.PaperEstimates Pseudodifferential

variable {n : ℕ} {ι I J : Type*} [Fintype ι] [MetricSpace ι] [DiscreteTopology ι]
  [MeasurableSpace ι] [BorelSpace ι] [Fintype I] [Fintype J]

omit [Fintype ι] [MeasurableSpace ι] [BorelSpace ι] in
/-- Joint continuity of the original sampled amplitude uses only smoothness
inside each fixed sample, never sample-index regularity. -/
theorem continuous_originalSampledAmplitude
    (a : ι → Euclidean (n - 1) → Euclidean n → ℂ)
    (ha : ∀ i, ContDiff ℝ ∞ (Function.uncurry (a i))) :
    Continuous (Function.uncurry (fun u : ι × Euclidean (n - 1) ↦ a u.1 u.2)) := by
  have hc : Continuous (fun p : ι × (Euclidean (n - 1) × Euclidean n) ↦ a p.1 p.2.1 p.2.2) :=
    continuous_prod_of_discrete_left.mpr (fun i ↦ (ha i).continuous)
  exact hc.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))

/-- Construct the scalar entries of the native sampled matrix from their
original full kernels. Continuity is from primitive samplewise joint
smoothness, and the original masks construct every integral. -/
def sampledMomentMatrixEntry
    (μ : Measure (ι × Euclidean (n - 1))) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ : (ι × Euclidean (n - 1)) → Euclidean n → ℝ)
    (m : (ι × Euclidean (n - 1)) → ℝ)
    (a : I → J → ι → Euclidean (n - 1) → Euclidean n → ℂ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (ha : ∀ i j k, ContDiff ℝ ∞ (Function.uncurry (a i j k)))
    {K : Set (Euclidean n)} (hK : IsCompact K) (has : ∀ i j k η, tsupport (a i j k η) ⊆ K)
    (i : I) (j : J) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)) :=
  sampledMomentOperator μ φ m (fun u ↦ a i j u.1 u.2) hφ hm
    (continuous_originalSampledAmplitude (a i j) (ha i j)) hms hK (fun u ↦ has i j u.1 u.2)

/-- Every source coordinate of the actual native matrix adjoint has the
radial estimate from the scalar tester. The only finite sum in the source
norm is over the FIXED measured output coordinates, not samples or bands.
The original data vector is assembled through the exact L² coordinate
isometry (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem sampledMatrixAdjoint_coordinate_radial_L2_bound
    (μ : Measure (ι × Euclidean (n - 1))) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ : (ι × Euclidean (n - 1)) → Euclidean n → ℝ)
    (m : (ι × Euclidean (n - 1)) → ℝ)
    (a : I → J → ι → Euclidean (n - 1) → Euclidean n → ℂ)
    (L : ι → Euclidean (n - 1) → Euclidean (n - 1) → Euclidean n → Euclidean n)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (ha : ∀ i j k, ContDiff ℝ ∞ (Function.uncurry (a i j k)))
    (hL : ∀ i h, ContDiff ℝ ∞ (fun p : Euclidean (n - 1) × Euclidean n ↦ L i p.1 h p.2))
    {K : Set (Euclidean n)} (hK : IsCompact K) (has : ∀ i j k η, tsupport (a i j k η) ⊆ K)
    (χ : Euclidean n → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχK : ∀ x ∈ K, χ x = 1)
    (R : ℝ) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ R)
    (T₀ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hT₀ : ∀ f : Lp ℂ 2 μ, T₀ f =ᵐ[volume] fun x ↦ ∫ u,
      sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)) x u * f u ∂μ)
    (hφsmooth : ∀ u, ContDiff ℝ ∞ (φ u))
    (hphase : ∀ u, m u ≠ 0 → ∀ h x, x ∈ K →
      inner ℝ h u.2 = fderiv ℝ (φ u) x (L u.1 u.2 h x))
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (q r₀ : ℕ) {T : ℝ} (hT : 1 ≤ T)
    (hamp : ∀ i j k η, m (k, η) ≠ 0 → ∀ x ∈ K, ∀ s,
      ‖iteratedFDeriv ℝ s (a i j k η) x‖ ≤ B s * T ^ (s - (r₀ + (n / 2 + 1))))
    (hcoeff : ∀ k η, m (k, η) ≠ 0 → ∀ h, ‖h‖ ≤ 1 → ∀ x ∈ K, ∀ s,
      ‖iteratedFDeriv ℝ s (L k η h) x‖ ≤ B s * T ^ (s - (r₀ + (n / 2 + 1))))
    (v : I → Euclidean n → ℂ) (hv : ∀ i, ContDiff ℝ ∞ (v i))
    (hvs : ∀ i, HasCompactSupport (v i)) (j : J) :
    let f := fun i ↦ ((hv i).continuous.memLp_of_hasCompactSupport (hvs i)
      (p := 2) (μ := volume)).toLp (v i)
    let V := (finiteL2CoordinateIsometry (I := I) volume).symm (WithLp.toLp 2 f)
    let S := nativeMatrixRowOperator μ volume (sampledMomentMatrixEntry μ φ m a hφ hm hms ha hK has)
    let raw := finiteL2CoordinateIsometry μ (S.adjoint V) j
    MemLp (fun u ↦ (‖u.2‖ : ℂ) ^ q * raw u) 2 μ ∧
      lpNorm (fun u ↦ (‖u.2‖ : ℂ) ^ q * raw u) 2 μ ≤
        sampledRadialMomentConstant n R B q * ‖T₀‖ *
          ∑ i : I, ∑ k ∈ Finset.range (q + 1), T ^ (q - k - r₀) * fourierSobolevNorm k (f i) := by
  classical
  dsimp only
  let f := fun i ↦ ((hv i).continuous.memLp_of_hasCompactSupport (hvs i)
    (p := 2) (μ := volume)).toLp (v i)
  let V := (finiteL2CoordinateIsometry (I := I) volume).symm (WithLp.toLp 2 f)
  let A := sampledMomentMatrixEntry μ φ m a hφ hm hms ha hK has
  let S := nativeMatrixRowOperator μ volume A
  let F := fun i u ↦ (m u : ℂ) * chartAdjoint (φ u) (a i j u.1 u.2) (v i)
  let w := fun i u ↦ (‖u.2‖ : ℂ) ^ q * F i u
  have hb (i : I) := sampledRadialMoment_L2_bound μ φ m (a i j) L hφ hm hms (ha i j) hL
    hK (has i j) χ hχ hχs hχK R hbox T₀ hT₀ hφsmooth hphase B hB q r₀ hT (hamp i j)
      hcoeff (v i) (hv i) (hvs i)
  have hw (i : I) : MemLp (w i) 2 μ := (hb i).1
  have hadj : finiteL2CoordinateIsometry μ (S.adjoint V) j = ∑ i, (A i j).adjoint (f i) := by
    rw [nativeSampledMatrixRow_adjoint, nativeMatrixRowOperator_coordinate]
    simp only [V, LinearIsometryEquiv.apply_symm_apply]
  have haej := ae_all_iff.mpr (fun i ↦ sampledMomentOperator_adjoint_ae μ φ m
    (fun u ↦ a i j u.1 u.2) hφ hm
      (continuous_originalSampledAmplitude (a i j) (ha i j)) hms hK
      (fun u ↦ has i j u.1 u.2) (v i)
      ((hv i).continuous.memLp_of_hasCompactSupport (hvs i) (p := 2) (μ := volume)))
  have he : (fun u ↦ (‖u.2‖ : ℂ) ^ q * (finiteL2CoordinateIsometry μ (S.adjoint V) j) u) =ᵐ[μ]
      (∑ i, w i) := by
    rw [hadj]
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ (A i j).adjoint (f i)), haej]
      with u hu haeu
    rw [hu]
    simp only [Finset.sum_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg ((‖u.2‖ : ℂ) ^ q * ·) (haeu i)
  have hmem : MemLp (∑ i, w i) 2 μ := memLp_finsetSum' _ (fun i _ ↦ hw i)
  refine ⟨(memLp_congr_ae he).mpr hmem, ?_⟩
  calc
    _ = lpNorm (∑ i, w i) 2 μ := by rw [← toReal_eLpNorm, ← toReal_eLpNorm, eLpNorm_congr_ae he]
    _ ≤ ∑ i, lpNorm (w i) 2 μ := lpNorm_sum_le (fun i _ ↦ hw i) (by norm_num)
    _ ≤ ∑ i : I, sampledRadialMomentConstant n R B q * ‖T₀‖ *
        ∑ k ∈ Finset.range (q + 1), T ^ (q - k - r₀) * fourierSobolevNorm k (f i) :=
      Finset.sum_le_sum (fun i _ ↦ (hb i).2)
    _ = _ := (Finset.mul_sum _ _ _).symm

end JanetCartan.PhysicalMean
