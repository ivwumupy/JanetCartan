module

public import JanetCartan.Iteration.PhysicalMean.MomentMatrix

/-!
# Individual adjoint moments with the exact half-order cost

The individual moment immediately after
`app:ch_mean_pairs:eq:raw-adjoint-moments` is of order `q - 1/2`, NOT `q`.
The actual halfweighted adjoint times this weight is exactly the bare
adjoint's integer moment of order `q`. The existing compact IBP estimate
therefore applies with the original bare tester from `PhysicalScalarChannel`.
The original high pass handles the zero frequency even when `q = 0`.
No sample/band norm sum, inverse sample mass or altered native measure is used.
This does not replace the halfweighted aggregate scalar tester.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ContDiff BigOperators

namespace JanetCartan.PhysicalMean

open ContinuumAdjoint.DerivativeKernels AmplitudeBound.PaperEstimates Pseudodifferential

variable {n : ℕ} {ι : Type*}

/-- The SAME original half derivative, factored out only to compare the
individual adjoint with its bare scalar tester. -/
def halfWeightedMomentMask (m : ι × Euclidean (n - 1) → ℝ)
    (u : ι × Euclidean (n - 1)) : ℝ := Real.sqrt ‖u.2‖ * m u

/-- The original high pass makes half-order cancellation valid at every
frequency, including the zero-frequency endpoint for the order-zero moment. -/
theorem individualMoment_halfMask_cancel
    (m : ι × Euclidean (n - 1) → ℝ) (hhigh : ∀ u, ‖u.2‖ ≤ 1 → m u = 0)
    (q : ℕ) (u : ι × Euclidean (n - 1)) :
    ((‖u.2‖ ^ ((q : ℝ) - 1 / 2) : ℝ) : ℂ) * (halfWeightedMomentMask m u : ℂ) =
      (‖u.2‖ : ℂ) ^ q * (m u : ℂ) := by
  by_cases hu : m u = 0
  · simp only [halfWeightedMomentMask, hu, mul_zero, Complex.ofReal_zero]
  · have hn : 0 < ‖u.2‖ := by
      have hh : 1 < ‖u.2‖ := lt_of_not_ge (fun h ↦ hu (hhigh u h))
      exact zero_lt_one.trans hh
    have hr : ‖u.2‖ ^ ((q : ℝ) - 1 / 2) * Real.sqrt ‖u.2‖ = ‖u.2‖ ^ q := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn]
      rw [show (q : ℝ) - 1 / 2 + 1 / 2 = q by ring, Real.rpow_natCast]
    simp only [halfWeightedMomentMask, Complex.ofReal_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul, hr, Complex.ofReal_pow]

variable [MetricSpace ι]

/-- The halfweighted original mask has the same joint continuity. -/
theorem continuous_halfWeightedMomentMask
    (m : ι × Euclidean (n - 1) → ℝ) (hm : Continuous m) :
    Continuous (halfWeightedMomentMask m) :=
  (Real.continuous_sqrt.comp continuous_snd.norm).mul hm

/-- Multiplying by the literal half derivative does not enlarge the original
compact frequency support. -/
theorem hasCompactSupport_halfWeightedMomentMask
    (m : ι × Euclidean (n - 1) → ℝ) (hms : HasCompactSupport m) :
    HasCompactSupport (halfWeightedMomentMask m) := hms.mul_left

variable [DiscreteTopology ι] [Fintype ι] [MeasurableSpace ι] [BorelSpace ι]

/-- Exact radial comparison of the actual halfweighted and bare scalar
adjoints on their SAME native Hilbert space. This identity is where the
individual half order is accounted for, rather than silently discarded. -/
theorem sampledHalfAdjoint_radial_ae
    (μ : Measure (ι × Euclidean (n - 1))) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ : (ι × Euclidean (n - 1)) → Euclidean n → ℝ)
    (m : (ι × Euclidean (n - 1)) → ℝ) (a : (ι × Euclidean (n - 1)) → Euclidean n → ℂ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (hhigh : ∀ u, ‖u.2‖ ≤ 1 → m u = 0) (ha : Continuous (Function.uncurry a))
    {K : Set (Euclidean n)} (hK : IsCompact K) (has : ∀ u, tsupport (a u) ⊆ K)
    (v : Euclidean n → ℂ) (hv : MemLp v 2 volume) (q : ℕ) :
    let S := sampledMomentOperator μ φ (halfWeightedMomentMask m) a hφ
      (continuous_halfWeightedMomentMask m hm) ha (hasCompactSupport_halfWeightedMomentMask m hms) hK has
    let S₀ := sampledMomentOperator μ φ m a hφ hm ha hms hK has
    (fun u ↦ ((‖u.2‖ ^ ((q : ℝ) - 1 / 2) : ℝ) : ℂ) * S.adjoint (hv.toLp v) u) =ᵐ[μ]
      fun u ↦ (‖u.2‖ : ℂ) ^ q * S₀.adjoint (hv.toLp v) u := by
  dsimp only
  filter_upwards [sampledMomentOperator_adjoint_ae μ φ (halfWeightedMomentMask m) a hφ
    (continuous_halfWeightedMomentMask m hm) ha (hasCompactSupport_halfWeightedMomentMask m hms) hK has v hv,
    sampledMomentOperator_adjoint_ae μ φ m a hφ hm ha hms hK has v hv] with u hh hb
  rw [hh, hb, ← mul_assoc, individualMoment_halfMask_cancel m hhigh q u, mul_assoc]

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The ORIGINAL individual halfweighted matrix adjoint has moment order
`q - 1/2`, bounded by the bare tester and the same integer source orders.
The only finite sum is over fixed physical output coordinates. In the actual
application `ι = RefinedIndex J` and `μ` is the whole original disjoint-shell
measure for ONE carrier, not a separate estimate summed over its bands. -/
theorem individualMatrixAdjoint_coordinate_moment_L2_bound
    (μ : Measure (ι × Euclidean (n - 1))) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ : (ι × Euclidean (n - 1)) → Euclidean n → ℝ)
    (m : (ι × Euclidean (n - 1)) → ℝ)
    (a : I → J → ι → Euclidean (n - 1) → Euclidean n → ℂ)
    (L : ι → Euclidean (n - 1) → Euclidean (n - 1) → Euclidean n → Euclidean n)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (hhigh : ∀ u, ‖u.2‖ ≤ 1 → m u = 0)
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
    let S := nativeMatrixRowOperator μ volume
      (sampledMomentMatrixEntry μ φ (halfWeightedMomentMask m) a hφ
        (continuous_halfWeightedMomentMask m hm) (hasCompactSupport_halfWeightedMomentMask m hms) ha hK has)
    let raw := finiteL2CoordinateIsometry μ (S.adjoint V) j
    MemLp (fun u ↦ ((‖u.2‖ ^ ((q : ℝ) - 1 / 2) : ℝ) : ℂ) * raw u) 2 μ ∧
      lpNorm (fun u ↦ ((‖u.2‖ ^ ((q : ℝ) - 1 / 2) : ℝ) : ℂ) * raw u) 2 μ ≤
        sampledRadialMomentConstant n R B q * ‖T₀‖ *
          ∑ i : I, ∑ k ∈ Finset.range (q + 1), T ^ (q - k - r₀) * fourierSobolevNorm k (f i) := by
  classical
  dsimp only
  let f := fun i ↦ ((hv i).continuous.memLp_of_hasCompactSupport (hvs i)
    (p := 2) (μ := volume)).toLp (v i)
  let V := (finiteL2CoordinateIsometry (I := I) volume).symm (WithLp.toLp 2 f)
  let A := sampledMomentMatrixEntry μ φ (halfWeightedMomentMask m) a hφ
    (continuous_halfWeightedMomentMask m hm) (hasCompactSupport_halfWeightedMomentMask m hms) ha hK has
  let A₀ := sampledMomentMatrixEntry μ φ m a hφ hm hms ha hK has
  let S := nativeMatrixRowOperator μ volume A
  let S₀ := nativeMatrixRowOperator μ volume A₀
  have hb := sampledMatrixAdjoint_coordinate_radial_L2_bound μ φ m a L hφ hm hms ha hL hK has
    χ hχ hχs hχK R hbox T₀ hT₀ hφsmooth hphase B hB q r₀ hT hamp hcoeff v hv hvs j
  have hh : finiteL2CoordinateIsometry μ (S.adjoint V) j = ∑ i, (A i j).adjoint (f i) := by
    rw [nativeSampledMatrixRow_adjoint, nativeMatrixRowOperator_coordinate]
    simp only [V, LinearIsometryEquiv.apply_symm_apply]
  have hbare : finiteL2CoordinateIsometry μ (S₀.adjoint V) j = ∑ i, (A₀ i j).adjoint (f i) := by
    rw [nativeSampledMatrixRow_adjoint, nativeMatrixRowOperator_coordinate]
    simp only [V, LinearIsometryEquiv.apply_symm_apply]
  have haej := ae_all_iff.mpr (fun i ↦ sampledHalfAdjoint_radial_ae μ φ m
    (fun u ↦ a i j u.1 u.2) hφ hm hms hhigh
    (continuous_originalSampledAmplitude (a i j) (ha i j)) hK (fun u ↦ has i j u.1 u.2)
      (v i) ((hv i).continuous.memLp_of_hasCompactSupport (hvs i) (p := 2) (μ := volume)) q)
  have he : (fun u ↦ ((‖u.2‖ ^ ((q : ℝ) - 1 / 2) : ℝ) : ℂ) *
      finiteL2CoordinateIsometry μ (S.adjoint V) j u) =ᵐ[μ]
      fun u ↦ (‖u.2‖ : ℂ) ^ q * finiteL2CoordinateIsometry μ (S₀.adjoint V) j u := by
    rw [hh, hbare]
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ (A i j).adjoint (f i)),
      Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ (A₀ i j).adjoint (f i)), haej] with u hu hb hi
    rw [hu, hb, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ hi i)
  refine ⟨(memLp_congr_ae he).mpr hb.1, ?_⟩
  calc
    _ = lpNorm (fun u ↦ (‖u.2‖ : ℂ) ^ q * finiteL2CoordinateIsometry μ (S₀.adjoint V) j u) 2 μ := by
      rw [← toReal_eLpNorm, ← toReal_eLpNorm, eLpNorm_congr_ae he]
    _ ≤ _ := hb.2

end JanetCartan.PhysicalMean
