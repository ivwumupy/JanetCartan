module

public import JanetCartan.Iteration.PhysicalMean.CurrentAdjoint
public import JanetCartan.Iteration.PhysicalMean.IndividualMoments

/-!
# The original individual real adjoint on the same current inverse

This joins the literal `q - 1/2` individual moment with the real `2 Re`
channel, original output transfer and exact regular current-inverse datum.
The bare scalar tester removes NO half order from the conclusion: taking
`q = k + 1` gives precisely the `k + 1/2` input moment needed by the
original individual forward field (`app:ch_mean_pairs:eq:block-fields`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped ContDiff BigOperators

namespace JanetCartan.PhysicalMean

open CurrentMean PeriodicLocalL2 Pseudodifferential AmplitudeBound.PaperEstimates

variable {n : ℕ} {ι J : Type*} [Fintype ι] [MetricSpace ι] [DiscreteTopology ι]
  [MeasurableSpace ι] [BorelSpace ι] [Fintype J]

/-- The actual individual HALFWEIGHTED real adjoint on the SAME regular
periodic source, with its exact `q - 1/2` moment. The scalar tester is bare,
but the adjoint is not. In the original application the native measure is
the whole disjoint refined-shell measure for one carrier; every band stays
inside that one operator (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem nativeRealIndividualAdjoint_moment_L2_bound
    (μ : Measure (ι × Euclidean (n - 1))) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ : (ι × Euclidean (n - 1)) → Euclidean n → ℝ)
    (m : (ι × Euclidean (n - 1)) → ℝ)
    (a : Fin n → J → ι → Euclidean (n - 1) → Euclidean n → ℂ)
    (L : ι → Euclidean (n - 1) → Euclidean (n - 1) → Euclidean n → Euclidean n)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (hhigh : ∀ u, ‖u.2‖ ≤ 1 → m u = 0)
    (ha : ∀ i j k, ContDiff ℝ ∞ (Function.uncurry (a i j k)))
    (hL : ∀ i h, ContDiff ℝ ∞ (fun p : Euclidean (n - 1) × Euclidean n ↦ L i p.1 h p.2))
    {K : Set (Euclidean n)} (hK : IsCompact K) (has : ∀ i j k η, tsupport (a i j k η) ⊆ K)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ halfOpenCell n) (hχK : ∀ x ∈ K, χ x = 1)
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
    (u : ContinuumRow.OutputL2 n) (hu : ∀ s, u ∈ periodicSobolevLevel n (Euclidean n) s) (j : J) :
    let S := nativeMatrixRowOperator μ volume
      (sampledMomentMatrixEntry μ φ (halfWeightedMomentMask m) a hφ
        (continuous_halfWeightedMomentMask m hm) (hasCompactSupport_halfWeightedMomentMask m hms) ha hK has)
    let raw := finiteL2CoordinateIsometry μ ((transferOutputOperator (realQuadratureChannel S)).adjoint u) j
    MemLp (fun z ↦ ((‖z.2‖ ^ ((q : ℝ) - 1 / 2) : ℝ) : ℂ) * raw z) 2 μ ∧
      lpNorm (fun z ↦ ((‖z.2‖ ^ ((q : ℝ) - 1 / 2) : ℝ) : ℂ) * raw z) 2 μ ≤
        nativeRealMomentConstant χ hχ hc hs R B q * ‖T₀‖ *
          ∑ k ∈ Finset.range (q + 1), T ^ (q - k - r₀) * periodicSobolevNorm k u := by
  classical
  dsimp only
  let r := regularSourceRepresentative u hu
  let v := fun i : Fin n ↦ (cutSmoothResidualCoordinate χ hχ hc r i : Euclidean n → ℂ)
  have hv (i : Fin n) : ContDiff ℝ ∞ (v i) := (cutSmoothResidualCoordinate χ hχ hc r i).smooth ⊤
  have hvs (i : Fin n) : HasCompactSupport (v i) := hasCompactSupport_cutSmoothResidualCoordinate χ hχ hc r i
  let f := fun i ↦ ((hv i).continuous.memLp_of_hasCompactSupport (hvs i)
    (p := 2) (μ := volume)).toLp (v i)
  let V := (finiteL2CoordinateIsometry (I := Fin n) volume).symm (WithLp.toLp 2 f)
  have hf (i : Fin n) : f i = (cutSmoothResidualCoordinate χ hχ hc r i).toLp 2 volume := rfl
  have hV : V = l2ComplexInclusion volume ((cutSmoothResidual χ hχ hc r).toLp 2 volume) := by
    apply (finiteL2CoordinateIsometry volume).injective
    simp only [V, LinearIsometryEquiv.apply_symm_apply, cutSmoothResidual_coordinates_toLp]
    apply PiLp.ext
    intro i
    exact hf i
  have hKcell : K ⊆ halfOpenCell n := by
    intro x hx
    apply hs
    apply subset_tsupport
    change χ x ≠ 0
    rw [hχK x hx]
    norm_num
  let S := nativeMatrixRowOperator μ volume
    (sampledMomentMatrixEntry μ φ (halfWeightedMomentMask m) a hφ
      (continuous_halfWeightedMomentMask m hm) (hasCompactSupport_halfWeightedMomentMask m hms) ha hK has)
  let raw := finiteL2CoordinateIsometry μ ((transferOutputOperator (realQuadratureChannel S)).adjoint u) j
  let raw₀ := finiteL2CoordinateIsometry μ (S.adjoint V) j
  have hb := individualMatrixAdjoint_coordinate_moment_L2_bound μ φ m a L hφ hm hms hhigh ha hL hK has
    χ hχ.continuous hc hχK R hbox T₀ hT₀ hφsmooth hphase B hB q r₀ hT hamp hcoeff v hv hvs j
  have he := nativeRealSampledAdjoint_coordinate_eq_cut μ φ (halfWeightedMomentMask m) a hφ
    (continuous_halfWeightedMomentMask m hm) (hasCompactSupport_halfWeightedMomentMask m hms)
      ha hK has hKcell χ hχ hc hχK u hu j
  change raw = (2 : ℝ) • finiteL2CoordinateIsometry μ
    (S.adjoint (l2ComplexInclusion volume ((cutSmoothResidual χ hχ hc r).toLp 2 volume))) j at he
  rw [← hV] at he
  have hreal := weightedNativeCoordinate_two μ raw raw₀ he
    (fun z ↦ ((‖z.2‖ ^ ((q : ℝ) - 1 / 2) : ℝ) : ℂ)) hb.1
  have hsum : (∑ i : Fin n, ∑ k ∈ Finset.range (q + 1), T ^ (q - k - r₀) * fourierSobolevNorm k (f i)) ≤
      sourceMomentConstant χ hχ hc hs q *
        ∑ k ∈ Finset.range (q + 1), T ^ (q - k - r₀) * periodicSobolevNorm k u := by
    simpa only [hf, r, regularSourceRepresentative_sobolevNorm] using
      cutSmoothResidualCoordinate_moment_sum_le χ hχ hc hs q r₀ (zero_le_one.trans hT) r
  refine ⟨hreal.1, ?_⟩
  calc
    _ = 2 * lpNorm (fun z ↦ ((‖z.2‖ ^ ((q : ℝ) - 1 / 2) : ℝ) : ℂ) * raw₀ z) 2 μ := hreal.2
    _ ≤ 2 * (sampledRadialMomentConstant n R B q * ‖T₀‖ *
        ∑ i : Fin n, ∑ k ∈ Finset.range (q + 1), T ^ (q - k - r₀) * fourierSobolevNorm k (f i)) :=
      mul_le_mul_of_nonneg_left hb.2 (by norm_num)
    _ ≤ 2 * (sampledRadialMomentConstant n R B q * ‖T₀‖ *
        (sourceMomentConstant χ hχ hc hs q *
          ∑ k ∈ Finset.range (q + 1), T ^ (q - k - r₀) * periodicSobolevNorm k u)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (sampledRadialMomentConstant_nonneg n R B hB q) (norm_nonneg _))) (by norm_num)
    _ = _ := by unfold nativeRealMomentConstant; ring

end JanetCartan.PhysicalMean
