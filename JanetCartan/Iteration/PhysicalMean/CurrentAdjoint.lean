module

public import JanetCartan.Iteration.PhysicalMean.MomentSourceConstants

/-!
# The original real sampled adjoint on the same current-inverse source

The operator is the real `2 Re` channel of the ORIGINAL native full matrix
kernel, with the original periodic output transfer. The datum is any given
all-order regular L² source: in the mean construction it is exactly the
CURRENT UNCUT augmented-normal inverse applied to the Picard source.
The sharp periodic lift is replaced only inside the supported adjoint by
its literal smooth localization. No continuum carrier slot is substituted
for the sampled corrected adjoint (`app:ch_mean_pairs:eq:raw-adjoint-moments`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped ContDiff BigOperators

namespace JanetCartan.PhysicalMean

open CurrentMean PeriodicLocalL2 Pseudodifferential AmplitudeBound.PaperEstimates

/-- The exact real-quadrature factor two preserves native weighted L²
membership and multiplies its norm by two. The weight and native measure
are unchanged (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem weightedNativeCoordinate_two {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (v w : Lp ℂ 2 μ) (hvw : v = (2 : ℝ) • w) (ρ : X → ℂ)
    (hw : MemLp (fun x ↦ ρ x * w x) 2 μ) :
    MemLp (fun x ↦ ρ x * v x) 2 μ ∧
      lpNorm (fun x ↦ ρ x * v x) 2 μ = 2 * lpNorm (fun x ↦ ρ x * w x) 2 μ := by
  have he : (fun x ↦ ρ x * v x) =ᵐ[μ] (2 : ℝ) • (fun x ↦ ρ x * w x) := by
    rw [hvw]
    filter_upwards [Lp.coeFn_smul (2 : ℝ) w] with x hx
    change ρ x * (((2 : ℝ) • w) x) = (2 : ℝ) • (ρ x * w x)
    rw [hx]
    exact mul_smul_comm (2 : ℝ) (ρ x) (w x)
  refine ⟨(memLp_congr_ae he).mpr (hw.const_smul (2 : ℝ)), ?_⟩
  have hn : lpNorm (fun x ↦ ρ x * v x) 2 μ =
      lpNorm ((2 : ℝ) • (fun x ↦ ρ x * w x)) 2 μ := by
    rw [← toReal_eLpNorm, ← toReal_eLpNorm, eLpNorm_congr_ae he]
  rw [hn, lpNorm_const_smul]
  norm_num

variable {n : ℕ} {ι J : Type*} [Fintype ι] [MetricSpace ι] [DiscreteTopology ι]
  [MeasurableSpace ι] [BorelSpace ι] [Fintype J]

/-- Exact same-source coordinate identity for the original real native row.
The output datum may be the current uncut inverse applied to any smooth
source; only its proved all-order Sobolev membership is needed here. -/
theorem nativeRealSampledAdjoint_coordinate_eq_cut
    (μ : Measure (ι × Euclidean (n - 1))) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ : (ι × Euclidean (n - 1)) → Euclidean n → ℝ)
    (m : (ι × Euclidean (n - 1)) → ℝ)
    (a : Fin n → J → ι → Euclidean (n - 1) → Euclidean n → ℂ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (ha : ∀ i j k, ContDiff ℝ ∞ (Function.uncurry (a i j k)))
    {K : Set (Euclidean n)} (hK : IsCompact K) (has : ∀ i j k η, tsupport (a i j k η) ⊆ K)
    (hKcell : K ⊆ halfOpenCell n)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχK : ∀ x ∈ K, χ x = 1)
    (u : ContinuumRow.OutputL2 n) (hu : ∀ s, u ∈ periodicSobolevLevel n (Euclidean n) s) (j : J) :
    let S := nativeMatrixRowOperator μ volume (sampledMomentMatrixEntry μ φ m a hφ hm hms ha hK has)
    let r := regularSourceRepresentative u hu
    finiteL2CoordinateIsometry μ ((transferOutputOperator (realQuadratureChannel S)).adjoint u) j =
      (2 : ℝ) • finiteL2CoordinateIsometry μ
        (S.adjoint (l2ComplexInclusion volume ((cutSmoothResidual χ hχ hc r).toLp 2 volume))) j := by
  dsimp only
  let A := sampledMomentMatrixEntry μ φ m a hφ hm hms ha hK has
  let κ := fun i j x z ↦ sampledMomentKernel φ m (fun u ↦ a i j u.1 u.2) x z
  let r := regularSourceRepresentative u hu
  have he := nativeRealRow_adjoint_eq_cutSmoothResidual μ A κ
    (fun i j ↦ continuous_sampledMomentKernel φ m (fun u ↦ a i j u.1 u.2) hφ hm
      (continuous_originalSampledAmplitude (a i j) (ha i j)))
    (fun i j ↦ hasCompactSupport_sampledMomentKernel φ m (fun u ↦ a i j u.1 u.2)
      hms hK (fun u ↦ has i j u.1 u.2))
    (fun i j f ↦ sampledMomentOperator_ae_kernel μ φ m (fun u ↦ a i j u.1 u.2) hφ hm
      (continuous_originalSampledAmplitude (a i j) (ha i j)) hms hK (fun u ↦ has i j u.1 u.2) f)
    (fun i j x hx z ↦ by
      simp only [κ, sampledMomentKernel,
        image_eq_zero_of_notMem_tsupport (fun h ↦ hx (has i j z.1 z.2 h)), star_zero, mul_zero])
    hKcell χ hχ hc hχK r
  have hr : smoothResidualToL2 n r = u := regularSourceRepresentative_toL2 u hu
  rw [hr] at he
  rw [he]
  exact congrArg (fun z : PiLp 2 (fun _ : J ↦ Lp ℂ 2 μ) ↦ z j)
    (LinearMapClass.map_smul_of_tower (finiteL2CoordinateIsometry μ) (2 : ℝ) _)

omit [Fintype ι] [MetricSpace ι] [DiscreteTopology ι] [MeasurableSpace ι] [BorelSpace ι]
    [Fintype J] in
/-- The full real moment constant depends only on the fixed physical cutoff,
fixed coordinate dimension, primitive profiles and moment order. -/
def nativeRealMomentConstant
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ halfOpenCell n) (R : ℝ) (B : ℕ → ℝ) (q : ℕ) : ℝ :=
  2 * sampledRadialMomentConstant n R B q * sourceMomentConstant χ hχ hc hs q

/-- The actual original real sampled adjoint, applied to the SAME regular
periodic source, has the native radial moment bound. Applying this to the
proved regular datum `Q₀ e` retains the current uncut inverse; its source
Sobolev estimates can then be inserted without changing any row or sample. -/
theorem nativeRealSampledAdjoint_radial_L2_bound
    (μ : Measure (ι × Euclidean (n - 1))) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ : (ι × Euclidean (n - 1)) → Euclidean n → ℝ)
    (m : (ι × Euclidean (n - 1)) → ℝ)
    (a : Fin n → J → ι → Euclidean (n - 1) → Euclidean n → ℂ)
    (L : ι → Euclidean (n - 1) → Euclidean (n - 1) → Euclidean n → Euclidean n)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
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
    let S := nativeMatrixRowOperator μ volume (sampledMomentMatrixEntry μ φ m a hφ hm hms ha hK has)
    let raw := finiteL2CoordinateIsometry μ ((transferOutputOperator (realQuadratureChannel S)).adjoint u) j
    MemLp (fun z ↦ (‖z.2‖ : ℂ) ^ q * raw z) 2 μ ∧
      lpNorm (fun z ↦ (‖z.2‖ : ℂ) ^ q * raw z) 2 μ ≤
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
  let S := nativeMatrixRowOperator μ volume (sampledMomentMatrixEntry μ φ m a hφ hm hms ha hK has)
  let raw := finiteL2CoordinateIsometry μ ((transferOutputOperator (realQuadratureChannel S)).adjoint u) j
  let raw₀ := finiteL2CoordinateIsometry μ (S.adjoint V) j
  have hb := sampledMatrixAdjoint_coordinate_radial_L2_bound μ φ m a L hφ hm hms ha hL hK has
    χ hχ.continuous hc hχK R hbox T₀ hT₀ hφsmooth hphase B hB q r₀ hT hamp hcoeff v hv hvs j
  have he := nativeRealSampledAdjoint_coordinate_eq_cut μ φ m a hφ hm hms ha hK has hKcell
    χ hχ hc hχK u hu j
  change raw = (2 : ℝ) • finiteL2CoordinateIsometry μ
    (S.adjoint (l2ComplexInclusion volume ((cutSmoothResidual χ hχ hc r).toLp 2 volume))) j at he
  rw [← hV] at he
  have hreal := weightedNativeCoordinate_two μ raw raw₀ he (fun z ↦ (‖z.2‖ : ℂ) ^ q) hb.1
  have hsum : (∑ i : Fin n, ∑ k ∈ Finset.range (q + 1), T ^ (q - k - r₀) * fourierSobolevNorm k (f i)) ≤
      sourceMomentConstant χ hχ hc hs q *
        ∑ k ∈ Finset.range (q + 1), T ^ (q - k - r₀) * periodicSobolevNorm k u := by
    simpa only [hf, r, regularSourceRepresentative_sobolevNorm] using
      cutSmoothResidualCoordinate_moment_sum_le χ hχ hc hs q r₀ (zero_le_one.trans hT) r
  refine ⟨hreal.1, ?_⟩
  calc
    _ = 2 * lpNorm (fun z ↦ (‖z.2‖ : ℂ) ^ q * raw₀ z) 2 μ := hreal.2
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
