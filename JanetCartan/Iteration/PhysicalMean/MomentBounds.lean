module

public import JanetCartan.Iteration.PhysicalMean.MomentRows
public import JanetCartan.Iteration.PhysicalMean.MomentFamily
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Interpolation
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Actual raw moment terms from the unchanged scalar tester

Each term in `app:ch_mean_pairs:eq:raw-adjoint-moments` is represented by the
Hilbert adjoint of a constructed modified row on the original source measure.
Its norm follows from the scalar tester and the original physical coefficient
profiles. There is no assumed modified-row or moment estimate. Only the fixed
physical test reserve is spent, with no dependence on the number of samples
or bands. The original-data scalar tests are produced by tasks 26 and 30;
the full corrected amplitude and inverse directions by tasks 13 and 28.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.PhysicalMean

open ContinuumAdjoint.DerivativeKernels AmplitudeBound AmplitudeBound.PaperEstimates
open Pseudodifferential

variable {n : ℕ} {ι : Type*} [Fintype ι] [MetricSpace ι] [DiscreteTopology ι]
  [MeasurableSpace ι] [BorelSpace ι]

variable (μ : Measure (ι × Euclidean (n - 1))) [IsLocallyFiniteMeasure μ] [SFinite μ]
  (φ : (ι × Euclidean (n - 1)) → Euclidean n → ℝ)
  (m : (ι × Euclidean (n - 1)) → ℝ)
  (a : ι → Euclidean (n - 1) → Euclidean n → ℂ)
  (L : ι → Euclidean (n - 1) → Euclidean (n - 1) → Euclidean n → Euclidean n)
  (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
  (ha : ∀ i, ContDiff ℝ ∞ (Function.uncurry (a i)))
  (hL : ∀ i h, ContDiff ℝ ∞ (fun q : Euclidean (n - 1) × Euclidean n ↦ L i q.1 h q.2))
  {K : Set (Euclidean n)} (hK : IsCompact K)
  (has : ∀ i η, tsupport (a i η) ⊆ K)
  (χ : Euclidean n → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
  (hχK : ∀ x ∈ K, χ x = 1)
  (R : ℝ) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ R)
  (T₀ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
  (hT₀ : ∀ f : Lp ℂ 2 μ, T₀ f =ᵐ[volume] fun x ↦ ∫ u,
    sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)) x u * f u ∂μ)

include hφ hm hms ha hL hK has hχ hχs hχK hbox hT₀

/-- Every actual frequency-dependent IBP term belongs to the SAME native
L² space, with the reserve-preserving source-order bound from the scalar test.
The data derivative is the original physical coordinate word, not a carrier
or frequency derivative (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem sampledMomentTemplate_L2_bound
    (B : ℕ → ℝ) (hB : ∀ q, 0 ≤ B q) (ds : List (Euclidean (n - 1)))
    (t : AdjointMomentTemplate n)
    (ht : t ∈ adjointMomentTemplates (ds.map InitialCarrierDerivative.initial))
    (r₀ : ℕ) {T : ℝ} (hT : 1 ≤ T)
    (hamp : ∀ i η, m (i, η) ≠ 0 → ∀ x ∈ K, ∀ j, ‖iteratedFDeriv ℝ j (a i η) x‖ ≤
      B j * T ^ (j - (r₀ + (n / 2 + 1))))
    (hcoeff : ∀ i η, m (i, η) ≠ 0 → ∀ h, h ∈ ds → ∀ x ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (L i η h) x‖ ≤ B j * T ^ (j - (r₀ + (n / 2 + 1))))
    (v : Euclidean n → ℂ) (hv : ContDiff ℝ ∞ v) (hvs : HasCompactSupport v) :
    let b := physicalMomentAmplitude t (fun u : ι × Euclidean (n - 1) ↦ a u.1 u.2)
      (fun u : ι × Euclidean (n - 1) ↦ L u.1 u.2)
    let f := (hv.continuous.memLp_of_hasCompactSupport hvs (p := 2) (μ := volume)).toLp v
    MemLp (fun u ↦ (m u : ℂ) * chartAdjoint (φ u) (b u)
      (euclideanCoordinateDerivList t.2 v)) 2 μ ∧
    (eLpNorm (fun u ↦ (m u : ℂ) * chartAdjoint (φ u) (b u)
      (euclideanCoordinateDerivList t.2 v)) 2 μ).toReal ≤
      finiteRowAmplitudeConstant n R * ‖T₀‖ * momentAmplitudeTestConstant B ds (n / 2 + 1) *
        T ^ (ds.length - t.2.length - r₀) *
        ((2 * Real.pi) ^ t.2.length * fourierSobolevNorm t.2.length f) := by
  classical
  dsimp only
  let a₀ := fun u : ι × Euclidean (n - 1) ↦ a u.1 u.2
  let L₀ := fun u : ι × Euclidean (n - 1) ↦ L u.1 u.2
  have ha₀ : ∀ u, ContDiff ℝ ∞ (a₀ u) :=
    fun u ↦ (ha u.1).comp (contDiff_const.prodMk contDiff_id)
  have hL₀ : ∀ u h, ContDiff ℝ ∞ (L₀ u h) :=
    fun u h ↦ (hL u.1 h).comp (contDiff_const.prodMk contDiff_id)
  let b := physicalMomentAmplitude t a₀ L₀
  have hb : Continuous (Function.uncurry b) :=
    continuous_discrete_physicalMomentAmplitude t a L ha hL
  have hbr := physicalMomentAmplitude_supported ds t ht a₀ L₀ hK.isClosed ha₀
    (fun u ↦ has u.1 u.2) hL₀
  let S := sampledMomentOperator μ φ m b hφ hm hb hms hK (fun u ↦ (hbr u).2)
  have hop : ‖S‖ ≤ finiteRowAmplitudeConstant n R * ‖T₀‖ *
      (momentAmplitudeTestConstant B ds (n / 2 + 1) * T ^ (ds.length - t.2.length - r₀)) := by
    apply norm_sampledMomentOperator_le_scalarTest_onMask μ φ m b hφ hm hb hms hK
      (fun u ↦ (hbr u).2) χ hχ hχs
      (fun u x hx ↦ hχK x ((hbr u).2 (subset_tsupport _ hx))) R _
      (mul_nonneg (momentAmplitudeTestConstant_nonneg B hB ds _) (by positivity))
      (fun u ↦ (hbr u).1) (fun u x hx ↦ hbox x ((hbr u).2 (subset_tsupport _ hx)))
    · intro u hu is his x
      exact physicalMomentAmplitude_coordinate_jet_le_onSupport B hB ds t ht a₀ L₀ ha₀ hL₀
        hK.isClosed (fun u ↦ has u.1 u.2) (n / 2 + 1) r₀ hT u
        (hamp u.1 u.2 hu) (hcoeff u.1 u.2 hu) is his x
    · exact hT₀
  let w := euclideanCoordinateDerivList t.2 v
  have hw : MemLp w 2 volume :=
    (contDiff_euclideanCoordinateDerivList hv _).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_euclideanCoordinateDerivList hvs _)
  have he := sampledMomentOperator_adjoint_ae μ φ m b hφ hm hb hms hK
    (fun u ↦ (hbr u).2) w hw
  have hmem : MemLp (fun u ↦ (m u : ℂ) * chartAdjoint (φ u) (b u) w) 2 μ :=
    (memLp_congr_ae he).mp (Lp.memLp (S.adjoint (hw.toLp w)))
  refine ⟨hmem, ?_⟩
  have hnorm : ‖hw.toLp w‖ ≤ (2 * Real.pi) ^ t.2.length *
      fourierSobolevNorm t.2.length
        ((hv.continuous.memLp_of_hasCompactSupport hvs (p := 2) (μ := volume)).toLp v) := by
    simpa only [Nat.cast_zero, zero_add, fourierSobolevNorm_zero] using
      fourierSobolevNorm_coordinateDerivList_toLp_le t.2 0 v hv hvs
  calc
    _ = ‖S.adjoint (hw.toLp w)‖ := by rw [Lp.norm_def, eLpNorm_congr_ae he]
    _ ≤ ‖S‖ * ‖hw.toLp w‖ := by
      simpa only [ContinuousLinearMap.adjoint.norm_map] using S.adjoint.le_opNorm (hw.toLp w)
    _ ≤ (finiteRowAmplitudeConstant n R * ‖T₀‖ *
        (momentAmplitudeTestConstant B ds (n / 2 + 1) * T ^ (ds.length - t.2.length - r₀))) *
        ((2 * Real.pi) ^ t.2.length * fourierSobolevNorm t.2.length
          ((hv.continuous.memLp_of_hasCompactSupport hvs (p := 2) (μ := volume)).toLp v)) := by
      apply mul_le_mul hop hnorm (norm_nonneg _)
      exact mul_nonneg (mul_nonneg (finiteRowAmplitudeConstant_nonneg n R) (norm_nonneg _))
        (mul_nonneg (momentAmplitudeTestConstant_nonneg B hB ds _) (by positivity))
    _ = _ := by ring

/-- The fixed raw moment constant depends on the physical box, finite word
and primitive jet constants, but not on the sample/band count, cutoff or scale. -/
def sampledMomentConstant (n : ℕ) (R : ℝ) (B : ℕ → ℝ)
    (ds : List (Euclidean (n - 1))) : ℝ :=
  (adjointMomentTemplates (ds.map InitialCarrierDerivative.initial)).length *
    finiteRowAmplitudeConstant n R * momentAmplitudeTestConstant B ds (n / 2 + 1) *
      (2 * Real.pi) ^ ds.length

/-- The literal original phase moment is in native L², with exactly the
`sum_i T^(q-i-s0) H^i` reserve profile. This applies on the SAME disjoint
sampled shell measure and on a single original sample; only the scalar test
operator changes. In particular the finite sum is over the FIXED derivative
templates, never over samples or frequency bands
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem sampledMoment_L2_bound
    (hφsmooth : ∀ u, ContDiff ℝ ∞ (φ u))
    (hphase : ∀ u, m u ≠ 0 → ∀ h x, x ∈ K →
      inner ℝ h u.2 = fderiv ℝ (φ u) x (L u.1 u.2 h x))
    (B : ℕ → ℝ) (hB : ∀ q, 0 ≤ B q) (ds : List (Euclidean (n - 1)))
    (r₀ : ℕ) {T : ℝ} (hT : 1 ≤ T)
    (hamp : ∀ i η, m (i, η) ≠ 0 → ∀ x ∈ K, ∀ j, ‖iteratedFDeriv ℝ j (a i η) x‖ ≤
      B j * T ^ (j - (r₀ + (n / 2 + 1))))
    (hcoeff : ∀ i η, m (i, η) ≠ 0 → ∀ h, h ∈ ds → ∀ x ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (L i η h) x‖ ≤ B j * T ^ (j - (r₀ + (n / 2 + 1))))
    (v : Euclidean n → ℂ) (hv : ContDiff ℝ ∞ v) (hvs : HasCompactSupport v) :
    let F := fun u ↦ (m u : ℂ) *
      ((ds.map (fun h ↦ Complex.I * (inner ℝ h u.2 : ℂ))).prod * chartAdjoint (φ u) (a u.1 u.2) v)
    let f := (hv.continuous.memLp_of_hasCompactSupport hvs (p := 2) (μ := volume)).toLp v
    MemLp F 2 μ ∧ (eLpNorm F 2 μ).toReal ≤ sampledMomentConstant n R B ds * ‖T₀‖ *
      ∑ i ∈ Finset.range (ds.length + 1), T ^ (ds.length - i - r₀) * fourierSobolevNorm i f := by
  classical
  dsimp only
  let ts := adjointMomentTemplates (ds.map InitialCarrierDerivative.initial)
  let a₀ := fun u : ι × Euclidean (n - 1) ↦ a u.1 u.2
  let L₀ := fun u : ι × Euclidean (n - 1) ↦ L u.1 u.2
  let f := (hv.continuous.memLp_of_hasCompactSupport hvs (p := 2) (μ := volume)).toLp v
  let term := fun t : AdjointMomentTemplate n ↦ fun u : ι × Euclidean (n - 1) ↦
    (m u : ℂ) * chartAdjoint (φ u) (physicalMomentAmplitude t a₀ L₀ u)
      (euclideanCoordinateDerivList t.2 v)
  have ht (i : Fin ts.length) :=
    sampledMomentTemplate_L2_bound μ φ m a L hφ hm hms ha hL hK has χ hχ hχs hχK R hbox T₀ hT₀
      B hB ds (ts.get i) (List.get_mem ts i) r₀ hT hamp hcoeff v hv hvs
  have hmterm (i : Fin ts.length) : MemLp (term (ts.get i)) 2 μ := (ht i).1
  have he : (∑ i : Fin ts.length, term (ts.get i)) = fun u ↦ (m u : ℂ) *
      ((ds.map (fun h ↦ Complex.I * (inner ℝ h u.2 : ℂ))).prod * chartAdjoint (φ u) (a u.1 u.2) v) := by
    funext u
    simp only [Finset.sum_apply]
    calc
      _ = (ts.map (fun t ↦ term t u)).sum := by
        rw [← List.sum_ofFn]
        congr 1
        change List.ofFn ((fun t ↦ term t u) ∘ ts.get) = _
        rw [← List.map_ofFn, List.ofFn_get]
      _ = (m u : ℂ) * (ts.map (fun t ↦ chartAdjoint (φ u)
          (physicalMomentAmplitude t a₀ L₀ u) (euclideanCoordinateDerivList t.2 v))).sum :=
        List.sum_map_mul_left _ _ _
      _ = _ := by
        by_cases hu : m u = 0
        · simp only [hu, Complex.ofReal_zero, zero_mul]
        · rw [physicalMomentAmplitude_sum_realizes ds a₀ L₀ hK u (hφsmooth u)
            ((ha u.1).comp (contDiff_const.prodMk contDiff_id)) (has u.1 u.2)
            (fun h ↦ (hL u.1 h).comp (contDiff_const.prodMk contDiff_id)) v hv u.2 (hphase u hu)]
  have hsumMem : MemLp (∑ i : Fin ts.length, term (ts.get i)) 2 μ :=
    memLp_finsetSum' _ (fun i _ ↦ hmterm i)
  refine ⟨by rw [he] at hsumMem; exact hsumMem, ?_⟩
  have hn := lpNorm_sum_le (s := Finset.univ) (f := fun i : Fin ts.length ↦ term (ts.get i))
    (fun i _ ↦ hmterm i) (by norm_num : (1 : ENNReal) ≤ 2)
  simp only [← toReal_eLpNorm] at hn
  rw [he] at hn
  apply hn.trans
  let A := finiteRowAmplitudeConstant n R * ‖T₀‖ * momentAmplitudeTestConstant B ds (n / 2 + 1)
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg (finiteRowAmplitudeConstant_nonneg n R) (norm_nonneg _))
    (momentAmplitudeTestConstant_nonneg B hB ds _)
  let H := ∑ i ∈ Finset.range (ds.length + 1),
    T ^ (ds.length - i - r₀) * fourierSobolevNorm i f
  have hH : 0 ≤ H := Finset.sum_nonneg (fun i _ ↦ by
    unfold fourierSobolevNorm
    positivity)
  calc
    _ ≤ ∑ _i : Fin ts.length, (A * (2 * Real.pi) ^ ds.length * H) := by
      apply Finset.sum_le_sum
      intro i _
      have hg := (adjointMomentTemplate_grade (ds.map InitialCarrierDerivative.initial)
        (ts.get i) (List.get_mem ts i)).1
      have hk : (ts.get i).2.length ≤ ds.length := by
        simp only [List.length_map] at hg
        omega
      have hp : (2 * Real.pi) ^ (ts.get i).2.length ≤ (2 * Real.pi) ^ ds.length :=
        pow_le_pow_right₀ (by linarith [Real.two_le_pi]) hk
      have hs : T ^ (ds.length - (ts.get i).2.length - r₀) *
          fourierSobolevNorm (ts.get i).2.length f ≤ H := by
        dsimp only [H]
        exact Finset.single_le_sum
          (f := fun j ↦ T ^ (ds.length - j - r₀) * fourierSobolevNorm j f)
          (s := Finset.range (ds.length + 1)) (a := (ts.get i).2.length)
          (fun j _ ↦ by unfold fourierSobolevNorm; positivity)
          (Finset.mem_range.mpr (by omega))
      calc
        _ ≤ A * T ^ (ds.length - (ts.get i).2.length - r₀) *
            ((2 * Real.pi) ^ (ts.get i).2.length * fourierSobolevNorm (ts.get i).2.length f) := (ht i).2
        _ = (A * (2 * Real.pi) ^ (ts.get i).2.length) *
            (T ^ (ds.length - (ts.get i).2.length - r₀) * fourierSobolevNorm (ts.get i).2.length f) := by ring
        _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hp hA) hs
          (by unfold fourierSobolevNorm; positivity) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp only [sampledMomentConstant, A, H, ts, f]
      ring

end JanetCartan.PhysicalMean
