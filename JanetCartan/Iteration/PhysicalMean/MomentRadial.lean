module

public import JanetCartan.Iteration.PhysicalMean.MomentBounds
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Native radial moments of the original sampled adjoint

Convert the fixed coordinate moment words to the literal `|η|^q` multiplier
in `app:ch_mean_pairs:eq:raw-adjoint-moments`. Only the fixed transverse
dimension enters the conversion. The original measure and every sample,
shell and frequency coordinate remain unchanged.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators

namespace JanetCartan.PhysicalMean

/-- A fixed finite set of coordinate powers dominates the radial power,
including zero transverse dimension and order zero. No frequency cutoff
appears in the constant (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_pow_le_coordinate_powers {d : ℕ} (q : ℕ) (η : Euclidean d) :
    ‖η‖ ^ q ≤ ((d : ℝ) + 1) ^ q * (1 + ∑ i, |η i| ^ q) := by
  classical
  let a : Option (Fin d) → ℝ := Option.elim' 1 (fun i ↦ |η i|)
  have ha (i) : 0 ≤ a i := by cases i <;> simp [a]
  have hn : ‖η‖ ≤ ∑ i, |η i| := by
    apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ ↦ abs_nonneg (η i)))).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [sq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ) (fun i _ ↦ abs_nonneg (η i))
  have hsum : ‖η‖ ≤ ∑ i, a i := by
    simp only [Fintype.sum_option, a, Option.elim']
    linarith
  have hc : (1 : ℝ) ≤ (Finset.univ : Finset (Option (Fin d))).card := by simp
  have hp : (∑ i, a i) ^ q ≤
      ((Finset.univ : Finset (Option (Fin d))).card : ℝ) ^ q * ∑ i, a i ^ q := by
    cases q with
    | zero => simp
    | succ r =>
        exact (pow_sum_le_card_mul_sum_pow (fun i _ ↦ ha i) r).trans
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc (Nat.le_succ r))
            (Finset.sum_nonneg (fun i _ ↦ pow_nonneg (ha i) _)))
  simpa only [Finset.card_univ, Fintype.card_option, Fintype.card_fin, Nat.cast_add,
    Nat.cast_one, Fintype.sum_option, a, Option.elim', one_pow] using
      (pow_le_pow_left₀ (norm_nonneg _) hsum q).trans hp

/-- The fixed phase factors `I` in the exact IBP words do not change their
physical radial moment norms. This native-measure conversion is used for both
the common sampled row and the individual bare row. -/
theorem radialMoment_L2_of_coordinate_powers
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {d : ℕ}
    (η : X → Euclidean d) (hη : Measurable η) (f : X → ℂ) (hf : MemLp f 2 μ)
    (q : ℕ)
    (hpow : ∀ i : Fin d, MemLp (fun x ↦ (Complex.I * (η x i : ℂ)) ^ q * f x) 2 μ) :
    MemLp (fun x ↦ (‖η x‖ : ℂ) ^ q * f x) 2 μ ∧
      lpNorm (fun x ↦ (‖η x‖ : ℂ) ^ q * f x) 2 μ ≤ ((d : ℝ) + 1) ^ q *
        (lpNorm f 2 μ + ∑ i, lpNorm (fun x ↦ (Complex.I * (η x i : ℂ)) ^ q * f x) 2 μ) := by
  classical
  let a : Option (Fin d) → X → ℝ
    | none => fun x ↦ ‖f x‖
    | some i => fun x ↦ |η x i| ^ q * ‖f x‖
  have he (i : Fin d) : (fun x ↦ ‖(Complex.I * (η x i : ℂ)) ^ q * f x‖) = a (some i) := by
    funext x
    simp only [a, norm_mul, norm_pow, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
  have ha (i) : MemLp (a i) 2 μ := by
    cases i with
    | none => exact hf.norm
    | some i => rw [← he i]; exact (hpow i).norm
  let C : ℝ := ((d : ℝ) + 1) ^ q
  let g : X → ℝ := C • ∑ i, a i
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hg : MemLp g 2 μ := (memLp_finsetSum' Finset.univ (fun i _ ↦ ha i)).const_smul C
  have hp (x : X) : ‖(‖η x‖ : ℂ) ^ q * f x‖ ≤ g x := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    have h := mul_le_mul_of_nonneg_right (norm_pow_le_coordinate_powers q (η x)) (norm_nonneg (f x))
    convert h using 1
    simp only [g, C, Pi.smul_apply, smul_eq_mul, Fintype.sum_option, a,
      Pi.add_apply, Finset.sum_apply]
    rw [← Finset.sum_mul]
    ring
  have hw : AEStronglyMeasurable (fun x ↦ (‖η x‖ : ℂ) ^ q * f x) μ :=
    ((Complex.measurable_ofReal.comp hη.norm).pow_const q).aestronglyMeasurable.mul hf.aestronglyMeasurable
  refine ⟨hg.mono' hw (Filter.Eventually.of_forall hp), ?_⟩
  calc
    _ ≤ lpNorm g 2 μ := lpNorm_mono_real hg hp
    _ = C * lpNorm (∑ i, a i) 2 μ := by
      rw [lpNorm_const_smul]
      simp only [NNReal.coe_mk, Real.nnnorm_of_nonneg hC]
    _ ≤ C * ∑ i, lpNorm (a i) 2 μ :=
      mul_le_mul_of_nonneg_left (lpNorm_sum_le (fun i _ ↦ ha i) (by norm_num)) hC
    _ = _ := by
      rw [Fintype.sum_option]
      congr 1
      congr 1
      · exact lpNorm_norm hf.aestronglyMeasurable 2
      · apply Finset.sum_congr rfl
        intro i _
        rw [← he i, lpNorm_norm (hpow i).aestronglyMeasurable]

/-- Fixed coordinate word for the original transverse radial moment. -/
def radialMomentWord {n : ℕ} (q : ℕ) : Option (Fin (n - 1)) → List (Euclidean (n - 1))
  | none => []
  | some i => List.replicate q (EuclideanSpace.single i 1)

/-- The radial constant is chosen before the current map, original sample,
frequency cutoff and datum. Only fixed coordinate and IBP words are summed. -/
def sampledRadialMomentConstant (n : ℕ) (R : ℝ) (B : ℕ → ℝ) (q : ℕ) : ℝ :=
  (((n - 1 : ℕ) : ℝ) + 1) ^ q *
    ∑ i : Option (Fin (n - 1)), sampledMomentConstant n R B (radialMomentWord q i)

open Set ContinuumAdjoint.DerivativeKernels AmplitudeBound AmplitudeBound.PaperEstimates
open Pseudodifferential
open scoped ContDiff

variable {n : ℕ} {ι : Type*} [Fintype ι] [MetricSpace ι] [DiscreteTopology ι]
  [MeasurableSpace ι] [BorelSpace ι]

/-- The actual original radial adjoint moment follows from the unchanged
scalar row and the primitive physical coefficient profiles. It retains the
full phase, full corrected coefficient, original scalar masks and the SAME
native sample/shell measure. No radial moment estimate is an input
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem sampledRadialMoment_L2_bound
    (μ : Measure (ι × Euclidean (n - 1))) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ : (ι × Euclidean (n - 1)) → Euclidean n → ℝ)
    (m : (ι × Euclidean (n - 1)) → ℝ)
    (a : ι → Euclidean (n - 1) → Euclidean n → ℂ)
    (L : ι → Euclidean (n - 1) → Euclidean (n - 1) → Euclidean n → Euclidean n)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (ha : ∀ i, ContDiff ℝ ∞ (Function.uncurry (a i)))
    (hL : ∀ i h, ContDiff ℝ ∞ (fun p : Euclidean (n - 1) × Euclidean n ↦ L i p.1 h p.2))
    {K : Set (Euclidean n)} (hK : IsCompact K) (has : ∀ i η, tsupport (a i η) ⊆ K)
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
    (hamp : ∀ i η, m (i, η) ≠ 0 → ∀ x ∈ K, ∀ j, ‖iteratedFDeriv ℝ j (a i η) x‖ ≤
      B j * T ^ (j - (r₀ + (n / 2 + 1))))
    (hcoeff : ∀ i η, m (i, η) ≠ 0 → ∀ h, ‖h‖ ≤ 1 → ∀ x ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (L i η h) x‖ ≤ B j * T ^ (j - (r₀ + (n / 2 + 1))))
    (v : Euclidean n → ℂ) (hv : ContDiff ℝ ∞ v) (hvs : HasCompactSupport v) :
    let F := fun u ↦ (m u : ℂ) * chartAdjoint (φ u) (a u.1 u.2) v
    let f := (hv.continuous.memLp_of_hasCompactSupport hvs (p := 2) (μ := volume)).toLp v
    MemLp (fun u ↦ (‖u.2‖ : ℂ) ^ q * F u) 2 μ ∧
      lpNorm (fun u ↦ (‖u.2‖ : ℂ) ^ q * F u) 2 μ ≤
        sampledRadialMomentConstant n R B q * ‖T₀‖ *
          ∑ i ∈ Finset.range (q + 1), T ^ (q - i - r₀) * fourierSobolevNorm i f := by
  classical
  dsimp only
  let F := fun u : ι × Euclidean (n - 1) ↦ (m u : ℂ) * chartAdjoint (φ u) (a u.1 u.2) v
  let f := (hv.continuous.memLp_of_hasCompactSupport hvs (p := 2) (μ := volume)).toLp v
  let H := ∑ i ∈ Finset.range (q + 1), T ^ (q - i - r₀) * fourierSobolevNorm i f
  let C := fun i : Option (Fin (n - 1)) ↦ sampledMomentConstant n R B (radialMomentWord q i)
  have hC (i) : 0 ≤ C i := by
    dsimp only [C, sampledMomentConstant]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (finiteRowAmplitudeConstant_nonneg n R)) (momentAmplitudeTestConstant_nonneg B hB _ _))
      (by positivity)
  have hH : 0 ≤ H := Finset.sum_nonneg (fun i _ ↦ by unfold fourierSobolevNorm; positivity)
  have hbase := sampledMoment_L2_bound μ φ m a L hφ hm hms ha hL hK has χ hχ hχs hχK
    R hbox T₀ hT₀ hφsmooth hphase B hB [] r₀ hT hamp (by simp) v hv hvs
  have hF : MemLp F 2 μ := by simpa only [List.map_nil, List.prod_nil, one_mul] using hbase.1
  have hzero : lpNorm F 2 μ ≤ C none * ‖T₀‖ * H := by
    have h0 : fourierSobolevNorm 0 f ≤ H := by
      apply le_trans (b := T ^ (q - 0 - r₀) * fourierSobolevNorm 0 f)
      · exact le_mul_of_one_le_left (by unfold fourierSobolevNorm; positivity) (one_le_pow₀ hT)
      · dsimp only [H]
        simpa only [Nat.cast_zero] using Finset.single_le_sum
          (f := fun j ↦ T ^ (q - j - r₀) * fourierSobolevNorm j f)
          (s := Finset.range (q + 1)) (a := 0)
          (fun j _ ↦ by unfold fourierSobolevNorm; positivity) (Finset.mem_range.mpr (by omega))
    apply le_trans (b := C none * ‖T₀‖ * fourierSobolevNorm 0 f)
    · simpa only [C, radialMomentWord, F, f, List.map_nil, List.prod_nil, one_mul,
        List.length_nil, Nat.zero_sub, Nat.zero_add, Finset.range_one, Finset.sum_singleton,
        pow_zero, Nat.cast_zero, toReal_eLpNorm] using hbase.2
    · exact mul_le_mul_of_nonneg_left h0 (mul_nonneg (hC none) (norm_nonneg _))
  have hp (i : Fin (n - 1)) :
      MemLp (fun u ↦ (Complex.I * (u.2 i : ℂ)) ^ q * F u) 2 μ ∧
      lpNorm (fun u ↦ (Complex.I * (u.2 i : ℂ)) ^ q * F u) 2 μ ≤ C (some i) * ‖T₀‖ * H := by
    have hb := sampledMoment_L2_bound μ φ m a L hφ hm hms ha hL hK has χ hχ hχs hχK
      R hbox T₀ hT₀ hφsmooth hphase B hB (List.replicate q (EuclideanSpace.single i 1)) r₀ hT hamp
      (fun j η hm h hh ↦ by
        obtain ⟨_, rfl⟩ := List.mem_replicate.mp hh
        exact hcoeff j η hm _ (by simp [EuclideanSpace.single, PiLp.norm_single])) v hv hvs
    have he : (fun u : ι × Euclidean (n - 1) ↦ (m u : ℂ) *
        ((List.map (fun h ↦ Complex.I * (inner ℝ h u.2 : ℂ))
          (List.replicate q (EuclideanSpace.single i 1))).prod * chartAdjoint (φ u) (a u.1 u.2) v)) =
        (fun u ↦ (Complex.I * (u.2 i : ℂ)) ^ q * F u) := by
      funext u
      simp only [List.map_replicate, List.prod_replicate, EuclideanSpace.inner_single_left,
        map_one, one_mul, F]
      ring
    rw [he] at hb
    refine ⟨hb.1, ?_⟩
    simpa only [C, radialMomentWord, H, f, List.length_replicate, toReal_eLpNorm] using hb.2
  obtain ⟨hmem, hrad⟩ := radialMoment_L2_of_coordinate_powers μ Prod.snd measurable_snd F hF q
    (fun i ↦ (hp i).1)
  refine ⟨hmem, ?_⟩
  apply hrad.trans
  calc
    _ ≤ (((n - 1 : ℕ) : ℝ) + 1) ^ q *
        (C none * ‖T₀‖ * H + ∑ i, C (some i) * ‖T₀‖ * H) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add hzero (Finset.sum_le_sum (fun i _ ↦ (hp i).2))) (by positivity)
    _ = _ := by
      simp only [sampledRadialMomentConstant, ← Finset.sum_mul, ← add_mul,
        ← Fintype.sum_option]
      dsimp only [C, H, f]
      ring

end JanetCartan.PhysicalMean
