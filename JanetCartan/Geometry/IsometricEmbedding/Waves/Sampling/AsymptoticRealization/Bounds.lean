module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.KernelRealization

/-!
# Uniform scalar bounds for the actual refined sampling input

These bounds are consumed by `Sampling.AsymptoticRealization`, at the mesh of
`app:ch_waves:thm:sampling`. The factors three, `1 + 2^n`, and four come from
the proved refined row/trace estimates and `cutoffCount_ceiling` respectively.
The constants are positive upper bounds even for zero channels.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators

namespace JanetCartan.Sampling.AsymptoticRealization
open SeparatedSampling RawInputPartition SamplingKernelBounds

variable {A : Type*} [Fintype A] {n p : ℕ}

/-- The actual grouped-prefix count in `app:ch_waves:eq:sampling-all-prefixes`.
The harmless linear bound is uniform in the changing cutoff count. -/
theorem cutoffCount_prefix_card_le {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ((Finset.range (cutoffCount Λ + 1)).card : ℝ) ≤ 4 * Λ := by
  have hpow : ∀ j : ℕ, (j + 1 : ℝ) ≤ (2 : ℝ) ^ j := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [pow_succ]
      push_cast
      have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      linarith
  simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using
    (hpow (cutoffCount Λ)).trans (cutoffCount_ceiling hΛ)

/-- Positive block upper coefficient, consumed by the source-scale Bernstein
application in `app:ch_waves:eq:sampling-all-prefixes`. -/
def blockConstant (p : ℕ) (P : A → ℝ) (C_op : ℝ) : ℝ :=
  1 + 12 * C_op * nodesPerBlock p * ∑ a, P a

/-- Positive mean/trace upper coefficient, consumed by the source-scale
Bernstein application in `app:ch_waves:eq:sampling-all-prefixes`. -/
def meanConstant (n p : ℕ) (B : ℝ) (P Q : A → ℝ) (C_mean : ℝ) : ℝ :=
  1 + |C_mean| + (4 : ℝ) ^ n *
    ∑ a, (Q a * (1 + (2 : ℝ) ^ n)) * (countConstant p B * (P a * 1 ^ 3))

variable {ψ : A → Point → ℝ} {B C_op C_mean : ℝ} {P Q : A → ℝ}

omit [Fintype A] in
private theorem patch_bound_nonneg (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (a : A) :
    0 ≤ P a := (hψ a).nonneg 0 |>.trans ((hψ a).le_bound 0)

omit [Fintype A] in
private theorem patch_count_nonneg (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (a : A) :
    0 ≤ countConstant p B * (P a * 1 ^ 3) := by
  have hB := (hψ a).radius_nonneg
  have hP := patch_bound_nonneg hψ a
  unfold countConstant blockCountConstant
  positivity

/-- The block coefficient stays strictly positive when all operators vanish
(`app:ch_waves:thm:sampling`). -/
theorem blockConstant_pos (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hC_op : 0 ≤ C_op) :
    0 < blockConstant p P C_op := by
  have hP := Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) ↦ patch_bound_nonneg hψ a)
  unfold blockConstant
  positivity

/-- The mean/trace coefficient dominates the primitive full-normal bound and
is positive even when the actual variance vanishes (`app:ch_waves:thm:sampling`). -/
theorem meanConstant_bounds (hψ : ∀ a, PatchBounds (ψ a) B (P a))
    (hQ : ∀ a, 0 ≤ Q a) :
    0 < meanConstant n p B P Q C_mean ∧ C_mean ≤ meanConstant n p B P Q C_mean := by
  have hsum : 0 ≤ ∑ a, (Q a * (1 + (2 : ℝ) ^ n)) *
      (countConstant p B * (P a * 1 ^ 3)) :=
    Finset.sum_nonneg fun a _ ↦ mul_nonneg (mul_nonneg (hQ a) (by positivity)) (patch_count_nonneg hψ a)
  have hprod := mul_nonneg (show 0 ≤ (4 : ℝ) ^ n by positivity) hsum
  dsimp [meanConstant]
  constructor
  · positivity
  · linarith [le_abs_self C_mean]

/-- Literal block mass times the factor-three refined row estimate, at the
rounded ceiling (`app:ch_waves:eq:sampling-all-prefixes`). -/
theorem block_le (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hC_op : 0 ≤ C_op)
    {Λ h : ℝ} (hΛ : 1 ≤ Λ) (hh : 0 ≤ h) (a : A) :
    (nodesPerBlock p : ℝ) * (h ^ 3 * (P a * 1 ^ 3)) *
      ((3 * C_op) * (2 : ℝ) ^ cutoffCount Λ) ≤
        blockConstant p P C_op * (Λ * h ^ 3) := by
  have hP := patch_bound_nonneg hψ a
  have hPa : P a ≤ ∑ b, P b :=
    Finset.single_le_sum (fun b _ ↦ patch_bound_nonneg hψ b) (Finset.mem_univ a)
  have hΛpos : 0 ≤ Λ := zero_le_one.trans hΛ
  calc
    _ ≤ (nodesPerBlock p : ℝ) * (h ^ 3 * (P a * 1 ^ 3)) *
        ((3 * C_op) * (4 * Λ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (cutoffCount_ceiling hΛ) (by positivity)) (by positivity)
    _ = (12 * C_op * nodesPerBlock p * P a) * (Λ * h ^ 3) := by ring
    _ ≤ blockConstant p P C_op * (Λ * h ^ 3) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have := mul_le_mul_of_nonneg_left hPa
        (show 0 ≤ 12 * C_op * nodesPerBlock p by positivity)
      dsimp [blockConstant]
      linarith

/-- The literal refined trace bound from `operatorBernstein_refinedKernelPrefix`,
with the same original band kernel on both shells
(`app:ch_waves:eq:sampling-operator-bounds`). -/
def traceBound {J : ℕ}
    (D : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (B : ℝ) (P : A → ℝ) : ℝ :=
  (∑ a, ((D a).squaredKernelConstant * (1 + (2 : ℝ) ^ n)) *
    (countConstant p B * (P a * 1 ^ 3))) * ((2 : ℝ) ^ J) ^ n

/-- The primitive kernel constants give the source-scale trace estimate;
no trace or row estimate is assumed (`app:ch_waves:eq:sampling-all-prefixes`). -/
theorem traceBound_bounds {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (D : A → BandKernelData (Fin (cutoffCount Λ) × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hQ : ∀ a, 0 ≤ Q a)
    (hkernel : ∀ a, (D a).squaredKernelConstant ≤ Q a) :
    0 ≤ traceBound D B P ∧
      traceBound D B P ≤ meanConstant n p B P Q C_mean * Λ ^ n := by
  have hΛpos : 0 ≤ Λ := zero_le_one.trans hΛ
  have hnon a : 0 ≤ ((D a).squaredKernelConstant * (1 + (2 : ℝ) ^ n)) *
      (countConstant p B * (P a * 1 ^ 3)) :=
    mul_nonneg (mul_nonneg (D a).squaredKernelConstant_nonneg (by positivity))
      (patch_count_nonneg hψ a)
  have hsum := Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) ↦ hnon a)
  have hsumQ : 0 ≤ ∑ a, (Q a * (1 + (2 : ℝ) ^ n)) *
      (countConstant p B * (P a * 1 ^ 3)) :=
    Finset.sum_nonneg fun a _ ↦ mul_nonneg (mul_nonneg (hQ a) (by positivity)) (patch_count_nonneg hψ a)
  refine ⟨mul_nonneg hsum (by positivity), ?_⟩
  calc
    _ ≤ (∑ a, (Q a * (1 + (2 : ℝ) ^ n)) *
        (countConstant p B * (P a * 1 ^ 3))) * (4 * Λ) ^ n := by
      apply mul_le_mul _ (pow_le_pow_left₀ (by positivity) (cutoffCount_ceiling hΛ) n)
        (by positivity) hsumQ
      exact Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hkernel a) (by positivity)) (patch_count_nonneg hψ a)
    _ ≤ meanConstant n p B P Q C_mean * Λ ^ n := by
      rw [mul_pow]
      dsimp [meanConstant]
      nlinarith [pow_nonneg hΛpos n, abs_nonneg C_mean]

/-- The scalar tail of the actual cutoff family has the source polynomial
prefactor. This estimate supplies the strict budget to
`exists_refinedKernelPrefix_realization` (`app:ch_waves:eq:sampling-all-prefixes`). -/
theorem cutoff_bernsteinTail_le {Λ R C T t c ε : ℝ} (hΛ : 1 ≤ Λ)
    (hR : 0 < R) (hC : 0 < C) (hT : T ≤ C * Λ ^ n)
    (hexp : c * Λ ^ (ε / 2) ≤ t ^ 2 / (2 * (R * C + R * t / 3))) :
    (cutoffCount Λ + 1 : ENNReal) * OperatorCompression.bernsteinTail R (R * C) (R * T) t ≤
      ENNReal.ofReal (56 * Λ ^ (n + 1) * Real.exp (-c * Λ ^ (ε / 2))) := by
  have hΛpos : 0 ≤ Λ := zero_le_one.trans hΛ
  have htail : OperatorCompression.bernsteinTail R (R * C) (R * T) t ≤
      ENNReal.ofReal (14 * Λ ^ n * Real.exp (-c * Λ ^ (ε / 2))) := by
    apply ENNReal.ofReal_le_ofReal
    have hratio : 14 * (R * T) / (R * C) ≤ 14 * Λ ^ n := by
      apply (div_le_iff₀ (mul_pos hR hC)).2
      nlinarith [mul_le_mul_of_nonneg_left hT hR.le]
    apply mul_le_mul hratio _ (Real.exp_pos _).le (by positivity)
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    linarith
  apply (mul_le_mul_right htail _).trans
  have hcount := cutoffCount_prefix_card_le hΛ
  simp only [Finset.card_range, Nat.cast_add, Nat.cast_one] at hcount
  have he : (cutoffCount Λ + 1 : ENNReal) = ENNReal.ofReal (cutoffCount Λ + 1) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  rw [he, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (4 * Λ) * (14 * Λ ^ n * Real.exp (-c * Λ ^ (ε / 2))) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by ring

end JanetCartan.Sampling.AsymptoticRealization
