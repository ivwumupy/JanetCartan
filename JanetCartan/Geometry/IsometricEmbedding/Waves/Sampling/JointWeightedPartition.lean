module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.JointDetectorMasks

/-!
# Exact carrier weights for the joint cone refinement

The angular partition alone does not preserve an original carrier weight.
For every subset of the selected charts, split that weight by the product
of its carrier bumps and the complementary bumps. These products form an
exact partition. On an active product, every carrier plateau needed by the
angular subcover remains available. The resulting localizations are separated
products of carrier and angular functions, as required by `FiniteRealization`.
-/

@[expose] public noncomputable section
open Set Metric NormedSpace
open scoped ContDiff

namespace JanetCartan.Sampling
open SeparatedSampling ContinuumRow.CanonicalConic

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Split the ORIGINAL carrier weight by a subset of the selected carrier
bumps. No normalization depending jointly on carrier and frequency is added
(`app:ch_waves:thm:sampling`). -/
def carrierSubsetWeight (ψ : Point → ℝ) (b : I → Point → ℝ)
    (s : Finset I) (z : Point) : ℝ :=
  ψ z * ((∏ i ∈ s, b i z) * ∏ i ∈ sᶜ, (1 - b i z))

/-- The subset weights sum to the original weight everywhere, including
outside the detector support (`app:ch_waves:thm:sampling`). -/
theorem sum_carrierSubsetWeight (ψ : Point → ℝ) (b : I → Point → ℝ) (z : Point) :
    ∑ s : Finset I, carrierSubsetWeight ψ b s z = ψ z := by
  simp only [carrierSubsetWeight, ← Finset.mul_sum, ← Fintype.prod_add,
    add_sub_cancel, Finset.prod_const_one, mul_one]

/-- Each nonzero subset weight retains the original support and lies in
EVERY selected carrier bump's support (`app:ch_waves:thm:sampling`). -/
theorem carrierSubsetWeight_support (ψ : Point → ℝ) (b : I → Point → ℝ)
    (s : Finset I) {z : Point} (h : carrierSubsetWeight ψ b s z ≠ 0) :
    ψ z ≠ 0 ∧ ∀ i ∈ s, b i z ≠ 0 := by
  have hprod := mul_ne_zero_iff.mp h
  exact ⟨hprod.1, Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod.2).1⟩

/-- An active subset must contain every carrier bump which equals one at
that point. This preserves the SAME label of the joint covering rectangle
(`app:ch_waves:thm:sampling`). -/
theorem mem_of_carrierSubsetWeight_ne_zero (ψ : Point → ℝ) (b : I → Point → ℝ)
    (s : Finset I) {z : Point} (h : carrierSubsetWeight ψ b s z ≠ 0)
    {i : I} (hi : b i z = 1) : i ∈ s := by
  by_contra hs
  have hz : (∏ j ∈ sᶜ, (1 - b j z)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_compl.mpr hs) (by rw [hi, sub_self])
  simp [carrierSubsetWeight, hz] at h

/-- Smooth original weights and bumps give smooth subset weights; only
carrier derivatives are introduced (`app:ch_waves:eq:background-quadrature`). -/
theorem carrierSubsetWeight_contDiff (ψ : Point → ℝ) (b : I → Point → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hb : ∀ i, ContDiff ℝ ∞ (b i)) (s : Finset I) :
    ContDiff ℝ ∞ (carrierSubsetWeight ψ b s) :=
  hψ.mul ((contDiff_prod (fun i _ ↦ hb i)).mul
    (contDiff_prod (fun i _ ↦ contDiff_const.sub (hb i))))

/-- The original compact support is retained by every subset weight
(`app:ch_waves:thm:sampling`). -/
theorem carrierSubsetWeight_hasCompactSupport (ψ : Point → ℝ) (b : I → Point → ℝ)
    (hψ : HasCompactSupport ψ) (s : Finset I) :
    HasCompactSupport (carrierSubsetWeight ψ b s) := hψ.mul_right

/-- The carrier refinement has nonnegative weights bounded by the original
weight, with no loss in the original sampling cube (`app:ch_waves:thm:sampling`). -/
theorem carrierSubsetWeight_mem_Icc (ψ : Point → ℝ) (b : I → Point → ℝ)
    (hψ : ∀ z, 0 ≤ ψ z) (hb : ∀ i z, b i z ∈ Icc (0 : ℝ) 1)
    (s : Finset I) (z : Point) : carrierSubsetWeight ψ b s z ∈ Icc 0 (ψ z) := by
  have hp : 0 ≤ ∏ i ∈ s, b i z := Finset.prod_nonneg (fun i _ ↦ (hb i z).1)
  have hq : 0 ≤ ∏ i ∈ sᶜ, (1 - b i z) :=
    Finset.prod_nonneg (fun i _ ↦ sub_nonneg.mpr (hb i z).2)
  have hp₁ : (∏ i ∈ s, b i z) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ ↦ (hb i z).1) (fun i _ ↦ (hb i z).2)
  have hq₁ : (∏ i ∈ sᶜ, (1 - b i z)) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ ↦ sub_nonneg.mpr (hb i z).2)
      (fun i _ ↦ by linarith [(hb i z).1])
  exact ⟨mul_nonneg (hψ z) (mul_nonneg hp hq),
    (mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_right hp₁ hq).trans (by simpa using hq₁)) (hψ z)).trans_eq
        (mul_one (ψ z))⟩

/-- The literal `PatchBounds` input of `FiniteRealization` follows for every
subset from the original patch bounds (`app:ch_waves:thm:sampling`). -/
theorem carrierSubsetWeight_patchBounds (ψ : Point → ℝ) (b : I → Point → ℝ)
    {B P : ℝ} (hψ : PatchBounds ψ B P) (hb : ∀ i z, b i z ∈ Icc (0 : ℝ) 1)
    (s : Finset I) : PatchBounds (carrierSubsetWeight ψ b s) B P where
  radius_nonneg := hψ.radius_nonneg
  nonneg z := (carrierSubsetWeight_mem_Icc ψ b hψ.nonneg hb s z).1
  le_bound z := ((carrierSubsetWeight_mem_Icc ψ b hψ.nonneg hb s z).2).trans (hψ.le_bound z)
  support z hz := hψ.support z (carrierSubsetWeight_support ψ b s hz).1

variable {n : ℕ} (ηb : I → Euclidean (n - 1)) (r : I → ℝ)
    (hηb : ∀ i, ηb i ≠ 0) (hr : ∀ i, 0 < r i)

/-- Use the already constructed canonical angular square masks on the
subset of charts retained by a carrier weight (`app:ch_waves:thm:sampling`). -/
def subsetAngularMask (s : Finset I) : s → Euclidean (n - 1) → ℝ :=
  canonicalAngularSquareMask (fun i : s ↦ ηb i) (fun i ↦ r i)
    (fun i ↦ hηb i) (fun i ↦ hr i)

/-- On an active carrier subset, a SAME-label covering rectangle supplies
the exact angular square partition, without shrinking the original support
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem subsetAngularMask_sum_sq (ψ : Point → ℝ) (b : I → Point → ℝ)
    (s : Finset I) {z : Point} {η : Euclidean (n - 1)}
    (hs : carrierSubsetWeight ψ b s z ≠ 0)
    (hcover : ∃ i, b i z = 1 ∧ normalize η ∈
      ball (normalize (ηb i)) (angularWidth (ηb i) (r i) / 4)) :
    ∑ i : s, subsetAngularMask ηb r hηb hr s i η ^ 2 = 1 := by
  obtain ⟨i, hi, hdir⟩ := hcover
  have his := mem_of_carrierSubsetWeight_ne_zero ψ b s hs hi
  exact canonicalAngularSquareMask_sum_sq _ _ _ _
    (S := {normalize η}) (fun θ hθ ↦ by
      rcases Set.mem_singleton_iff.mp hθ with rfl
      exact ⟨⟨i, his⟩, hdir⟩) (Set.mem_singleton _)

/-- Exact separated carrier/angular reassembly on the joint cover. The
weights are CONSTRUCTED from the original weight and the actual carrier
bumps, while the angular masks use the same selected labels
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sum_carrierSubsetWeight_mul_subsetAngularMask_sq
    (ψ : Point → ℝ) (b : I → Point → ℝ) (z : Point) (η : Euclidean (n - 1))
    (hcover : ψ z ≠ 0 → ∃ i, b i z = 1 ∧ normalize η ∈
      ball (normalize (ηb i)) (angularWidth (ηb i) (r i) / 4)) :
    ∑ s : Finset I, ∑ i : s,
      carrierSubsetWeight ψ b s z * subsetAngularMask ηb r hηb hr s i η ^ 2 = ψ z := by
  calc
    _ = ∑ s : Finset I, carrierSubsetWeight ψ b s z := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.mul_sum]
      by_cases hs : carrierSubsetWeight ψ b s z = 0
      · simp [hs]
      · rw [subsetAngularMask_sum_sq ηb r hηb hr ψ b s hs
          (hcover (carrierSubsetWeight_support ψ b s hs).1), mul_one]
    _ = ψ z := sum_carrierSubsetWeight ψ b z

end JanetCartan.Sampling
