module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.Bounds
public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Quantitative.OneHigh.Composition
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.PhysicalBounds.Quotient

/-!
# Pulling primitive grades to the original rescaled slice chart

The substitution in `app:ch_waves:eq:phase-quotient` is polynomial in epsilon
and the original annular variable. Its jets are fixed geometric constants.
Composition with this map preserves the primitive reserve, as does multiplication
by the fixed physical and annular masks. These results supply the chart grades
used by `norm_iteratedFDeriv_sliceDerivativeAmplitude_le_fixedReserve`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.RawPrimary.SliceBounds
open FourierIntegral.NormalOneHigh

variable {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The fixed slice substitution spends no history reserve. Only primitive
orders through `k` are used (`app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_iteratedFDeriv_comp_le_sliceGrade
    {g : E → H} {f : H → F} {x : E} {k R : ℕ}
    (hg : ContDiffAt ℝ ∞ g x) (hf : ContDiffAt ℝ ∞ f (g x))
    {a c : ℕ → ℝ} (ha : ∀ j ≤ k, 0 ≤ a j)
    {L : ℝ} (hL : 1 ≤ L)
    (houter : ∀ j ≤ k, ‖iteratedFDeriv ℝ j f (g x)‖ ≤ a j * L ^ (j - R))
    (hinner : ∀ j, 1 ≤ j → j ≤ k → ‖iteratedFDeriv ℝ j g x‖ ≤ c j) :
    ‖iteratedFDeriv ℝ k (f ∘ g) x‖ ≤ compositionBudget a c k * L ^ (k - R) := by
  apply (CompositionBounds.norm_iteratedFDeriv_comp_le_partition_sum
    (hf.of_le (by simp : (k : ℕ∞ω) ≤ ∞))
    (hg.of_le (by simp : (k : ℕ∞ω) ≤ ∞)) le_rfl).trans
  rw [compositionBudget, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  have hc : 0 ≤ ∏ i, c (p.partSize i) := Finset.prod_nonneg fun i _ ↦
    (norm_nonneg _).trans (hinner _ (p.partSize_pos i) (p.partSize_le i))
  calc
    _ ≤ (a p.length * L ^ (p.length - R)) * ∏ i, c (p.partSize i) :=
      mul_le_mul (houter _ p.length_le)
        (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
          (fun i _ ↦ hinner _ (p.partSize_pos i) (p.partSize_le i)))
        (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))
        (mul_nonneg (ha _ p.length_le) (pow_nonneg (zero_le_one.trans hL) _))
    _ = (a p.length * ∏ i, c (p.partSize i)) * L ^ (p.length - R) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (Nat.sub_le_sub_right p.length_le R))
      (mul_nonneg (ha _ p.length_le) hc)

/-- Coefficient for a fixed mask multiplying a primitive graded field.
Its dependence is finite, through the stated jet order
(`app:ch_waves:eq:individual-raw-slice`). -/
def sliceMaskJetConstant (c a : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * c i * a (k - i)

/-- Positivity of the finite mask coefficient
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem sliceMaskJetConstant_nonneg {c a : ℕ → ℝ}
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ j, 0 ≤ a j) (k : ℕ) :
    0 ≤ sliceMaskJetConstant c a k :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (hc i)) (ha _)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Multiplication by a fixed smooth cutoff preserves the reserve, including
all parameter jets (`app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_iteratedFDeriv_mask_smul_le_sliceGrade
    {U : Set E} (hU : IsOpen U) {m : E → ℂ} {A : E → V}
    (hm : ContDiffOn ℝ ∞ m U) (hA : ContDiffOn ℝ ∞ A U)
    {x : E} (hx : x ∈ U) {k R : ℕ} {L : ℝ} (hL : 1 ≤ L)
    {c a : ℕ → ℝ} (hc : ∀ j ≤ k, 0 ≤ c j) (ha : ∀ j ≤ k, 0 ≤ a j)
    (hmask : ∀ j ≤ k, ‖iteratedFDeriv ℝ j m x‖ ≤ c j)
    (hamp : ∀ j ≤ k, ‖iteratedFDeriv ℝ j A x‖ ≤ a j * L ^ (j - R)) :
    ‖iteratedFDeriv ℝ k (fun y ↦ m y • A y) x‖ ≤
      sliceMaskJetConstant c a k * L ^ (k - R) := by
  have h := norm_iteratedFDerivWithin_smul_le hm hA hU.uniqueDiffOn hx
    (by simp : (k : ℕ∞ω) ≤ ∞)
  simp only [iteratedFDerivWithin_of_isOpen _ hU hx] at h
  apply h.trans
  rw [sliceMaskJetConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  calc
    _ ≤ (k.choose i : ℝ) * c i * (a (k - i) * L ^ (k - i - R)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hmask i hi') (Nat.cast_nonneg _))
        (hamp _ (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (hc i hi'))
    _ = ((k.choose i : ℝ) * c i * a (k - i)) * L ^ (k - i - R) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hc i hi')) (ha _ (Nat.sub_le _ _)))

variable {X P : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The original shifted chart, with physical coordinates retained and no
restriction or enlargement of the annulus (`app:ch_waves:eq:phase-quotient`). -/
def rawSliceShift (ζ : P) (t : ℝ) (q : ℝ × X × P) : X × P :=
  (q.2.1, ζ + (t * q.1) • q.2.2)

/-- Every joint jet of the actual substitution is a fixed geometric constant
on a compact buffered chart, uniformly on the quotient integration interval.
The constants are chosen before the primitive phase, amplitude and history
scale (`app:ch_waves:eq:phase-quotient`). -/
theorem exists_rawSliceShift_jetBounds (ζ : P) {K : Set (ℝ × X × P)}
    (hK : IsCompact K) :
    ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ q ∈ K, ∀ j,
        ‖iteratedFDeriv ℝ j (rawSliceShift ζ t) q‖ ≤ c j := by
  have h (j : ℕ) : ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ q ∈ K,
      ‖iteratedFDeriv ℝ j (rawSliceShift ζ t) q‖ ≤ C := by
    have hs : ContDiff ℝ ∞ (fun w : ℝ × (ℝ × X × P) ↦ rawSliceShift ζ w.1 w.2) := by
      unfold rawSliceShift
      fun_prop
    have hc : Continuous (fun w : ℝ × (ℝ × X × P) ↦
        iteratedFDeriv ℝ j (rawSliceShift ζ w.1) w.2) :=
      continuous_iff_continuousAt.mpr fun w ↦
        (NormalComparison.contDiffAt_segmentSpatialJet hs.contDiffAt j).continuousAt
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hc.continuousOn
    exact ⟨C, fun t ht q hq ↦ hC (t, q) ⟨ht, hq⟩⟩
  choose c hc using h
  exact ⟨fun j ↦ max 0 (c j), fun j ↦ le_max_left _ _,
    fun t ht q hq j ↦ (hc j t ht q hq).trans (le_max_right _ _)⟩

end JanetCartan.RawPrimary.SliceBounds
