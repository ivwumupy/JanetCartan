module
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.Masks
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# First derivatives of the literal colored masks

The mask derivative input to `exists_colored_prefix_homotopy_bound`, for
`app:ch_waves:eq:colored-normal-comparison`. The masks are exactly
`BackgroundQuadrature.coloredBlockMask` with the convolved-box window and the
original finite block cutoff. A constant depending only on the fixed kernel
and window order bounds their first derivatives by `L / h`.

The compact smooth product window has a bounded first derivative. Translation
and dilation give the bound for each block. At any point, at most one block of
a given color is nonzero; every other block has zero derivative there because
it is nonnegative. Thus summing costs no block-count factor. Affine pullback
costs only the operator norm of its linear part, independently of the spectator
offset. No higher derivative budgets or normal-operator estimates are assumed.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
namespace JanetCartan.Sampling.ColoredNormalComparison
open SeparatedSampling LatticeQuadrature BackgroundQuadrature

/-- The support diameter is strictly smaller than the same-color coordinate
spacing, as used in `app:ch_waves:eq:colored-normal-comparison`. -/
private theorem blockWeight_same_color_unique {p : ℕ} {w : ℝ → ℝ} {W : ℝ}
    (hw : WindowBounds p w W) {h : ℝ} {q r : Lattice} {z : Point}
    (hc : color p q = color p r)
    (hq : blockWeight w h q z ≠ 0) (hr : blockWeight w h r z ≠ 0) : q = r := by
  funext i
  by_contra hi
  have hg := color_coordinate_gap hc hi
  have hq' := hw.support _ ((Finset.prod_ne_zero_iff.mp hq) i (Finset.mem_univ i))
  have hr' := hw.support _ ((Finset.prod_ne_zero_iff.mp hr) i (Finset.mem_univ i))
  have ht : |(q i : ℝ) - (r i : ℝ)| ≤
      |z i / h - (q i : ℝ)| + |z i / h - (r i : ℝ)| := by
    calc
      _ = |-(z i / h - (q i : ℝ)) + (z i / h - (r i : ℝ))| := by
        congr 1; ring
      _ ≤ _ := by
        simpa only [abs_neg] using abs_add_le (-(z i / h - (q i : ℝ))) (z i / h - (r i : ℝ))
  dsimp [windowRadius] at hq' hr'
  linarith

/-- Zero blocks have a local minimum, so they do not contribute to the first
mask derivative in `app:ch_waves:eq:colored-normal-comparison`. -/
private theorem fderiv_blockWeight_eq_zero {w : ℝ → ℝ}
    (hw : ∀ t, 0 ≤ w t) {h : ℝ} {q : Lattice} {z : Point}
    (hz : blockWeight w h q z = 0) : fderiv ℝ (blockWeight w h q) z = 0 := by
  apply IsLocalMin.fderiv_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  change blockWeight w h q z ≤ blockWeight w h q y
  rw [hz]
  exact Finset.prod_nonneg fun _ _ ↦ hw _

/-- The fixed product-window derivative bound scales by exactly `h⁻¹` for
every translated block in `app:ch_waves:eq:colored-normal-comparison`. -/
private theorem exists_blockWeight_fderiv_bound {p : ℕ} {w : ℝ → ℝ} {W : ℝ}
    (hw : WindowBounds p w W) (hs : ContDiff ℝ ∞ w) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (h : ℝ), 0 < h → ∀ (q : Lattice) (z : Point),
      ‖fderiv ℝ (blockWeight w h q) z‖ ≤ L / h := by
  have hc : HasCompactSupport (blockWeight w 1 0) := by
    apply HasCompactSupport.intro
      (isCompact_Icc (a := fun _ : Fin 3 ↦ -windowRadius p)
        (b := fun _ ↦ windowRadius p))
    intro z hz
    by_contra hn
    apply hz
    have hb (i : Fin 3) : |z i| ≤ windowRadius p := by
      simpa [blockWeight] using hw.support _
        ((Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i))
    exact ⟨fun i ↦ (abs_le.mp (hb i)).1, fun i ↦ (abs_le.mp (hb i)).2⟩
  have hd := contDiff_blockWeight hs 1 0
  obtain ⟨L, hL⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hd.continuous_fderiv (by simp))
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  refine ⟨L, hL0, ?_⟩
  intro h hh q z
  let a : Point → Point := fun x ↦ h⁻¹ • x - fun i ↦ (q i : ℝ)
  have ha : HasFDerivAt a (h⁻¹ • ContinuousLinearMap.id ℝ Point) z :=
    ((hasFDerivAt_id z).const_smul h⁻¹).sub_const _
  have he : blockWeight w h q = blockWeight w 1 0 ∘ a := by
    funext x
    simp [blockWeight, a, div_eq_mul_inv, mul_comm]
  rw [he, fderiv_comp z ((hd.differentiable (by simp)) (a z)) ha.differentiableAt,
    ha.fderiv]
  calc
    _ ≤ ‖fderiv ℝ (blockWeight w 1 0) (a z)‖ *
        ‖h⁻¹ • ContinuousLinearMap.id ℝ Point‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ L * ‖h⁻¹ • ContinuousLinearMap.id ℝ Point‖ :=
      mul_le_mul_of_nonneg_right (hL _) (norm_nonneg _)
    _ = L / h := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos hh, div_eq_mul_inv]

/-- Uniform first derivative bound for every finite submask of the actual
convolved-box partition. The constant precedes the finite enumeration, mesh,
color and evaluation point. This supplies the mask derivative input of
`exists_colored_prefix_homotopy_bound` without a block-count loss
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem exists_coloredBlockMask_fderiv_bound {κ : ℝ → ℝ} (hc : HasCompactSupport κ)
    (hs : ContDiff ℝ ∞ κ) (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Set.Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (s : Finset Lattice) (h : ℝ), 0 < h →
      ∀ (c : Fin 3 → Fin (p + 1)) (z : Point),
        ‖fderiv ℝ (coloredBlockMask p s (convolvedBoxWindow κ p) h c) z‖ ≤ L / h := by
  classical
  have hw := convolvedBoxWindow_bounds (hs.continuous.integrable_of_hasCompactSupport hc)
    hm hn hk hp
  have hd := contDiff_convolvedBoxWindow hc hs p
  obtain ⟨L, hL, hb⟩ := exists_blockWeight_fderiv_bound hw hd
  refine ⟨L, hL, ?_⟩
  intro s h hh c z
  unfold coloredBlockMask
  rw [fderiv_fun_sum (fun q _ ↦ (contDiff_blockWeight hd h q).differentiable
    (by simp) z)]
  by_cases hex : ∃ q ∈ s.filter (fun q ↦ color p q = c),
      blockWeight (convolvedBoxWindow κ p) h q z ≠ 0
  · obtain ⟨q, hq, hq0⟩ := hex
    rw [Finset.sum_eq_single_of_mem q hq]
    · exact hb h hh q z
    · intro r hr hrq
      apply fderiv_blockWeight_eq_zero hw.nonneg
      by_contra hr0
      exact hrq (blockWeight_same_color_unique hw
        ((Finset.mem_filter.mp hr).2.trans (Finset.mem_filter.mp hq).2.symm) hr0 hq0)
  · have hz : ∑ q ∈ s.filter (fun q ↦ color p q = c),
        fderiv ℝ (blockWeight (convolvedBoxWindow κ p) h q) z = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      apply fderiv_blockWeight_eq_zero hw.nonneg
      by_contra hq0
      exact hex ⟨q, hq, hq0⟩
    rw [hz, norm_zero]
    exact div_nonneg hL hh.le

/-- The first derivative estimate for the literal block cutoff used by the
sampling normal. The constant is fixed before `B`, `h`, `c` and `z`, and no
upper bound on `h` is needed (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem exists_truncated_coloredBlockMask_fderiv_bound {κ : ℝ → ℝ} (hc : HasCompactSupport κ)
    (hs : ContDiff ℝ ∞ κ) (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Set.Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (B h : ℝ), 0 < h →
      ∀ (c : Fin 3 → Fin (p + 1)) (z : Point),
        ‖fderiv ℝ (coloredBlockMask p (integerCube (blockCutoff p B h))
          (convolvedBoxWindow κ p) h c) z‖ ≤ L / h := by
  obtain ⟨L, hL, hb⟩ := exists_coloredBlockMask_fderiv_bound hc hs hm hn hk hp
  exact ⟨L, hL, fun B h hh c z ↦ hb _ h hh c z⟩

/-- Pulling the literal truncated mask back along `u ↦ z₀ + Z u` costs only
`‖Z‖`. The constant is uniform in the spectator offset `z₀`, dimension, finite
cutoff and mesh. For fixed `Z`, `L * ‖Z‖` is the derivative budget in
`exists_colored_prefix_homotopy_bound`
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem exists_coloredBlockMask_pullback_fderiv_bound {κ : ℝ → ℝ} (hc : HasCompactSupport κ)
    (hs : ContDiff ℝ ∞ κ) (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Set.Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (n : ℕ) (Z : EuclideanSpace ℝ (Fin n) →L[ℝ] Point)
      (B h : ℝ), 0 < h → ∀ (c : Fin 3 → Fin (p + 1)) (z₀ : Point)
      (u : EuclideanSpace ℝ (Fin n)),
        ‖fderiv ℝ (fun v ↦ coloredBlockMask p (integerCube (blockCutoff p B h))
          (convolvedBoxWindow κ p) h c (z₀ + Z v)) u‖ ≤ L * ‖Z‖ / h := by
  obtain ⟨L, hL, hb⟩ := exists_truncated_coloredBlockMask_fderiv_bound hc hs hm hn hk hp
  refine ⟨L, hL, ?_⟩
  intro n Z B h hh c z₀ u
  let m := coloredBlockMask p (integerCube (blockCutoff p B h))
    (convolvedBoxWindow κ p) h c
  have hm' : Differentiable ℝ m :=
    (contDiff_coloredBlockMask hc hs p _ h c).differentiable (by simp)
  have ha : HasFDerivAt (fun v ↦ z₀ + Z v) Z u := Z.hasFDerivAt.const_add z₀
  change ‖fderiv ℝ (m ∘ (fun v ↦ z₀ + Z v)) u‖ ≤ _
  rw [fderiv_comp u (hm' _) ha.differentiableAt, ha.fderiv]
  calc
    _ ≤ ‖fderiv ℝ m (z₀ + Z u)‖ * ‖Z‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (L / h) * ‖Z‖ := mul_le_mul_of_nonneg_right (hb B h hh c _) (norm_nonneg _)
    _ = L * ‖Z‖ / h := by ring

end JanetCartan.Sampling.ColoredNormalComparison
