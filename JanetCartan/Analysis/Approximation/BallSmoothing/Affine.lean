module

public import JanetCartan.Analysis.Approximation.BallSmoothing.Linearity
public import JanetCartan.Analysis.Approximation.BallSmoothing.UnitBounds
public import JanetCartan.Analysis.Extension.Mollification.Contraction
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Affine transport to the original ball

The affine normalization in the proof of
`app:ch_regular_base:lem:ball-extension` changes only fixed constants. This
file proves the exact coordinate identities, including every derivative
order, for the SAME inward smoother. The original closed-ball `C⁰` norm is
preserved exactly, and higher source norms incur only fixed radius factors.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Metric
open scoped ContDiff

namespace JanetCartan.BallSmoothing

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The fixed map from the unit ball to the original ball
(`app:ch_regular_base:lem:ball-extension`). -/
def ballRescale (c : E) (a : ℝ) (z : E) : E := c + a • z

/-- The fixed map from the original ball to the unit ball
(`app:ch_regular_base:lem:ball-extension`). -/
def ballNormalize (c : E) (a : ℝ) (x : E) : E := a⁻¹ • (x - c)

/-- The original positive-radius ball is exactly normalized
(`app:ch_regular_base:lem:ball-extension`). -/
theorem ballRescale_ballNormalize (c : E) {a : ℝ} (ha : a ≠ 0) (x : E) :
    ballRescale c a (ballNormalize c a x) = x := by
  simp [ballRescale, ballNormalize, smul_smul, ha]

/-- The original positive-radius ball is exactly normalized
(`app:ch_regular_base:lem:ball-extension`). -/
theorem ballNormalize_ballRescale (c : E) {a : ℝ} (ha : a ≠ 0) (z : E) :
    ballNormalize c a (ballRescale c a z) = z := by
  simp [ballRescale, ballNormalize, smul_smul, ha]

/-- The fixed affine map sends the whole closed unit ball into the
original closed ball (`app:ch_regular_base:lem:ball-extension`). -/
theorem ballRescale_mem_closedBall (c : E) {a : ℝ} (ha : 0 ≤ a)
    {z : E} (hz : z ∈ closedBall (0 : E) 1) : ballRescale c a z ∈ closedBall c a := by
  rw [mem_closedBall, ballRescale, dist_eq_norm, add_sub_cancel_left,
    norm_smul, Real.norm_of_nonneg ha]
  exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) ha).trans_eq (mul_one a)

/-- The inverse fixed affine map sends the whole original closed ball
into the unit ball (`app:ch_regular_base:lem:ball-extension`). -/
theorem ballNormalize_mem_closedBall (c : E) {a : ℝ} (ha : 0 < a)
    {x : E} (hx : x ∈ closedBall c a) : ballNormalize c a x ∈ closedBall (0 : E) 1 := by
  rw [mem_closedBall_zero_iff, ballNormalize, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
  have hd : ‖x - c‖ ≤ a := by simpa only [mem_closedBall, dist_eq_norm] using hx
  exact (mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr ha.le)).trans_eq (inv_mul_cancel₀ ha.ne')

/-- Exact derivative factors for the original affine input pullback.
This uses the existing affine derivative identity, with no global input
regularity assumption (`app:ch_regular_base:lem:ball-extension`). -/
theorem iteratedFDeriv_ballRescale (c : E) {a : ℝ} (ha : a ≠ 0)
    (f : E → F) (r : ℕ) (z : E) :
    iteratedFDeriv ℝ r (fun x ↦ f (ballRescale c a x)) z =
      a ^ r • iteratedFDeriv ℝ r f (ballRescale c a z) := by
  simpa only [Function.comp_def, Mollification.contract, sub_zero, zero_add,
    iteratedFDeriv_comp_add_left, ballRescale] using
    Mollification.iteratedFDeriv_comp_contract (0 : E) ha (fun y ↦ f (c + y)) r z

/-- Exact output derivative factors under the inverse affine map
(`app:ch_regular_base:lem:ball-extension`). -/
theorem iteratedFDeriv_ballNormalize (c : E) {a : ℝ} (ha : a ≠ 0)
    (g : E → F) (r : ℕ) (x : E) :
    iteratedFDeriv ℝ r (fun y ↦ g (ballNormalize c a y)) x =
      (a⁻¹) ^ r • iteratedFDeriv ℝ r g (ballNormalize c a x) := by
  change iteratedFDeriv ℝ r (fun y ↦ (fun z ↦ g (a⁻¹ • z)) (y - c)) x = _
  rw [iteratedFDeriv_comp_sub (f := fun z : E ↦ g (a⁻¹ • z)) r c x]
  simpa only [Function.comp_def, Mollification.contract, sub_zero, zero_add, ballNormalize] using
    Mollification.iteratedFDeriv_comp_contract (0 : E) (inv_ne_zero ha) g r (x - c)

/-- The original input `C⁰` norm is preserved exactly by normalization;
no exterior values or derivatives enter
(`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem cNorm_zero_ballRescale (c : E) {a : ℝ} (ha : 0 < a) (f : E → F) :
    cNorm (closedBall (0 : E) 1) 0 (fun z ↦ f (ballRescale c a z)) =
      cNorm (closedBall c a) 0 f := by
  rw [cNorm_order_zero, cNorm_order_zero]
  congr 1
  ext t
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨ballRescale c a z, ballRescale_mem_closedBall c ha.le hz, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨ballNormalize c a x, ballNormalize_mem_closedBall c ha hx,
      by
        change ‖f (ballRescale c a (ballNormalize c a x))‖ = ‖f x‖
        rw [ballRescale_ballNormalize c ha.ne' x]⟩

/-- Smooth-up-to-boundary data remain smooth up to the boundary after
the fixed affine pullback (`app:ch_regular_base:lem:ball-extension`). -/
theorem contDiffAt_ballRescale_closedBall (c : E) {a : ℝ} (ha : 0 ≤ a)
    {f : E → F} (hf : ∀ x ∈ closedBall c a, ContDiffAt ℝ ∞ f x) :
    ∀ z ∈ closedBall (0 : E) 1, ContDiffAt ℝ ∞ (fun y ↦ f (ballRescale c a y)) z := by
  intro z hz
  exact (hf _ (ballRescale_mem_closedBall c ha hz)).comp z
    (contDiff_const.add (contDiff_id.const_smul a)).contDiffAt

omit [NormedSpace ℝ F] in
/-- Continuity on the original closed ball suffices for continuity of
the pulled-back input (`app:ch_regular_base:lem:ball-extension`). -/
theorem continuousOn_ballRescale_closedBall (c : E) {a : ℝ} (ha : 0 ≤ a)
    {f : E → F} (hf : ContinuousOn f (closedBall c a)) :
    ContinuousOn (fun z ↦ f (ballRescale c a z)) (closedBall (0 : E) 1) := by
  have hr : Continuous (ballRescale c a) :=
    continuous_const.add (continuous_id.const_smul a)
  exact hf.comp hr.continuousOn (fun _ hz ↦ ballRescale_mem_closedBall c ha hz)

/-- Fixed radius factors control all original source derivatives through
order `r`, so affine normalization causes no loss of derivative order
(`app:ch_regular_base:eq:ball-extension-continuous`). -/
theorem cNorm_ballRescale_le (c : E) {a : ℝ} (ha : 0 < a)
    (r : ℕ) {f : E → F} (hf : ∀ x ∈ closedBall c a, ContDiffAt ℝ r f x) :
    cNorm (closedBall (0 : E) 1) r (fun z ↦ f (ballRescale c a z)) ≤
      (∑ j ∈ Finset.range (r + 1), a ^ j) * cNorm (closedBall c a) r f := by
  calc
    _ ≤ ∑ j ∈ Finset.range (r + 1), a ^ j * cNorm (closedBall c a) r f := by
      apply cNorm_le_sum_of_bounds
        (fun j _ ↦ mul_nonneg (pow_nonneg ha.le _) (cNorm_nonneg _ _ _))
      intro j hj z hz
      rw [iteratedFDeriv_ballRescale c ha.ne', norm_smul, norm_pow, Real.norm_of_nonneg ha.le]
      exact mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall c a) hf
          (ballRescale_mem_closedBall c ha.le hz) hj) (pow_nonneg ha.le _)
    _ = _ := by rw [Finset.sum_mul]

/-- The actual smoother on the original ball is the fixed affine
transport of the SAME finite-moment inward formula
(`app:ch_regular_base:lem:ball-extension`). -/
def affineSmoothing (c : E) (a R : ℝ) (m : ℕ) (f : E → F) (x : E) : F :=
  unitSmoothing R m (fun z ↦ f (ballRescale c a z)) (ballNormalize c a x)

/-- The actual transported output is globally smooth using only original
closed-ball continuity (`app:ch_regular_base:lem:ball-extension`). -/
theorem contDiff_affineSmoothing (c : E) {a : ℝ} (ha : 0 < a)
    {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : (2 : ℝ) * m ≤ R)
    {f : E → F} (hf : ContinuousOn f (closedBall c a)) :
    ContDiff ℝ ∞ (affineSmoothing c a R m f) :=
  (contDiff_unitSmoothing hm hR (continuousOn_ballRescale_closedBall c ha.le hf)).comp
    ((contDiff_id.sub contDiff_const).const_smul a⁻¹)

/-- Every output of the actual transported smoother lies in the stated
thin collar of the original ball
(`app:ch_regular_base:lem:ball-extension`). -/
theorem affineSmoothing_tsupport_subset (c : E) {a : ℝ} (ha : 0 < a)
    {R : ℝ} (hR : 1 ≤ R) (m : ℕ) (f : E → F) :
    tsupport (affineSmoothing c a R m f) ⊆ closedBall c (a + a / (4 * R)) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have hs : ballNormalize c a x ∈ tsupport (unitSmoothing R m (fun z ↦ f (ballRescale c a z))) :=
    subset_tsupport _ hx
  have hn := mem_ball_zero_iff.mp (unitSmoothing_tsupport_subset hR m _ hs)
  have he : ‖ballNormalize c a x‖ = a⁻¹ * ‖x - c‖ := by
    simp only [ballNormalize, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
  rw [he] at hn
  rw [mem_closedBall, dist_eq_norm]
  have hp := mul_le_mul_of_nonneg_left hn.le ha.le
  calc
    ‖x - c‖ = a * (a⁻¹ * ‖x - c‖) := by rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
    _ ≤ a * (1 + 1 / (4 * R)) := hp
    _ = _ := by ring

/-- All transported derivative constants remain fixed before the varying
scale and original input. Affine normalization changes only the constants,
and the original `C⁰` norm remains exact
(`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem exists_affineSmoothing_jet_bounds (c : E) {a : ℝ} (ha : 0 < a)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ B : ℕ → ℝ, (∀ r, 0 ≤ B r) ∧
      ∀ R : ℝ, (2 : ℝ) * m ≤ R → ∀ f : E → F,
        ContinuousOn f (closedBall c a) → ∀ r x,
          ‖iteratedFDeriv ℝ r (affineSmoothing c a R m f) x‖ ≤
            B r * R ^ r * cNorm (closedBall c a) 0 f := by
  obtain ⟨B, hB, hb⟩ := exists_unitSmoothing_jet_bounds (F := F) n m hm
  refine ⟨fun r ↦ (a⁻¹) ^ r * B r,
    fun r ↦ mul_nonneg (pow_nonneg (inv_nonneg.mpr ha.le) _) (hB r), ?_⟩
  intro R hR f hf r x
  change ‖iteratedFDeriv ℝ r (fun y ↦
    unitSmoothing R m (fun z ↦ f (ballRescale c a z)) (ballNormalize c a y)) x‖ ≤ _
  rw [iteratedFDeriv_ballNormalize c ha.ne', norm_smul, norm_pow,
    Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
  have hh := hb R hR (fun z ↦ f (ballRescale c a z))
    (continuousOn_ballRescale_closedBall c ha.le hf) r (ballNormalize c a x)
  rw [cNorm_zero_ballRescale c ha] at hh
  exact (mul_le_mul_of_nonneg_left hh (pow_nonneg (inv_nonneg.mpr ha.le) _)).trans_eq (by ring)

end JanetCartan.BallSmoothing
