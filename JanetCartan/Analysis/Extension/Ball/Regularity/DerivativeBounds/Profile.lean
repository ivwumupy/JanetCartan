module

public import JanetCartan.Analysis.Extension.Ball.Regularity.Jets
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# A fixed profile for the exterior collar

For `app:ch_regular_base:eq:extension-radial-formula`, separate the scaled normal
coordinate from the spatial variable. The profile is smooth within a fixed domain;
its derivatives on a compact collar are bounded independently of the summand index.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace JanetCartan.BallExtension.Parameters

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : JanetCartan.BallExtension.Parameters E)

/-- Fixed profile domain for `app:ch_regular_base:eq:extension-collar-l2`. -/
def collarProfileDomain : Set (ℝ × E) := Icc 0 p.width ×ˢ {p.center}ᶜ

/-- Fixed radial sampling map for `app:ch_regular_base:eq:extension-radial-formula`. -/
def collarSample (z : ℝ × E) : E :=
  p.center + ((p.radius - z.1) / ‖z.2 - p.center‖) • (z.2 - p.center)

/-- The cutoff radial profile in `app:ch_regular_base:eq:extension-radial-formula`. -/
def collarProfile (f : E → ℝ) (z : ℝ × E) : ℝ :=
  p.cutoff z.1 * f (p.collarSample z)

/-- The fixed domain has unique one-sided jets, including at normal coordinate zero,
as required by `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem uniqueDiffOn_collarProfileDomain : UniqueDiffOn ℝ p.collarProfileDomain :=
  (uniqueDiffOn_Icc p.width_pos).prod isOpen_compl_singleton.uniqueDiffOn

/-- The fixed profile samples only the original closed ball in
`app:ch_regular_base:eq:extension-radial-formula`. -/
theorem collarSample_mem_closedBall {z : ℝ × E} (hz : z ∈ p.collarProfileDomain) :
    p.collarSample z ∈ closedBall p.center p.radius := by
  have hne : z.2 - p.center ≠ 0 := sub_ne_zero.mpr hz.2
  have hnorm : 0 < ‖z.2 - p.center‖ := norm_pos_iff.mpr hne
  have hr : 0 ≤ p.radius - z.1 := by
    have := p.width_lt
    have := p.radius_pos
    linarith [hz.1.2]
  rw [mem_closedBall_iff_norm, collarSample, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr hnorm.le), div_mul_cancel₀ _ hnorm.ne']
  linarith [hz.1.1]

/-- Smoothness of the fixed sampling map in
`app:ch_regular_base:eq:extension-radial-formula`. -/
theorem contDiffOn_collarSample : ContDiffOn ℝ ∞ p.collarSample p.collarProfileDomain := by
  have hsub : ContDiffOn ℝ ∞ (fun z : ℝ × E ↦ z.2 - p.center) p.collarProfileDomain :=
    contDiffOn_snd.sub contDiffOn_const
  have hne : ∀ z ∈ p.collarProfileDomain, z.2 - p.center ≠ 0 :=
    fun _ hz ↦ sub_ne_zero.mpr hz.2
  exact contDiffOn_const.add (((contDiffOn_const.sub contDiffOn_fst).div
    (hsub.norm ℝ hne) (fun z hz ↦ norm_ne_zero_iff.mpr (hne z hz))).smul hsub)

/-- The collar profile is smooth using only the input's one-sided smoothness on
its closed ball; see `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem contDiffOn_collarProfile {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) :
    ContDiffOn ℝ ∞ (p.collarProfile f) p.collarProfileDomain :=
  (p.cutoff.contDiff.comp_contDiffOn contDiffOn_fst).mul
    (hf.comp p.contDiffOn_collarSample (fun _ hz ↦ p.collarSample_mem_closedBall hz))

/-- A fixed compact spatial collar for the estimates in
`app:ch_regular_base:eq:extension-collar-l2`. -/
def compactExteriorCollar : Set E :=
  {x | p.radius ≤ ‖x - p.center‖} ∩ closedBall p.center (p.radius + p.width)

/-- Compactness of the fixed collar used in
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem isCompact_compactExteriorCollar [FiniteDimensional ℝ E] :
    IsCompact p.compactExteriorCollar :=
  (isCompact_closedBall _ _).inter_left (isClosed_le continuous_const (by fun_prop))

omit [InnerProductSpace ℝ E] in
/-- The compact parameter collar stays in the smooth profile domain in
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem compactCollar_subset_profileDomain :
    Icc 0 p.width ×ˢ p.compactExteriorCollar ⊆ p.collarProfileDomain := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  have hr := p.radius_pos.trans_le hz.2.1
  exact sub_ne_zero.mp (norm_pos_iff.mp hr)

/-- Compactness bounds every fixed order of the profile derivatives, independently
of `k` and of the coefficient sequence, in `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem exists_collarProfile_derivative_bound [FiniteDimensional ℝ E] {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ m, ∀ z ∈ Icc 0 p.width ×ˢ p.compactExteriorCollar,
      ‖iteratedFDerivWithin ℝ i (p.collarProfile f) p.collarProfileDomain z‖ ≤ C := by
  have hb (i : ℕ) : ∃ C : ℝ, ∀ z ∈ Icc 0 p.width ×ˢ p.compactExteriorCollar,
      ‖iteratedFDerivWithin ℝ i (p.collarProfile f) p.collarProfileDomain z‖ ≤ C :=
    (isCompact_Icc.prod p.isCompact_compactExteriorCollar).exists_bound_of_continuousOn
      (((p.contDiffOn_collarProfile hf).continuousOn_iteratedFDerivWithin
        (by simp) p.uniqueDiffOn_collarProfileDomain).mono p.compactCollar_subset_profileDomain)
  choose C hC using hb
  refine ⟨∑ i ∈ Finset.range (m + 1), max 0 (C i),
    Finset.sum_nonneg (fun _ _ ↦ le_max_left _ _), ?_⟩
  intro i hi z hz
  exact (hC i z hz).trans ((le_max_right _ _).trans
    (Finset.single_le_sum (fun j _ ↦ le_max_left 0 (C j)) (Finset.mem_range.mpr (by omega))))

/-- The actual summand is a rescaled fixed profile, as in
`app:ch_regular_base:eq:extension-radial-formula`. -/
theorem summand_eq_collarProfile (a : ℕ → ℝ) (f : E → ℝ) (k : ℕ) (x : E) :
    p.summand a f x k = a k *
      p.collarProfile f ((2 : ℝ) ^ k * (‖x - p.center‖ - p.radius), x) := by
  simp only [summand, collarProfile, collarSample, radialPoint, smul_eq_mul]
  ring

end JanetCartan.BallExtension.Parameters
