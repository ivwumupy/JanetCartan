module

public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.LocalJets
public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.RadialPullback
public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.Integrability

/-! # Integrated summand estimates

The squared L² estimate in `app:ch_regular_base:eq:extension-collar-l2`,
with the radial Jacobian factor retained explicitly.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Filter
open scoped ContDiff Topology

namespace JanetCartan.BallExtension.Parameters

variable {n : ℕ} (p : Parameters (EuclideanSpace ℝ (Fin n)))

/-- Exterior jets can be computed within the closed exterior, as used in
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem iteratedFDerivWithin_summand_eq_exterior (a : ℕ → ℝ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (k m : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : p.radius < ‖x - p.center‖) :
    iteratedFDerivWithin ℝ m (fun y ↦ p.summand a f y k)
      {y | p.radius ≤ ‖y - p.center‖} x =
      iteratedFDeriv ℝ m (fun y ↦ p.summand a f y k) x := by
  exact iteratedFDerivWithin_eq_iteratedFDeriv p.uniqueDiffOn_closedExterior
    ((p.contDiffAt_summand_exterior a hf hx k).of_le (by simp)) hx.le

/-- Every summand derivative is square integrable on every sampling collar;
this supplies the integrability in `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem integrableOn_sq_norm_iteratedFDeriv_summand_radialCollar (a : ℕ → ℝ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (k m l : ℕ) :
    IntegrableOn (fun x ↦ ‖iteratedFDeriv ℝ m (fun y ↦ p.summand a f y k) x‖ ^ 2)
      (p.radialCollar l) := by
  have hc := (((p.contDiffOn_summand_closedExterior a hf k).continuousOn_iteratedFDerivWithin
    (m := m) (by simp) p.uniqueDiffOn_closedExterior).norm.pow 2).mono
    (show p.closedRadialCollar l ⊆ {y | p.radius ≤ ‖y - p.center‖} from fun _ hx ↦ hx.1)
  apply ((hc.integrableOn_compact (p.isCompact_closedRadialCollar l)).mono_set
    (p.radialCollar_subset_closedRadialCollar l)).congr_fun _ (p.isOpen_radialCollar l).measurableSet
  intro x hx
  dsimp only [Pi.pow_apply]
  rw [p.iteratedFDerivWithin_summand_eq_exterior a hf k m hx.1]

/-- A sampling collar is contained in the zeroth collar, as used to integrate
all terms on one fixed domain in `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem radialCollar_subset_radialCollar_zero (k : ℕ) :
    p.radialCollar k ⊆ p.radialCollar 0 := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hd := sub_pos.mpr hx.1
  simp only [pow_zero, one_mul]
  nlinarith [hx.2]

/-- The integral of the squared summand jet on the fixed collar equals its
integral on the active collar (`app:ch_regular_base:eq:extension-collar-l2`). -/
theorem integral_sq_norm_summand_radialCollar_zero (a : ℕ → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (k m : ℕ) :
    (∫ x in p.radialCollar 0, ‖iteratedFDeriv ℝ m (fun y ↦ p.summand a f y k) x‖ ^ 2) =
      ∫ x in p.radialCollar k, ‖iteratedFDeriv ℝ m (fun y ↦ p.summand a f y k) x‖ ^ 2 := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (p.isOpen_radialCollar 0).measurableSet (p.radialCollar_subset_radialCollar_zero k)
  intro x hx
  have hk : p.width ≤ (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) := by
    by_contra! h
    exact hx.2 ⟨hx.1.1, h⟩
  simp [p.iteratedFDeriv_summand_eq_zero_of_width_le a f k m hk]

/-- Squared L² collar estimate with the precise radial `2⁻ᵏ` factor in
`app:ch_regular_base:eq:extension-collar-l2`. The constant is independent of the
coefficients and input and applies also in dimensions zero and one. -/
theorem exists_integral_sq_norm_summand_bound (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ ∞ f (closedBall p.center p.radius) →
      ∀ (a : ℕ → ℝ) (k : ℕ),
      (∫ x in p.radialCollar 0,
        ‖iteratedFDeriv ℝ m (fun y ↦ p.summand a f y k) x‖ ^ 2) ≤
        B * |a k| ^ 2 * (2 : ℝ) ^ (2 * k * m) / (2 : ℝ) ^ k *
          frechetSobolevEnergy (ball p.center p.radius) m f := by
  obtain ⟨A, hA, hb⟩ := p.exists_summand_local_jet_sq_bound m
  refine ⟨A * (3 : ℝ) ^ (n - 1), by positivity, ?_⟩
  intro f hf a k
  let g := fun x ↦ ∑ j ∈ Finset.range (m + 1),
    ‖iteratedFDerivWithin ℝ j f (closedBall p.center p.radius) x‖ ^ 2
  have hg : ContinuousOn g (closedBall p.center p.radius) :=
    continuousOn_finsetSum _ fun j _ ↦
      (hf.continuousOn_iteratedFDerivWithin (by simp) p.uniqueDiffOn_closedBall).norm.pow 2
  have hg0 : ∀ x ∈ closedBall p.center p.radius, 0 ≤ g x :=
    fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hgi : (∫ x in ball p.center p.radius, g x) =
      frechetSobolevEnergy (ball p.center p.radius) m f := by
    rw [show g = (fun x ↦ ∑ j ∈ Finset.range (m + 1),
      ‖iteratedFDerivWithin ℝ j f (closedBall p.center p.radius) x‖ ^ 2) from rfl,
      integral_finsetSum _ (fun j _ ↦
        (p.integrableOn_sq_norm_iteratedFDerivWithin_closedBall hf j).mono_set ball_subset_closedBall)]
    apply Finset.sum_congr rfl
    intro j _
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only
    rw [p.iteratedFDerivWithin_closedBall_eq_on_ball f j hx]
  rw [p.integral_sq_norm_summand_radialCollar_zero a f k m]
  calc
    _ ≤ ∫ x in p.radialCollar k,
        (A * |a k| ^ 2 * (2 : ℝ) ^ (2 * k * m)) * g (p.radialPoint k x) := by
      apply setIntegral_mono_on
        (p.integrableOn_sq_norm_iteratedFDeriv_summand_radialCollar a hf k m k)
        ((p.integrableOn_comp_radialPoint_radialCollar hg k).const_mul _)
        (p.isOpen_radialCollar k).measurableSet
      intro x hx
      exact hb f hf a k x hx.1 hx.2
    _ = (A * |a k| ^ 2 * (2 : ℝ) ^ (2 * k * m)) *
        ∫ x in p.radialCollar k, g (p.radialPoint k x) := integral_const_mul _ _
    _ ≤ (A * |a k| ^ 2 * (2 : ℝ) ^ (2 * k * m)) *
        (((3 : ℝ) ^ (n - 1) / (2 : ℝ) ^ k) * ∫ x in ball p.center p.radius, g x) :=
      mul_le_mul_of_nonneg_left (p.integral_comp_radialPoint_le k hg hg0) (by positivity)
    _ = _ := by rw [hgi]; ring

end JanetCartan.BallExtension.Parameters
