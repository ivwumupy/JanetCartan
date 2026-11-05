module

public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.Definitions
public import JanetCartan.Analysis.Extension.Ball.ContinuousBounds
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Finiteness of the ball extension's derivative energies

For `app:ch_regular_base:eq:ball-extension-sobolev`, all input derivatives are
square integrable on the open ball, and all derivatives of the actual fixed
Seeley extension are square integrable on the whole space. These conclusions
follow from closed-ball smoothness alone. They do not supply the quantitative
Sobolev inequality, which additionally needs the collar change of variables.

All results include dimension zero and dimension one.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Filter
open scoped ContDiff Topology

namespace JanetCartan.BallExtension.Parameters

variable {n : ℕ} (p : Parameters (EuclideanSpace ℝ (Fin n)))

/-- The interior jets do not depend on whether derivatives are taken within the
open or closed ball (`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem iteratedFDerivWithin_closedBall_eq_on_ball
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (j : ℕ) :
    EqOn (iteratedFDerivWithin ℝ j f (closedBall p.center p.radius))
      (iteratedFDerivWithin ℝ j f (ball p.center p.radius)) (ball p.center p.radius) := by
  intro x hx
  apply iteratedFDerivWithin_congr_set _ j
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact propext ⟨fun _ ↦ hy, fun _ ↦ ball_subset_closedBall hy⟩

/-- The Cartesian input jets agree on the open ball, independently of which ball
is used for within differentiation (`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem cartesianDerivativeWithin_closedBall_eq_on_ball
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (α : Fin n → ℕ) :
    EqOn (cartesianDerivativeWithin α f (closedBall p.center p.radius))
      (cartesianDerivativeWithin α f (ball p.center p.radius)) (ball p.center p.radius) := by
  intro x hx
  unfold cartesianDerivativeWithin
  rw [p.iteratedFDerivWithin_closedBall_eq_on_ball f _ hx]

/-- Squared norms of all intrinsic input jets are integrable on the closed ball,
as needed in `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem integrableOn_sq_norm_iteratedFDerivWithin_closedBall
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (j : ℕ) :
    IntegrableOn (fun x ↦ ‖iteratedFDerivWithin ℝ j f (closedBall p.center p.radius) x‖ ^ 2)
      (closedBall p.center p.radius) :=
  ((hf.continuousOn_iteratedFDerivWithin (by simp) p.uniqueDiffOn_closedBall).norm.pow 2).integrableOn_compact
    (isCompact_closedBall _ _)

/-- Squared norms of input Fréchet jets are integrable on the open ball in
`app:ch_regular_base:eq:extension-collar-l2`, without an ambient smoothness premise. -/
theorem integrableOn_sq_norm_iteratedFDerivWithin_ball
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (j : ℕ) :
    IntegrableOn (fun x ↦ ‖iteratedFDerivWithin ℝ j f (ball p.center p.radius) x‖ ^ 2)
      (ball p.center p.radius) := by
  apply ((p.integrableOn_sq_norm_iteratedFDerivWithin_closedBall hf j).mono_set
    ball_subset_closedBall).congr_fun _ measurableSet_ball
  intro x hx
  dsimp only
  rw [p.iteratedFDerivWithin_closedBall_eq_on_ball f j hx]

/-- All squared Cartesian derivatives in the manuscript's input norm are
integrable (`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem integrableOn_sq_cartesianDerivativeWithin_ball
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (α : Fin n → ℕ) :
    IntegrableOn (fun x ↦ cartesianDerivativeWithin α f (ball p.center p.radius) x ^ 2)
      (ball p.center p.radius) := by
  have h := ((continuousOn_cartesianDerivativeWithin p.uniqueDiffOn_closedBall hf α).pow 2).integrableOn_compact
    (μ := volume) (isCompact_closedBall _ _)
  apply (h.mono_set ball_subset_closedBall).congr_fun _ measurableSet_ball
  intro x hx
  simp only [Pi.pow_apply]
  rw [p.cartesianDerivativeWithin_closedBall_eq_on_ball f α hx]

/-- Every derivative of the one fixed Seeley extension belongs to `L²`, as
required by `app:ch_regular_base:eq:ball-extension-sobolev`. -/
theorem memLp_iteratedFDeriv_extend
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (j : ℕ) :
    MemLp (iteratedFDeriv ℝ j (p.extend Seeley.coeff f)) 2 volume :=
  ((p.contDiff_extend Seeley.coeff Seeley.summable_abs_coeff_moment
    Seeley.infinite_moment hf).continuous_iteratedFDeriv (by simp)).memLp_of_hasCompactSupport
    ((p.hasCompactSupport_extend Seeley.coeff f).iteratedFDeriv j)

/-- All squared Fréchet jet norms of the extension are integrable; this justifies
the auxiliary whole-space energy in `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem integrable_sq_norm_iteratedFDeriv_extend
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (j : ℕ) :
    Integrable (fun x ↦ ‖iteratedFDeriv ℝ j (p.extend Seeley.coeff f) x‖ ^ 2) :=
  (p.memLp_iteratedFDeriv_extend hf j).integrable_norm_pow (by decide)

/-- Each Cartesian derivative of the fixed extension belongs to `L²`, as
asserted in `app:ch_regular_base:eq:ball-extension-sobolev`. -/
theorem memLp_cartesianDerivativeWithin_extend
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (α : Fin n → ℕ) :
    MemLp (cartesianDerivativeWithin α (p.extend Seeley.coeff f) univ) 2 volume :=
  (continuous_cartesianDerivativeWithin_univ
    (p.contDiff_extend Seeley.coeff Seeley.summable_abs_coeff_moment
      Seeley.infinite_moment hf) α).memLp_of_hasCompactSupport
    (hasCompactSupport_cartesianDerivativeWithin_univ
      (p.hasCompactSupport_extend Seeley.coeff f) α)

/-- Every integral in the whole-space Cartesian energy is finite for the actual
extension (`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem integrable_sq_cartesianDerivativeWithin_extend
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (α : Fin n → ℕ) :
    Integrable (fun x ↦ cartesianDerivativeWithin α (p.extend Seeley.coeff f) univ x ^ 2) :=
  (memLp_two_iff_integrable_sq
    (p.memLp_cartesianDerivativeWithin_extend hf α).aestronglyMeasurable).mp
    (p.memLp_cartesianDerivativeWithin_extend hf α)

/-- The extension's derivatives restrict to the input's intrinsic derivatives
on the open ball (`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem iteratedFDeriv_extend_eq_on_ball (a : ℕ → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (j : ℕ) :
    EqOn (iteratedFDeriv ℝ j (p.extend a f))
      (iteratedFDerivWithin ℝ j f (ball p.center p.radius)) (ball p.center p.radius) := by
  intro x hx
  rw [← iteratedFDerivWithin_of_isOpen j isOpen_ball hx]
  exact iteratedFDerivWithin_congr ((p.extend_eq_on_closedBall a f).mono
    ball_subset_closedBall) hx j

/-- Cartesian derivatives of the fixed formula restrict to the input derivatives
on the open ball (`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem cartesianDerivativeWithin_extend_eq_on_ball (a : ℕ → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (α : Fin n → ℕ) :
    EqOn (cartesianDerivativeWithin α (p.extend a f) univ)
      (cartesianDerivativeWithin α f (ball p.center p.radius)) (ball p.center p.radius) := by
  intro x hx
  unfold cartesianDerivativeWithin
  rw [iteratedFDerivWithin_univ, p.iteratedFDeriv_extend_eq_on_ball a f _ hx]

/-- Restriction decreases the actual Cartesian Sobolev energy, the easy direction
of the norm comparison in `app:ch_regular_base:lem:ball-extension`. -/
theorem cartesianSobolevEnergy_ball_le_extend
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (m : ℕ) :
    cartesianSobolevEnergy (ball p.center p.radius) m f ≤
      cartesianSobolevEnergy univ m (p.extend Seeley.coeff f) := by
  apply Finset.sum_le_sum
  intro α _
  have heq : (∫ x in ball p.center p.radius,
      cartesianDerivativeWithin (fun i ↦ α (some i)) f (ball p.center p.radius) x ^ 2) =
      ∫ x in ball p.center p.radius,
        cartesianDerivativeWithin (fun i ↦ α (some i)) (p.extend Seeley.coeff f) univ x ^ 2 := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only
    rw [p.cartesianDerivativeWithin_extend_eq_on_ball Seeley.coeff f _ hx]
  rw [heq, setIntegral_univ]
  exact setIntegral_le_integral (p.integrable_sq_cartesianDerivativeWithin_extend hf _)
    (ae_of_all _ (fun _ ↦ sq_nonneg _))

/-- Restriction decreases the manuscript's derivative Sobolev norm. The reverse
inequality is the substantive bound in `app:ch_regular_base:eq:ball-extension-sobolev`. -/
theorem cartesianSobolevNorm_ball_le_extend
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (m : ℕ) :
    cartesianSobolevNorm (ball p.center p.radius) m f ≤
      cartesianSobolevNorm univ m (p.extend Seeley.coeff f) :=
  Real.sqrt_le_sqrt (p.cartesianSobolevEnergy_ball_le_extend hf m)

end JanetCartan.BallExtension.Parameters
