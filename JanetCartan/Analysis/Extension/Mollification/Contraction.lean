module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Contraction of a closed ball

The contraction step in the density paragraph of
`app:ch_regular_base:lem:ball-extension` in Appendix B of `paper.tex`.
We prove Cᵐ regularity on the expanded open ball and uniform convergence of
all classical derivatives to the intrinsic closed-ball derivatives.
-/

open Set Metric Filter Function
open scoped Topology ContDiff

@[expose] public noncomputable section

namespace JanetCartan.Mollification

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: the affine contraction towards the
center of the ball. -/
def contract (c : E) (a : ℝ) (x : E) : E := c + a • (x - c)

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: the exact radial scaling under
contraction. -/
theorem dist_contract_center (c x : E) (a : ℝ) :
    dist (contract c a x) c = |a| * dist x c := by
  simp [contract, dist_eq_norm, norm_smul, Real.norm_eq_abs]

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: contraction preserves the closed ball. -/
theorem contract_mem_closedBall {c x : E} {R a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ closedBall c R) : contract c a x ∈ closedBall c R := by
  rw [mem_closedBall, dist_contract_center, abs_of_nonneg ha.1]
  exact (mul_le_of_le_one_left dist_nonneg ha.2).trans (mem_closedBall.mp hx)

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: strict contraction moves the closed ball
into its interior. -/
theorem contract_mem_ball {c x : E} {R a : ℝ} (hR : 0 < R) (ha : 0 ≤ a)
    (ha1 : a < 1) (hx : x ∈ closedBall c R) : contract c a x ∈ ball c R := by
  rw [mem_ball, dist_contract_center, abs_of_nonneg ha]
  exact (mul_le_mul_of_nonneg_left (mem_closedBall.mp hx) ha).trans_lt
    (mul_lt_of_lt_one_left hR ha1)

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: the contracted input is defined on a
larger open ball. -/
theorem contract_mem_ball_div {c x : E} {R a : ℝ} (ha : 0 < a)
    (hx : x ∈ ball c (R / a)) : contract c a x ∈ ball c R := by
  rw [mem_ball, dist_contract_center, abs_of_pos ha]
  simpa [mul_comm] using (lt_div_iff₀ ha).mp (mem_ball.mp hx)

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: contraction is smooth at every order. -/
theorem contDiff_contract (c : E) (a : ℝ) (n : ℕ∞ω) : ContDiff ℝ n (contract c a) :=
  contDiff_const.add ((contDiff_id.sub contDiff_const).const_smul a)

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: Cᵐ input on the closed ball becomes Cᵐ
on a larger open ball after contraction. -/
theorem contDiffOn_comp_contract {c : E} {R a : ℝ} (ha : 0 < a)
    {f : E → F} {n : ℕ∞ω} (hf : ContDiffOn ℝ n f (closedBall c R)) :
    ContDiffOn ℝ n (f ∘ contract c a) (ball c (R / a)) := by
  exact hf.comp (contDiff_contract c a n).contDiffOn
    (fun _ hx ↦ ball_subset_closedBall (contract_mem_ball_div ha hx))

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: the nth derivative under contraction has
the exact factor aⁿ. -/
theorem iteratedFDeriv_comp_contract (c : E) {a : ℝ} (ha : a ≠ 0)
    (f : E → F) (n : ℕ) (x : E) :
    iteratedFDeriv ℝ n (f ∘ contract c a) x =
      a ^ n • iteratedFDeriv ℝ n f (contract c a x) := by
  let L : E ≃L[ℝ] E :=
    { LinearEquiv.smulOfNeZero ℝ E a ha with
      continuous_toFun := continuous_const.smul continuous_id
      continuous_invFun := continuous_const.smul continuous_id }
  have hL (g : E → F) (y : E) :
      iteratedFDeriv ℝ n (g ∘ L) y =
        a ^ n • iteratedFDeriv ℝ n g (a • y) := by
    have h := L.iteratedFDerivWithin_comp_right g uniqueDiffOn_univ (mem_univ (L y)) n
    simp only [preimage_univ, iteratedFDerivWithin_univ] at h
    rw [h]
    ext v
    change (iteratedFDeriv ℝ n g (a • y)) (fun i ↦ a • v i) =
      a ^ n • (iteratedFDeriv ℝ n g (a • y)) v
    simp [ContinuousMultilinearMap.map_smul_univ]
  change iteratedFDeriv ℝ n (fun z ↦ (fun y ↦ f (c + a • y)) (z - c)) x = _
  rw [iteratedFDeriv_comp_sub (f := fun y ↦ f (c + a • y))]
  change iteratedFDeriv ℝ n ((fun y ↦ f (c + y)) ∘ L) (x - c) = _
  rw [hL, iteratedFDeriv_comp_add_left]
  rfl


/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: derivatives within a positive-radius
closed ball are unique. -/
theorem uniqueDiffOn_closedBall_of_pos (c : E) {R : ℝ} (hR : 0 < R) :
    UniqueDiffOn ℝ (closedBall c R) :=
  uniqueDiffOn_convex (convex_closedBall c R)
    ⟨c, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds c hR)⟩

variable [FiniteDimensional ℝ E]

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: continuous fields converge uniformly
under contraction, including the derivative scaling factor. -/
theorem tendstoUniformlyOn_scaled_comp_contract {c : E} {R : ℝ} (n : ℕ)
    {f : E → F} (hf : ContinuousOn f (closedBall c R)) :
    TendstoUniformlyOn (fun a x ↦ a ^ n • f (contract c a x)) f
      (𝓝[Icc (0 : ℝ) 1] 1) (closedBall c R) := by
  let H : ℝ × E → E := fun p ↦ contract c p.1 p.2
  have hH : Continuous H := continuous_const.add
    (continuous_fst.smul (continuous_snd.sub continuous_const))
  have hcomp : ContinuousOn (fun p : ℝ × E ↦ f (H p))
      (Icc (0 : ℝ) 1 ×ˢ closedBall c R) :=
    hf.comp hH.continuousOn (fun _ hp ↦ contract_mem_closedBall hp.1 hp.2)
  have hcont : ContinuousOn (fun p : ℝ × E ↦ p.1 ^ n • f (H p))
      (Icc (0 : ℝ) 1 ×ˢ closedBall c R) :=
    (continuous_fst.pow n).continuousOn.smul hcomp
  have hu := ((isCompact_Icc.prod (isCompact_closedBall c R)).uniformContinuousOn_of_continuous
    hcont).tendstoUniformlyOn (F := fun a x ↦ a ^ n • f (contract c a x))
      (show (1 : ℝ) ∈ Icc 0 1 by simp)
  simpa [H, contract] using hu


/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: every contracted classical derivative
converges uniformly to the derivative within the closed ball. No extension beyond the boundary
is assumed. -/
theorem tendstoUniformlyOn_iteratedFDeriv_comp_contract {c : E} {R : ℝ} (hR : 0 < R)
    {f : E → F} (n : ℕ) (hf : ContDiffOn ℝ n f (closedBall c R)) :
    TendstoUniformlyOn (fun a ↦ iteratedFDeriv ℝ n (f ∘ contract c a))
      (iteratedFDerivWithin ℝ n f (closedBall c R))
      (𝓝[Ioo (0 : ℝ) 1] 1) (closedBall c R) := by
  have hu := tendstoUniformlyOn_scaled_comp_contract n
    (hf.continuousOn_iteratedFDerivWithin le_rfl (uniqueDiffOn_closedBall_of_pos c hR))
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  filter_upwards [(hu ε hε).filter_mono
    (nhdsWithin_mono (1 : ℝ) Ioo_subset_Icc_self), self_mem_nhdsWithin] with a ha ha'
  intro x hx
  rw [iteratedFDeriv_comp_contract c ha'.1.ne']
  have hax := contract_mem_ball hR ha'.1.le ha'.2 hx
  have heq : iteratedFDerivWithin ℝ n f (closedBall c R) (contract c a x) =
      iteratedFDeriv ℝ n f (contract c a x) := by
    exact iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_closedBall_of_pos c hR)
      (hf.contDiffAt (mem_of_superset (isOpen_ball.mem_nhds hax) ball_subset_closedBall))
      (ball_subset_closedBall hax)
  simpa only [heq] using ha x hx

end JanetCartan.Mollification
