module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.FiniteFamily

/-!
# Primitive componentwise frame comparison

Convert the paper's componentwise frame bounds to the joint frame seminorm
used by the literal determinant producer. Only the derivative-order factor
appears; no phase estimate or linear continuity modulus is assumed.
The consumer is `exists_finite_current_fullPhaseInputs`
(`app:ch_seed:setup:seed-current`, `app:ch_seed:prop:seed-actual-menu`, Step 1).
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase
open HamiltonPhase FrozenMenu FrozenPhaseReference

/-- Componentwise finite-jet bounds imply the joint frame bound with the
explicit factor `m+1` from the sum over derivative orders. This applies to the
literal Frobenius-valued frame (`app:ch_seed:setup:seed-current`). -/
theorem frame_cNorm_le_of_componentwise {n m : ℕ} {K : Set (Euclidean n)}
    (hK : IsCompact K) {f : Euclidean n → Fin n → MetricTensor n}
    (hf : ∀ x ∈ K, ContDiffAt ℝ m f x) {b : ℝ} (hb : 0 ≤ b)
    (hcomp : ∀ i, cNorm K m (fun x ↦ f x i) ≤ b) :
    cNorm K m f ≤ (m + 1) * b := by
  have hjets (k : ℕ) (hk : k ≤ m) (x : Euclidean n) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ k f x‖ ≤ b := by
    apply ContinuousMultilinearMap.opNorm_le_bound hb
    intro v
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hb (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _)))).mpr
    intro i
    let π : (Fin n → MetricTensor n) →L[ℝ] MetricTensor n := ContinuousLinearMap.proj i
    have he := π.iteratedFDeriv_comp_left (hf x hx) (by exact_mod_cast hk)
    have he' : (iteratedFDeriv ℝ k f x v) i =
        iteratedFDeriv ℝ k (fun x ↦ f x i) x v := by
      exact (congrArg (fun L ↦ L v) he).symm
    rw [he']
    have hd := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun y hy ↦ contDiffAt_pi.mp (hf y hy) i) hx hk
    exact ((iteratedFDeriv ℝ k (fun x ↦ f x i) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hd.trans (hcomp i)) (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _)))
  have hh := cNorm_le_sum_of_bounds (fun _ (_ : _ ≤ m) ↦ hb) hjets
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using hh

/-- Every positive joint tolerance is obtained from an explicit positive
componentwise frame tolerance. For `m=6` this supplies the paper's primitive
current neighborhood (`app:ch_seed:setup:seed-current`). -/
theorem frame_cNorm_lt_of_componentwise {n m : ℕ} {K : Set (Euclidean n)}
    (hK : IsCompact K) {f : Euclidean n → Fin n → MetricTensor n}
    (hf : ∀ x ∈ K, ContDiffAt ℝ m f x) {d : ℝ} (hd : 0 < d)
    (hcomp : ∀ i, cNorm K m (fun x ↦ f x i) < d / (2 * (m + 1))) :
    cNorm K m f < d := by
  have hm : (0 : ℝ) < m + 1 := by positivity
  have hb : 0 ≤ d / (2 * (m + 1)) := by positivity
  have hh := frame_cNorm_le_of_componentwise hK hf hb (fun i ↦ (hcomp i).le)
  apply hh.trans_lt
  have he : (m + 1 : ℝ) * (d / (2 * (m + 1))) = d / 2 := by field_simp
  rw [he]
  exact half_lt_self hd

/-- The physical-domain witness constructed with each reference places its
whole closed frame ball inside the smooth frame domain
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem frameBall_subset_of_stateDomain {n : ℕ} {ξ : Euclidean n}
    {a : AdaptedSection ξ} (N : LocalFrozenReference a) {U : Set (Euclidean n)}
    (hdomain : ∀ q ∈ N.stateDomain, q.1 ∈ U) :
    closedBall (0 : Euclidean n) N.stateRadius ⊆ U := by
  intro x hx
  apply hdomain (x, ξ)
  apply N.stateBall_subset
  rw [a.baseState_eq]
  simpa only [mem_closedBall, Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using hx

end JanetCartan.ActualCarriers.CurrentFullPhase
