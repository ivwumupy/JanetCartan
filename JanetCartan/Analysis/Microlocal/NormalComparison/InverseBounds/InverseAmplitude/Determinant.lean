module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.UniformJets
public import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# The reciprocal absolute Jacobian

The determinant gap and a controlled compact set of differentials provide
the scalar estimates for `app:ch_osc:prop:osc-normal`, Step 1.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.NormalComparison
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- Smoothness of the finite dimensional determinant, used for the absolute
Jacobian in `app:ch_osc:prop:osc-normal`, Step 1. -/
theorem contDiff_normalJacobianDet : ContDiff ℝ ∞ (fun A : Euclidean n →L[ℝ] Euclidean n ↦ A.det) := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let L := ((LinearMap.toMatrix b b).toLinearMap.comp
    (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap
  have he (A : Euclidean n →L[ℝ] Euclidean n) : A.det = (L A).det :=
    (LinearMap.det_toMatrix b A.toLinearMap).symm
  simp_rw [he, Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact contDiff_pi.mp (contDiff_pi.mp L.contDiff (σ i)) i

/-- Reciprocal absolute determinants are smooth wherever the determinant is
nonzero (`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem contDiffAt_reciprocalAbsNormalJacobian
    {A : Euclidean n →L[ℝ] Euclidean n} (hA : A.det ≠ 0) :
    ContDiffAt ℝ ∞ (fun B : Euclidean n →L[ℝ] Euclidean n ↦ |B.det|⁻¹) A :=
  (contDiff_normalJacobianDet.contDiffAt.abs hA).inv (abs_ne_zero.mpr hA)

/-- The gap gives the sharp zeroth reciprocal absolute-Jacobian estimate
used by the inverse amplitude (`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem UniformNormalData.reciprocalAbsJacobian_le (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) {x y u : Euclidean n}
    (hx : x ∈ G.X) (hy : y ∈ G.X) (hu : u ∈ G.D) :
    |(fderiv ℝ (averagedGradient (F.phase ε) x y) u).det|⁻¹ ≤ G.gap⁻¹ :=
  inv_anti₀ G.gap_pos (F.jacobian_gap ε hε x hx y hy u hu)

/-- Ambient smoothness of the actual reciprocal absolute input Jacobian,
including admissible endpoints (`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem UniformNormalData.reciprocalAbsJacobian_contDiffAt (F : UniformNormalData G C)
    {q : ℝ × (Euclidean n × (Euclidean n × Euclidean n))}
    (hq : q ∈ Icc 0 G.ε₀ ×ˢ (G.X ×ˢ (G.X ×ˢ G.D))) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) ↦
      |(fderiv ℝ (averagedGradient (F.phase p.1) p.2.1 p.2.2.1) p.2.2.2).det|⁻¹) q := by
  have hdet := abs_pos.mp (G.gap_pos.trans_le
    (F.jacobian_gap q.1 hq.1 q.2.1 hq.2.1 q.2.2.1 hq.2.2.1 q.2.2.2 hq.2.2.2))
  exact (contDiffAt_reciprocalAbsNormalJacobian hdet).comp q
    (f := fun p : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) ↦
      fderiv ℝ (averagedGradient (F.phase p.1) p.2.1 p.2.2.1) p.2.2.2)
    (F.inputJacobian_contDiffOn.contDiffAt
      ((F.isOpen_parameterDomain.prod (G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D))).mem_nhds
        ⟨F.parameter_subset hq.1, hq.2⟩))

/-- Finite jets of the reciprocal absolute determinant are uniformly bounded
on the compact set of differentials with a fixed norm bound and gap. This
set is fixed before any phase family (`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem exists_reciprocalAbsNormalJacobian_jet_bound (N : ℕ) (B : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ K > 0, ∀ A : Euclidean n →L[ℝ] Euclidean n, ‖A‖ ≤ B → δ ≤ |A.det| →
      ∀ k ≤ N, ‖iteratedFDeriv ℝ k
        (fun L : Euclidean n →L[ℝ] Euclidean n ↦ |L.det|⁻¹) A‖ ≤ K := by
  let S : Set (Euclidean n →L[ℝ] Euclidean n) := {A | ‖A‖ ≤ B ∧ δ ≤ |A.det|}
  have hS : IsCompact S := (isCompact_closedBall (0 : Euclidean n →L[ℝ] Euclidean n) B).of_isClosed_subset
    (isClosed_le continuous_norm continuous_const |>.inter
      (isClosed_le continuous_const ContinuousLinearMap.continuous_det.abs))
    (fun A hA ↦ by simpa only [mem_closedBall, dist_zero_right] using hA.1)
  have hb (k : ℕ) : ∃ K : ℝ, ∀ A ∈ S, ‖iteratedFDeriv ℝ k
      (fun L : Euclidean n →L[ℝ] Euclidean n ↦ |L.det|⁻¹) A‖ ≤ K := by
    apply hS.exists_bound_of_continuousOn
    intro A hA
    exact ((contDiffAt_reciprocalAbsNormalJacobian (abs_pos.mp (hδ.trans_le hA.2))).continuousAt_iteratedFDeriv
      (by simp)).continuousWithinAt
  choose K hK using hb
  let L := 1 + ∑ k ∈ Finset.range (N + 1), |K k|
  have hsum : 0 ≤ ∑ k ∈ Finset.range (N + 1), |K k| :=
    Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  refine ⟨L, by dsimp [L]; linarith, ?_⟩
  intro A hA hdet k hk
  apply (hK k A ⟨hA, hdet⟩).trans
  have h := Finset.single_le_sum (fun i _ ↦ abs_nonneg (K i))
    (Finset.mem_range.mpr (by omega : k < N + 1))
  dsimp [L]
  linarith [le_abs_self (K k)]

end JanetCartan.NormalComparison
