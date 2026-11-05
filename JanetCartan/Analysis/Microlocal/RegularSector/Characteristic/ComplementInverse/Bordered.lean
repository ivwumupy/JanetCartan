module
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ComplementInverse.Regularity
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ComplementInverse.Homogeneity
public import Mathlib.Data.Matrix.Block
/-!
# The literal bordered characteristic pencil

The bordered matrix in `app:ch_regular_base:eq:complement-inverse` is
`[[H+eA, A k], [lᵀ A, 0]]`. Its nonsingularity follows from the same
rank-one completion used for the explicit complement inverse. Both matrices
have a common positive determinant gap on a compact normalized family.
-/

open scoped Matrix Matrix.Norms.Frobenius ContDiff
open Matrix Set
@[expose] public noncomputable section
namespace JanetCartan.RegularSector.Characteristic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The literal bordered matrix for the restricted pencil inverse
(`app:ch_regular_base:eq:complement-inverse`). -/
def borderedPencil (H A : Matrix ι ι ℝ) (k l : ι → ℝ) (e : ℝ) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
  fromBlocks (H + e • A) (fun i _ ↦ (A *ᵥ k) i) (fun _ j ↦ (l ᵥ* A) j) 0

/-- The completion construction proves nonsingularity of the literal bordered
matrix (`app:ch_regular_base:eq:complement-inverse`). -/
theorem borderedPencil_det_ne_zero {H A : Matrix ι ι ℝ} {k l : ι → ℝ} {e : ℝ}
    (hl : l ᵥ* H = 0) (hn : l ⬝ᵥ (A *ᵥ k) = 1)
    (hd : (pencilCompletion H A k l e).det ≠ 0) : (borderedPencil H A k l e).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  suffices hz : ∀ v, borderedPencil H A k l e *ᵥ v = 0 → v = 0 by
    intro v w hvw
    apply sub_eq_zero.mp
    apply hz
    simp [mulVec_sub, hvw]
  intro v hv
  let x : ι → ℝ := fun i ↦ v (.inl i)
  have hq : (l ᵥ* A) ⬝ᵥ x = 0 := by
    have h := congrFun hv (.inr ())
    simpa [borderedPencil, fromBlocks, mulVec, dotProduct, Fintype.sum_sum_type, x] using h
  have htop : (H + e • A) *ᵥ x + v (.inr ()) • (A *ᵥ k) = 0 := by
    funext i
    have h := congrFun hv (.inl i)
    simpa [borderedPencil, fromBlocks, mulVec, dotProduct, Fintype.sum_sum_type, x, mul_comm] using h
  have hvlast : v (.inr ()) = 0 := by
    have h := congrArg (fun w ↦ l ⬝ᵥ w) htop
    have hh : l ⬝ᵥ ((H + e • A) *ᵥ x) = 0 := by
      rw [dotProduct_mulVec, left_pencil hl, smul_dotProduct, hq, smul_zero]
    simpa [dotProduct_add, dotProduct_smul, hh, hn] using h
  have hx : x = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero hd
    simp only [hvlast, zero_smul, add_zero] at htop
    simpa [pencilCompletion, add_mulVec, smul_mulVec, vecMulVec_mulVec, hq] using htop
  funext i
  cases i with
  | inl j => exact congrFun hx j
  | inr j => cases j; exact hvlast

section Compact
variable {X : Type*} [TopologicalSpace X]
/-- The primitive kernel and normalization data on a compact family give one
interval and positive gaps for both the completion and bordered determinants
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_uniform_bordered_completion_gap (H A : X → Matrix ι ι ℝ) (k l : X → ι → ℝ)
    (hH : Continuous H) (hA : Continuous A) (hk : Continuous k) (hl : Continuous l)
    {K : Set X} (hK : IsCompact K)
    (hleft : ∀ x ∈ K, l x ᵥ* H x = 0)
    (hnorm : ∀ x ∈ K, l x ⬝ᵥ (A x *ᵥ k x) = 1)
    (hker : ∀ x ∈ K, ∀ v, H x *ᵥ v = 0 → ∃ c : ℝ, v = c • k x) :
    ∃ ε > 0, ∃ δ > 0, ∀ x ∈ K, ∀ e : ℝ, |e| ≤ ε →
      δ ≤ |(pencilCompletion (H x) (A x) (k x) (l x) e).det| ∧
      δ ≤ |(borderedPencil (H x) (A x) (k x) (l x) e).det| := by
  obtain ⟨ε, hε, δ, hδ, hgap⟩ := exists_uniform_completion_gap H A k l hH hA hk hl
    hK hleft hnorm hker
  have hB : Continuous (fun p : X × ℝ ↦ borderedPencil (H p.1) (A p.1) (k p.1) (l p.1) p.2) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change Continuous (fun p : X × ℝ ↦ H p.1 i j + p.2 * A p.1 i j)
        fun_prop
      | inr j =>
        change Continuous (fun p : X × ℝ ↦ ∑ a, A p.1 i a * k p.1 a)
        fun_prop
    | inr i =>
      cases j with
      | inl j =>
        change Continuous (fun p : X × ℝ ↦ ∑ a, l p.1 a * A p.1 a j)
        fun_prop
      | inr j => exact continuous_const
  have hnonzero (p : X × ℝ) (hp : p ∈ K ×ˢ Metric.closedBall (0 : ℝ) ε) :
      (borderedPencil (H p.1) (A p.1) (k p.1) (l p.1) p.2).det ≠ 0 := by
    apply borderedPencil_det_ne_zero (hleft p.1 hp.1) (hnorm p.1 hp.1)
    apply abs_pos.mp
    apply hδ.trans_le
    exact hgap p.1 hp.1 p.2 (by simpa [Metric.mem_closedBall, Real.dist_eq] using hp.2)
  obtain ⟨δB, hδB, hBbound⟩ := (hK.prod (isCompact_closedBall (0 : ℝ) ε)).exists_forall_le'
    hB.matrix_det.abs.continuousOn (fun p hp ↦ abs_pos.mpr (hnonzero p hp))
  refine ⟨ε, hε, min δ δB, lt_min hδ hδB, ?_⟩
  intro x hx e he
  exact ⟨(min_le_left _ _).trans (hgap x hx e he), (min_le_right _ _).trans
    (hBbound (x, e) ⟨hx, by simpa [Metric.mem_closedBall, Real.dist_eq] using he⟩)⟩
end Compact
end JanetCartan.RegularSector.Characteristic
