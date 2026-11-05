module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.PhaseTrade.Algebra
public import Mathlib.LinearAlgebra.Matrix.Bilinear
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# Smooth rectangular derivative-trade coefficients

Smoothness and one-high bounds for the rational matrix operations used in
`app:ch_background:eq:bg-derivative-trade`. The low matrix range and transverse
gap are fixed before the fields. Turning these bounds into primitive phase and
carrier bounds additionally requires estimating the actual differentiated inputs.
-/

@[expose] public noncomputable section

open Matrix Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint

variable {n p : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem contDiff_transpose {a b : ℕ} {N : ℕ∞ω} :
    ContDiff ℝ N (fun A : Matrix (Fin a) (Fin b) ℝ ↦ Aᵀ) :=
  (Matrix.transposeLinearEquiv (Fin a) (Fin b) ℝ ℝ).toLinearMap.toContinuousLinearMap.contDiff

private theorem contDiff_rectangular_mul {a b c : ℕ} {N : ℕ∞ω} :
    ContDiff ℝ N (fun q : Matrix (Fin a) (Fin b) ℝ × Matrix (Fin b) (Fin c) ℝ ↦
      q.1 * q.2) :=
  (mulLinearMap (l := Fin a) (m := Fin b) (n := Fin c) (A := ℝ) ℝ).toContinuousBilinearMap.isBoundedBilinearMap.contDiff

/-- The Gram operation is smooth; source:
`app:ch_background:eq:bg-derivative-trade`. -/
theorem contDiff_transverseGram {N : ℕ∞ω} :
    ContDiff ℝ N (transverseGram (n := n)) :=
  contDiff_rectangular_mul.comp (contDiff_transpose.prodMk contDiff_id)

/-- Smoothness of the actual rational left inverse at every matrix with the
transverse gap (`app:ch_background:eq:bg-derivative-trade`). -/
theorem contDiffAt_transverseLeftInverse {A : TransverseMatrix n} {δ : ℝ}
    (hδ : 0 < δ) (hA : TransverseGap δ A) {N : ℕ∞ω} :
    ContDiffAt ℝ N transverseLeftInverse A :=
  contDiff_rectangular_mul.contDiffAt.comp A
    (((contDiffAt_matrix_inv (isUnit_transverseGram hδ hA)).comp A
      contDiff_transverseGram.contDiffAt).prodMk contDiff_transpose.contDiffAt)

/-- A smooth rectangular field with the transverse gap has a smooth left
inverse, locally on its working domain; source:
`app:ch_background:eq:bg-derivative-trade`. -/
theorem contDiffOn_transverseLeftInverse {A : E → TransverseMatrix n} {U : Set E}
    {δ : ℝ} (hδ : 0 < δ) (hA : ∀ x ∈ U, TransverseGap δ (A x)) {N : ℕ∞ω}
    (hAs : ContDiffOn ℝ N A U) :
    ContDiffOn ℝ N (fun x ↦ transverseLeftInverse (A x)) U := by
  intro x hx
  exact (contDiffAt_transverseLeftInverse hδ (hA x hx)).comp_contDiffWithinAt x (hAs x hx)

/-- The literal carrier coefficient `B L`, where `B = D_z Y`, in
`app:ch_background:eq:bg-derivative-trade`. -/
def transverseCarrierCoefficient
    (q : TransverseMatrix n × Matrix (Fin p) (Fin (n - 1)) ℝ) :
    Matrix (Fin p) (Fin n) ℝ :=
  q.2 * transverseLeftInverse q.1

/-- Smoothness of the carrier rational coefficient, with no carrier derivative
discarded (`app:ch_background:eq:bg-derivative-trade`). -/
theorem contDiffAt_transverseCarrierCoefficient
    {q : TransverseMatrix n × Matrix (Fin p) (Fin (n - 1)) ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hq : TransverseGap δ q.1) {N : ℕ∞ω} :
    ContDiffAt ℝ N transverseCarrierCoefficient q :=
  contDiff_rectangular_mul.contDiffAt.comp q
    (contDiffAt_snd.prodMk ((contDiffAt_transverseLeftInverse hδ hq).comp q contDiffAt_fst))

/-- The bounded matrix range with a fixed transverse gap is compact. This fixes
all inverse constants before a family in `app:ch_background:eq:bg-derivative-trade`. -/
theorem isCompact_transverseGap_range (M δ : ℝ) :
    IsCompact {A : TransverseMatrix n | ‖A‖ ≤ M ∧ TransverseGap δ A} := by
  have hg : IsClosed {A : TransverseMatrix n | TransverseGap δ A} := by
    change IsClosed {A : TransverseMatrix n | ∀ v, δ * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v)}
    simp_rw [ofPred_forall]
    apply isClosed_iInter
    intro v
    exact isClosed_le continuous_const
      ((continuous_id.matrix_mulVec continuous_const).dotProduct
        (continuous_id.matrix_mulVec continuous_const))
  exact (isCompact_closedBall (0 : TransverseMatrix n) M).of_isClosed_subset
    ((isClosed_le continuous_norm continuous_const).inter hg)
    (fun A hA ↦ by simpa using hA.1)

set_option maxHeartbeats 800000 in
/-- One-high finite mixed jets of the rectangular left inverse from the matrix
field's jets. The gap and low bound are fixed, and `k = r` is allowed.
Source: `app:ch_background:eq:bg-derivative-trade`. -/
theorem exists_cNorm_transverseLeftInverse_le_tame [FiniteDimensional ℝ E]
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) (M : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {r k : ℕ} (hrk : r ≤ k) :
    ∃ C > 0, ∀ A : E → TransverseMatrix n, ContDiff ℝ ∞ A →
      (∀ y ∈ Metric.closedBall x ρ, ‖A y‖ ≤ M ∧ TransverseGap δ (A y)) →
      cNorm (Metric.closedBall x ρ) r (fun y ↦ transverseLeftInverse (A y)) ≤
        C * (1 + cNorm (Metric.closedBall x ρ) k A) := by
  obtain ⟨C, hC, hb⟩ := exists_cNorm_comp_le_tame_closedBall_of_compact_range
    (g := transverseLeftInverse (n := n)) x hρ
    (isCompact_transverseGap_range (n := n) M δ) hrk
    (fun _ hA ↦ contDiffAt_transverseLeftInverse hδ hA.2)
  exact ⟨C, hC, hb⟩

/-- One-high finite mixed jets of `B L` from the joint input `(A,B)`.
Here `B` must be instantiated with the actual carrier derivative of `Y`.
Source: `app:ch_background:eq:bg-derivative-trade`. -/
theorem exists_cNorm_transverseCarrierCoefficient_le_tame [FiniteDimensional ℝ E]
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) (M B : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {r k : ℕ} (hrk : r ≤ k) :
    ∃ C > 0, ∀ U : E → TransverseMatrix n × Matrix (Fin p) (Fin (n - 1)) ℝ,
      ContDiff ℝ ∞ U →
      (∀ y ∈ Metric.closedBall x ρ,
        (‖(U y).1‖ ≤ M ∧ TransverseGap δ (U y).1) ∧ ‖(U y).2‖ ≤ B) →
      cNorm (Metric.closedBall x ρ) r (fun y ↦ transverseCarrierCoefficient (U y)) ≤
        C * (1 + cNorm (Metric.closedBall x ρ) k U) := by
  have ht := (isCompact_transverseGap_range (n := n) M δ).prod
    (isCompact_closedBall (0 : Matrix (Fin p) (Fin (n - 1)) ℝ) B)
  obtain ⟨C, hC, hb⟩ := exists_cNorm_comp_le_tame_closedBall_of_compact_range x hρ ht hrk
    (fun q hq ↦ contDiffAt_transverseCarrierCoefficient (p := p) hδ hq.1.2)
  refine ⟨C, hC, fun U hU hUg ↦ hb U hU ?_⟩
  intro y hy
  exact ⟨(hUg y hy).1, by simpa using (hUg y hy).2⟩

end JanetCartan.ContinuumAdjoint
