module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.NormComparison.MixedEvaluations
public import Mathlib.Logic.Equiv.Fintype

/-!
# Symmetric tensor norms from ordered retarded evaluations

For `app:ch_osc:prop:osc-retarded-tube`, symmetry moves every time direction
before the transverse directions. Every resulting ordered transverse word is
present in `JetIndex`, with its multiplicity retained. Basis expansion then
bounds the Fréchet operator norm by these evaluations. The estimate is consumed
by the local Sobolev comparison for `app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section

namespace JanetCartan.ResponseTransfer

open RetardedSobolev.Spaces LocalSobolev

/-- Complex-valued basis expansion for the retarded norm comparison in
`app:ch_osc:prop:osc-retarded-tube`. This is the complex-output counterpart of
the scalar basis expansion in `BallExtension`'s symmetric jet bound. -/
private theorem complex_tensor_norm_le_basis_sum {n j : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ EuclideanSpace ℝ (Fin n)) ℂ) :
    ‖A‖ ≤ ∑ a : Fin j → Fin n, ‖A (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ (a k))‖ := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  intro v
  have hv : v = fun k ↦ ∑ i, b.repr (v k) i • b i := by
    funext k
    exact (b.sum_repr (v k)).symm
  calc
    ‖A v‖ = ‖∑ a : Fin j → Fin n, (∏ k, b.repr (v k) (a k)) •
        A (fun k ↦ b (a k))‖ := by
      conv_lhs => rw [hv, A.map_sum]
      simp only [A.map_smul_univ]
    _ ≤ ∑ a : Fin j → Fin n, ‖(∏ k, b.repr (v k) (a k)) •
        A (fun k ↦ b (a k))‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin j → Fin n, ‖A (fun k ↦ b (a k))‖ * ∏ k, ‖v k‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul, norm_prod, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
      intro k _
      exact (PiLp.norm_apply_le (b.repr (v k)) (a k)).trans_eq (b.repr.norm_map _)
    _ = _ := (Finset.sum_mul ..).symm

/-- Group the time slots first, preserving all transverse slots. Used to identify
basis evaluations in the norm comparison for `app:ch_osc:prop:osc-retarded-tube`. -/
private theorem exists_time_first_coordinate_word {d j : ℕ} (a : Fin j → Fin (d + 1)) :
    ∃ t k : ℕ, ∃ e : Fin (t + k) ≃ Fin j, ∃ w : Fin k → Fin d,
      ∀ q, a (e q) = Fin.addCases (fun _ : Fin t ↦ 0) (fun r ↦ (w r).succ) q := by
  classical
  let T := {q : Fin j // a q = 0}
  let X := {q : Fin j // a q ≠ 0}
  let t := Fintype.card T
  let k := Fintype.card X
  let et : Fin t ≃ T := (Fintype.equivFin T).symm
  let ex : Fin k ≃ X := (Fintype.equivFin X).symm
  let e : Fin (t + k) ≃ Fin j := finSumFinEquiv.symm |>.trans
    ((Equiv.sumCongr et ex).trans (Equiv.sumCompl (fun q ↦ a q = 0)))
  let w : Fin k → Fin d := fun r ↦ (a (ex r).val).pred (ex r).property
  refine ⟨t, k, e, w, ?_⟩
  intro q
  refine Fin.addCases (fun r ↦ ?_) (fun r ↦ ?_) q
  · simp only [Fin.addCases_left, e, Equiv.trans_apply,
      finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply]
    exact (et r).property
  · simp only [Fin.addCases_right, e, Equiv.trans_apply,
      finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply]
    exact (Fin.succ_pred (a (ex r).val) (ex r).property).symm

/-- A symmetric basis evaluation is one of the actual ordered retarded
evaluations for `app:ch_osc:prop:osc-retarded-tube`. -/
private theorem symmetric_basis_eq_retardedJetEvaluation {d s j : ℕ}
    (J : (j : ℕ) → (Euclidean (d + 1)) [×j]→L[ℝ] ℂ)
    (hsym : ∀ j ≤ s, ∀ v : Fin j → Euclidean (d + 1),
      ∀ σ : Equiv.Perm (Fin j), J j (v ∘ σ) = J j v)
    (hj : j ≤ s) (a : Fin j → Fin (d + 1)) :
    ∃ i : JetIndex d s,
      J j (fun q ↦ EuclideanSpace.basisFun (Fin (d + 1)) ℝ (a q)) =
        retardedJetEvaluation J i := by
  obtain ⟨t, k, e, w, he⟩ := exists_time_first_coordinate_word a
  have hcard : t + k = j := by simpa using Fintype.card_congr e
  subst j
  let i : JetIndex d s := ⟨⟨k, by omega⟩, w, ⟨t, by change t < s - k + 1; omega⟩⟩
  refine ⟨i, ?_⟩
  rw [← hsym (t + k) hj _ e]
  change J (t + k) (fun q ↦ EuclideanSpace.basisFun (Fin (d + 1)) ℝ (a (e q))) =
    J (t + k) (fun q ↦ EuclideanSpace.basisFun (Fin (d + 1)) ℝ
      (Fin.addCases (fun _ : Fin t ↦ 0) (fun r ↦ (w r).succ) q))
  congr 1
  funext q
  rw [he q]

/-- Symmetric Fréchet tensors are controlled by the ordered retarded evaluations
in `app:ch_osc:prop:osc-retarded-tube`, with a constant depending only on dimension
and grade. This is the pointwise reverse comparison consumed by the envelope
estimate `app:ch_response:eq:fixed-factor-transfer`.

The explicit constant is `(d + 1)^s`. No positivity of the transverse dimension
or derivative order is required, and all ordered-word multiplicities remain in
the sum. The symmetry premise is supplied by smooth jets in the consumer. -/
theorem exists_norm_le_sum_retardedJetEvaluation_of_symmetric (d s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ J : (j : ℕ) → (Euclidean (d + 1)) [×j]→L[ℝ] ℂ,
        (∀ j ≤ s, ∀ v : Fin j → Euclidean (d + 1),
          ∀ σ : Equiv.Perm (Fin j), J j (v ∘ σ) = J j v) →
        ∀ j ≤ s, ‖J j‖ ≤ C * ∑ i : JetIndex d s, ‖retardedJetEvaluation J i‖ := by
  classical
  refine ⟨((d + 1 : ℕ) : ℝ) ^ s, by positivity, ?_⟩
  intro J hsym j hj
  let S : ℝ := ∑ i : JetIndex d s, ‖retardedJetEvaluation J i‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hterm (a : Fin j → Fin (d + 1)) :
      ‖J j (fun q ↦ EuclideanSpace.basisFun (Fin (d + 1)) ℝ (a q))‖ ≤ S := by
    obtain ⟨i, hi⟩ := symmetric_basis_eq_retardedJetEvaluation J hsym hj a
    rw [hi]
    exact Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)
  calc
    ‖J j‖ ≤ ∑ a : Fin j → Fin (d + 1),
        ‖J j (fun q ↦ EuclideanSpace.basisFun (Fin (d + 1)) ℝ (a q))‖ :=
      complex_tensor_norm_le_basis_sum _
    _ ≤ ∑ _a : Fin j → Fin (d + 1), S := Finset.sum_le_sum fun a _ ↦ hterm a
    _ = ((d + 1 : ℕ) : ℝ) ^ j * S := by simp
    _ ≤ ((d + 1 : ℕ) : ℝ) ^ s * S :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_cast; omega) hj) hS

end JanetCartan.ResponseTransfer
