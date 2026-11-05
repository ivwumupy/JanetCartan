module

public import JanetCartan.Analysis.Sobolev.Local.Cutoff.AllOrders.Expressions

/-!
# All-order multiplication of weak jets by smooth cutoffs

The whole-space cutoff estimate used by `app:ch_regular:eq:one-gain-tame`
and `app:ch_regular:thm:exact-correction`. The jet is constructed by repeated
weak Leibniz differentiation. The constant is chosen before the input function
and jet. Restriction norms and zero extension are handled by the consumer.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Function
open scoped ContDiff

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace CutoffJet

/-- The explicit differential expression for the `j`th cutoff jet, obtained
by differentiating and uncurrying (`app:ch_regular:eq:one-gain-tame`). -/
def expression (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (j : ℕ) → Expr n F ((EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F)
  | 0 => .atom 0 φ hs hc (.id ℝ _)
  | j + 1 => ((expression φ hs hc j).deriv).map
      (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (j + 1) ↦ EuclideanSpace ℝ (Fin n)) F).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The product expression at order `j` uses only original orders at most `j`
(`app:ch_regular:eq:one-gain-tame`). -/
theorem order_expression_le (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (j : ℕ) :
    (expression (F := F) φ hs hc j).order ≤ j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    rw [expression, Expr.order_map]
    exact (Expr.order_deriv_le _).trans (Nat.add_le_add_right ih 1)

end CutoffJet

/-- Construct every component of the cutoff jet from the original jet,
without assuming product regularity (`app:ch_regular:eq:one-gain-tame`). -/
def cutoffAllJet (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F) :
    (j : ℕ) → EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F :=
  fun j ↦ (CutoffJet.expression φ hs hc j).eval J

/-- The constructed all-order cutoff jet satisfies the weak identities
(`app:ch_regular:eq:one-gain-tame`). -/
theorem hasWeakJetOn_cutoffAllJet [CompleteSpace F]
    {f : EuclideanSpace ℝ (Fin n) → F}
    {J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F} {s : ℕ}
    (hw : Mollification.HasWeakJetOn volume f J univ s)
    (hJ : ∀ j ≤ s, MemLp (J j) 2 volume)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hs : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    Mollification.HasWeakJetOn volume (fun x ↦ φ x • f x)
      (cutoffAllJet φ hs hc J) univ s := by
  refine ⟨?_, fun j hj ↦ ?_⟩
  · ext x v
    simp [cutoffAllJet, CutoffJet.expression, CutoffJet.Expr.eval, hw.1,
      iteratedFDeriv_zero_apply]
  · have h := (CutoffJet.expression (F := F) φ hs hc j).hasWeakFDerivOn_eval hw hJ
      ((CutoffJet.order_expression_le φ hs hc j).trans_lt hj)
    convert h using 1
    · rfl
    · funext x
      simp only [cutoffAllJet, CutoffJet.expression, comp_apply, CutoffJet.Expr.eval_map,
        ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        LinearIsometryEquiv.apply_symm_apply]

/-- Every constructed component through the specified order is L²
(`app:ch_regular:eq:one-gain-tame`). -/
theorem memLp_cutoffAllJet
    {J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F} {s : ℕ}
    (hJ : ∀ j ≤ s, MemLp (J j) 2 volume)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hs : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) {j : ℕ} (hj : j ≤ s) :
    MemLp (cutoffAllJet φ hs hc J j) 2 volume :=
  (CutoffJet.expression φ hs hc j).memLp_eval J
    (fun k hk ↦ hJ k (hk.trans ((CutoffJet.order_expression_le φ hs hc j).trans hj)))

/-- The all-order cutoff constant is chosen before the function and its weak
jet. No derivative loss occurs (`app:ch_regular:eq:one-gain-tame`). -/
theorem exists_cutoffAllJet_bound
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hs : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F),
      (∀ j ≤ s, MemLp (J j) 2 volume) →
      ∑ j ∈ Finset.range (s + 1), (eLpNorm (cutoffAllJet φ hs hc J j) 2 volume).toReal ≤
        C * ∑ j ∈ Finset.range (s + 1), (eLpNorm (J j) 2 volume).toReal := by
  choose C hC hbound using fun j ↦ (CutoffJet.expression (F := F) φ hs hc j).exists_bound
  refine ⟨max 1 (∑ j ∈ Finset.range (s + 1), C j), le_max_left _ _, fun J hJ ↦ ?_⟩
  calc
    _ ≤ ∑ j ∈ Finset.range (s + 1),
        C j * ∑ k ∈ Finset.range (s + 1), (eLpNorm (J k) 2 volume).toReal := by
      apply Finset.sum_le_sum
      intro j hj
      exact hbound j s J ((CutoffJet.order_expression_le φ hs hc j).trans
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) hJ
    _ = (∑ j ∈ Finset.range (s + 1), C j) *
        ∑ k ∈ Finset.range (s + 1), (eLpNorm (J k) 2 volume).toReal :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg)

/-- A fixed smooth bump multiplies every whole-space weak Sobolev jet of order
`s` with a uniform constant. This is the prerequisite for transporting the
cutoff estimate through the infimum restriction norm in
`app:ch_regular:eq:one-gain-tame` and `app:ch_regular:thm:exact-correction`. -/
theorem exists_bump_weakJet_bound [CompleteSpace F]
    {x : EuclideanSpace ℝ (Fin n)} (χ : ContDiffBump x) (s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : EuclideanSpace ℝ (Fin n) → F)
      (J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
        (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F),
      Mollification.HasWeakJetOn volume f J univ s → MemLp f 2 volume →
      (∀ j ≤ s, MemLp (J j) 2 volume) →
      ∃ K : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
          (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F,
        Mollification.HasWeakJetOn volume (fun y ↦ χ y • f y) K univ s ∧
        (∀ j ≤ s, MemLp (K j) 2 volume) ∧
        ∑ j ∈ Finset.range (s + 1), (eLpNorm (K j) 2 volume).toReal ≤
          C * ∑ j ∈ Finset.range (s + 1), (eLpNorm (J j) 2 volume).toReal := by
  obtain ⟨C, hC, hbound⟩ := exists_cutoffAllJet_bound (F := F) χ χ.contDiff χ.hasCompactSupport s
  refine ⟨C, hC, fun f J hw _hf hJ ↦ ⟨cutoffAllJet χ χ.contDiff χ.hasCompactSupport J,
    hasWeakJetOn_cutoffAllJet hw hJ χ.contDiff χ.hasCompactSupport,
    fun j hj ↦ memLp_cutoffAllJet hJ χ.contDiff χ.hasCompactSupport hj, hbound J hJ⟩⟩

end JanetCartan.LocalSobolev
