module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.JointGrades

/-!
# Local jet operations for the selected algebraic grade

Only local inverse smoothness is available at a selected direction. These
local versions of the existing product and linear-pullback bounds are used
by the comparable algebraic profile (`app:ch_regular:eq:high-amplitude`).
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FiniteChain.Retarded.KernelDecay
variable {V W F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The local normalized algebraic profile survives the coordinate
projections into `JointVariables` with their exact norm cost (`high-amplitude`). -/
theorem algebraic_norm_iteratedFDeriv_comp_linear_at_le
    (P : V →L[ℝ] W) {f : W → F} {v : V}
    (hf : ContDiffAt ℝ ∞ f (P v)) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (f ∘ P) v‖ ≤ ‖iteratedFDeriv ℝ k f (P v)‖ * ‖P‖ ^ k := by
  obtain ⟨U, hU, hfu⟩ := hf.contDiffOn (m := (k : ℕ∞ω)) (by simp) (by simp)
  obtain ⟨D, hDU, hD, hv⟩ := mem_nhds_iff.mp hU
  have hpre := hD.preimage P.continuous
  have he := P.iteratedFDerivWithin_comp_right (hfu.mono hDU) hD.uniqueDiffOn hpre.uniqueDiffOn
    hv (i := k) le_rfl
  rw [iteratedFDerivWithin_of_isOpen _ hpre hv, iteratedFDerivWithin_of_isOpen _ hD hv] at he
  rw [he]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ k f (P v)).norm_compContinuousLinearMap_le (fun _ ↦ P)

variable [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

private theorem local_smul_bound {f : V → ℂ} {g : V → F} {v : V}
    (hf : ContDiffAt ℝ ∞ f v) (hg : ContDiffAt ℝ ∞ g v) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y ↦ f y • g y) v‖ ≤
      ∑ j ∈ Finset.range (k+1), (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j f v‖ *
        ‖iteratedFDeriv ℝ (k-j) g v‖ := by
  obtain ⟨U, hU, hfu⟩ := hf.contDiffOn (m := (k : ℕ∞ω)) (by simp) (by simp)
  obtain ⟨W, hW, hgu⟩ := hg.contDiffOn (m := (k : ℕ∞ω)) (by simp) (by simp)
  obtain ⟨D, hDsub, hD, hv⟩ := mem_nhds_iff.mp (inter_mem hU hW)
  have h := norm_iteratedFDerivWithin_smul_le
    (hfu.mono (hDsub.trans inter_subset_left)) (hgu.mono (hDsub.trans inter_subset_right))
    hD.uniqueDiffOn hv (n := k) le_rfl
  simpa only [iteratedFDerivWithin_of_isOpen _ hD hv] using h

/-- Local multiplication by each original mask preserves the normalized
frequency weight and adds no offset. The consuming proof supplies the mask
profiles from their fixed compact seminorms (`high-amplitude`, `chain-tail`). -/
theorem algebraic_norm_iteratedFDeriv_smul_grades
    {f : V → ℂ} {g : V → F} {v : V}
    (hf : ContDiffAt ℝ ∞ f v) (hg : ContDiffAt ℝ ∞ g v)
    {C D : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j) {L S : ℝ} (hL : 0 ≤ L)
    (hfjet : ∀ j, ‖iteratedFDeriv ℝ j f v‖ ≤ C j * L ^ j)
    (hgjet : ∀ j, ‖iteratedFDeriv ℝ j g v‖ ≤ S * D j * L ^ j) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w ↦ f w • g w) v‖ ≤
      S * derivativeConvolution C D k * L ^ k := by
  apply (local_smul_bound hf hg k).trans
  simp only [derivativeConvolution, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  calc
    _ ≤ (k.choose j : ℝ) * (C j * L ^ j) * (S * D (k-j) * L ^ (k-j)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hfjet j) (Nat.cast_nonneg _)) (hgjet _)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC _) (pow_nonneg hL _)))
    _ = S * ((k.choose j : ℝ) * C j * D (k-j)) * (L ^ j * L ^ (k-j)) := by ring
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le hjk]

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
