module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.InverseStability.LowOrder

/-!
# Subtraction of differentiated inverse equations

For `app:lem:common-hamilton-phase`, isolate the top inverse jet. All partition
terms use strictly lower inverse jets. The half gap absorbs the top difference.
-/

@[expose] public noncomputable section
open Filter
open scoped ContDiff Topology
namespace JanetCartan.HamiltonPhase.InverseContinuity
variable {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The finite polynomial controlling the lower-inverse-jet remainder difference
in `app:lem:common-hamilton-phase`. It depends only on the order and jet budget. -/
def inverseJetDifferenceConstant (n : ℕ) (M : ℝ) : ℝ :=
  ∑ s : OrderedFinpartition n with 2 ≤ s.length,
    (M * s.length * M ^ (s.length - 1) + M ^ s.length)

/-- Nonnegativity of the remainder difference constant used by the inverse
induction step in `app:lem:common-hamilton-phase`. -/
theorem inverseJetDifferenceConstant_nonneg (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ inverseJetDifferenceConstant n M := by
  unfold inverseJetDifferenceConstant
  positivity

/-- `app:lem:common-hamilton-phase`: the Faà di Bruno remainder difference
uses equation jets through `n` and inverse jets strictly below `n`. Its consumer is
`norm_inverse_jet_sub_le`; no top perturbed inverse bound is needed. -/
theorem norm_jetPartitionRemainder_sub_le {n : ℕ} {M ε : ℝ}
    (hM : 1 ≤ M) (hε : 0 ≤ ε)
    {f f₀ : X → X} {g g₀ : P → X} {p : P}
    (hfjet : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j f (g p)‖ ≤ M)
    (hfdiff : ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDeriv ℝ j f (g p) - iteratedFDeriv ℝ j f₀ (g₀ p)‖ ≤ ε)
    (hgjet : ∀ j, 1 ≤ j → j < n → ‖iteratedFDeriv ℝ j g p‖ ≤ M)
    (hg₀jet : ∀ j, 1 ≤ j → j < n → ‖iteratedFDeriv ℝ j g₀ p‖ ≤ M)
    (hgdiff : ∀ j, 1 ≤ j → j < n →
      ‖iteratedFDeriv ℝ j g p - iteratedFDeriv ℝ j g₀ p‖ ≤ ε) :
    ‖ODE.jetPartitionRemainder n f g p - ODE.jetPartitionRemainder n f₀ g₀ p‖ ≤
      inverseJetDifferenceConstant n M * ε := by
  classical
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  simp only [ODE.jetPartitionRemainder, inverseJetDifferenceConstant,
    ← Finset.sum_sub_distrib, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s hs
  have hs2 := (Finset.mem_filter.mp hs).2
  have hsize (i : Fin s.length) := ODE.partSize_lt_of_two_le_length s hs2 i
  have hb (i : Fin s.length) : ‖iteratedFDeriv ℝ (s.partSize i) g p‖ ≤ M :=
    hgjet _ (s.partSize_pos i) (hsize i)
  have hb₀ (i : Fin s.length) : ‖iteratedFDeriv ℝ (s.partSize i) g₀ p‖ ≤ M :=
    hg₀jet _ (s.partSize_pos i) (hsize i)
  have h₁ : ‖fun i ↦ iteratedFDeriv ℝ (s.partSize i) g p‖ ≤ M :=
    (pi_norm_le_iff_of_nonneg hM0).mpr hb
  have h₀ : ‖fun i ↦ iteratedFDeriv ℝ (s.partSize i) g₀ p‖ ≤ M :=
    (pi_norm_le_iff_of_nonneg hM0).mpr hb₀
  have hd : ‖(fun i ↦ iteratedFDeriv ℝ (s.partSize i) g p) -
      (fun i ↦ iteratedFDeriv ℝ (s.partSize i) g₀ p)‖ ≤ ε := by
    apply (pi_norm_le_iff_of_nonneg hε).mpr
    intro i
    exact hgdiff _ (s.partSize_pos i) (hsize i)
  have hp : ∏ i, ‖iteratedFDeriv ℝ (s.partSize i) g₀ p‖ ≤
      M ^ s.length := by
    calc
      _ ≤ ∏ _i : Fin s.length, M :=
        Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ hb₀ i)
      _ = _ := by simp
  apply (s.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le
    (iteratedFDeriv ℝ s.length f (g p))
    (iteratedFDeriv ℝ s.length f₀ (g₀ p))
    (fun i ↦ iteratedFDeriv ℝ (s.partSize i) g p)
    (fun i ↦ iteratedFDeriv ℝ (s.partSize i) g₀ p)).trans
  calc
    _ ≤ M * s.length * M ^ (s.length - 1) * ε + ε * M ^ s.length := by
      gcongr
      · exact hfjet _ (by omega) s.length_le
      · exact max_le h₁ h₀
      · exact hfdiff _ (by omega) s.length_le
    _ = _ := by ring

private theorem norm_le_twice_comp (B : X →L[ℝ] X)
    (hB : ‖B - ContinuousLinearMap.id ℝ X‖ ≤ 1 / 2)
    {n : ℕ} (T : P [×n]→L[ℝ] X) :
    ‖T‖ ≤ 2 * ‖B.compContinuousMultilinearMap T‖ := by
  have he : T = B.compContinuousMultilinearMap T -
      (B - ContinuousLinearMap.id ℝ X).compContinuousMultilinearMap T := by
    ext v
    simp
  have h := norm_sub_le (B.compContinuousMultilinearMap T)
    ((B - ContinuousLinearMap.id ℝ X).compContinuousMultilinearMap T)
  rw [← he] at h
  have hb := ((B - ContinuousLinearMap.id ℝ X).norm_compContinuousMultilinearMap_le T).trans
    (mul_le_mul_of_nonneg_right hB (norm_nonneg T))
  linarith

/-- `app:lem:common-hamilton-phase`: the highest inverse-jet difference follows
from the actual inverse equations, forward jets through order `n`, and lower
inverse differences. The consumer is the finite-order compact-set induction. -/
theorem norm_inverse_jet_sub_le {n : ℕ} (hn : 0 < n) {M ε : ℝ}
    (hM : 1 ≤ M) (hε : 0 ≤ ε)
    {f f₀ : X → X} {g g₀ : P → X} {p : P} (L : P →L[ℝ] X)
    (hf : ContDiffAt ℝ n f (g p)) (hf₀ : ContDiffAt ℝ n f₀ (g₀ p))
    (hg : ContDiffAt ℝ n g p) (hg₀ : ContDiffAt ℝ n g₀ p)
    (heq : f ∘ g =ᶠ[𝓝 p] L) (heq₀ : f₀ ∘ g₀ =ᶠ[𝓝 p] L)
    (hgap : ‖fderiv ℝ f (g p) - ContinuousLinearMap.id ℝ X‖ ≤ 1 / 2)
    (hfjet : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j f (g p)‖ ≤ M)
    (hfdiff : ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDeriv ℝ j f (g p) - iteratedFDeriv ℝ j f₀ (g₀ p)‖ ≤ ε)
    (hgjet : ∀ j, 1 ≤ j → j < n → ‖iteratedFDeriv ℝ j g p‖ ≤ M)
    (hg₀jet : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j g₀ p‖ ≤ M)
    (hgdiff : ∀ j, 1 ≤ j → j < n →
      ‖iteratedFDeriv ℝ j g p - iteratedFDeriv ℝ j g₀ p‖ ≤ ε) :
    ‖iteratedFDeriv ℝ n g p - iteratedFDeriv ℝ n g₀ p‖ ≤
      2 * (inverseJetDifferenceConstant n M + M) * ε := by
  let B := fderiv ℝ f (g p)
  let B₀ := fderiv ℝ f₀ (g₀ p)
  let T := iteratedFDeriv ℝ n g p
  let T₀ := iteratedFDeriv ℝ n g₀ p
  let R := ODE.jetPartitionRemainder n f g p
  let R₀ := ODE.jetPartitionRemainder n f₀ g₀ p
  have hR : ‖R - R₀‖ ≤ inverseJetDifferenceConstant n M * ε :=
    norm_jetPartitionRemainder_sub_le hM hε hfjet hfdiff hgjet
      (fun j hj hjn ↦ hg₀jet j hj hjn.le) hgdiff
  have hB : ‖B - B₀‖ ≤ ε := by
    have h := hfdiff 1 le_rfl hn
    simpa only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
      ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map,
      iteratedFDeriv_zero_eq_comp] using h
  have hT := normalized_inverse_jet_identity L hn hf hg heq
  have hT₀ := normalized_inverse_jet_identity L hn hf₀ hg₀ heq₀
  have hid : B.compContinuousMultilinearMap (T - T₀) =
      -(R - R₀) - (B - B₀).compContinuousMultilinearMap T₀ := by
    have hh : B.compContinuousMultilinearMap T - B₀.compContinuousMultilinearMap T₀ =
        -(R - R₀) := by rw [hT, hT₀]; abel
    have he : B.compContinuousMultilinearMap (T - T₀) =
        (B.compContinuousMultilinearMap T - B₀.compContinuousMultilinearMap T₀) -
          (B - B₀).compContinuousMultilinearMap T₀ := by ext v; simp
    rw [he, hh]
  have hb := norm_le_twice_comp B hgap (T - T₀)
  rw [hid] at hb
  have he := (norm_sub_le (-(R - R₀)) ((B - B₀).compContinuousMultilinearMap T₀)).trans
    (add_le_add (by simpa only [norm_neg] using hR)
      (((B - B₀).norm_compContinuousMultilinearMap_le T₀).trans
        (mul_le_mul hB (hg₀jet n hn le_rfl) (norm_nonneg _) hε)))
  nlinarith

end JanetCartan.HamiltonPhase.InverseContinuity
