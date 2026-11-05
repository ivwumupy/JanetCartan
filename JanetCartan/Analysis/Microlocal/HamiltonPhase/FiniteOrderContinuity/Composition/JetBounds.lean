module

public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import JanetCartan.Analysis.ContDiff.Norm.Composition.Basic

/-!
# Difference bounds for finite composition jets

The Faà di Bruno difference estimate used by finite-order continuity in
`app:lem:common-hamilton-phase`. Its consumer is `exists_cNorm_comp_sub_lt`.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.HamiltonPhase.CompositionContinuity

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `app:lem:common-hamilton-phase`: the finite polynomial multiplying the jet error. -/
def jetDifferenceConstant (m : ℕ) (A B : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (m + 1), ∑ p : OrderedFinpartition n,
    (A * p.length * B ^ (p.length - 1) + B ^ p.length)

/-- `app:lem:common-hamilton-phase`: nonnegativity of the jet difference constant. -/
theorem jetDifferenceConstant_nonneg (m : ℕ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ jetDifferenceConstant m A B := by
  unfold jetDifferenceConstant
  positivity

/-- `app:lem:common-hamilton-phase`: compare compositions from bounds on their
jets, including the outer jets evaluated at the two different inner values.
Only derivatives through order `m` occur. -/
theorem cNorm_comp_sub_le_of_jet_bounds {K : Set E} {m : ℕ}
    {f f₀ : F → G} {g g₀ : E → F}
    (hf : ∀ x ∈ K, ContDiffAt ℝ m f (g x))
    (hf₀ : ∀ x ∈ K, ContDiffAt ℝ m f₀ (g₀ x))
    (hg : ∀ x ∈ K, ContDiffAt ℝ m g x)
    (hg₀ : ∀ x ∈ K, ContDiffAt ℝ m g₀ x)
    {A B η : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hη : 0 ≤ η)
    (houter : ∀ i ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ i f₀ (g₀ x)‖ ≤ A)
    (hinner : ∀ i ≤ m, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ i g₀ x‖ ≤ B ∧ ‖iteratedFDeriv ℝ i g x‖ ≤ B)
    (houterDiff : ∀ i ≤ m, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ i f₀ (g₀ x) - iteratedFDeriv ℝ i f (g x)‖ ≤ η)
    (hinnerDiff : ∀ i ≤ m, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ i g₀ x - iteratedFDeriv ℝ i g x‖ ≤ η) :
    cNorm K m (f ∘ g - f₀ ∘ g₀) ≤ jetDifferenceConstant m A B * η := by
  rw [jetDifferenceConstant, Finset.sum_mul]
  apply cNorm_le_sum_of_bounds
  · intro n _
    positivity
  intro n hn x hx
  rw [iteratedFDeriv_sub_apply (((hf x hx).comp x (hg x hx)).of_le
      (by exact_mod_cast hn)) (((hf₀ x hx).comp x (hg₀ x hx)).of_le
      (by exact_mod_cast hn)), norm_sub_rev,
    iteratedFDeriv_comp (hf₀ x hx) (hg₀ x hx) (by exact_mod_cast hn),
    iteratedFDeriv_comp (hf x hx) (hg x hx) (by exact_mod_cast hn)]
  simp only [FormalMultilinearSeries.taylorComp, ← Finset.sum_sub_distrib,
    Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p _
  apply (p.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le
    (iteratedFDeriv ℝ p.length f₀ (g₀ x)) (iteratedFDeriv ℝ p.length f (g x))
    (fun i ↦ iteratedFDeriv ℝ (p.partSize i) g₀ x)
    (fun i ↦ iteratedFDeriv ℝ (p.partSize i) g x)).trans
  have h₀ : ‖fun i ↦ iteratedFDeriv ℝ (p.partSize i) g₀ x‖ ≤ B :=
    (pi_norm_le_iff_of_nonneg hB).mpr fun i ↦ (hinner _ ((p.partSize_le i).trans hn) x hx).1
  have h₁ : ‖fun i ↦ iteratedFDeriv ℝ (p.partSize i) g x‖ ≤ B :=
    (pi_norm_le_iff_of_nonneg hB).mpr fun i ↦ (hinner _ ((p.partSize_le i).trans hn) x hx).2
  have hd : ‖(fun i ↦ iteratedFDeriv ℝ (p.partSize i) g₀ x) -
      (fun i ↦ iteratedFDeriv ℝ (p.partSize i) g x)‖ ≤ η :=
    (pi_norm_le_iff_of_nonneg hη).mpr fun i ↦ hinnerDiff _ ((p.partSize_le i).trans hn) x hx
  have hp : ∏ i, ‖iteratedFDeriv ℝ (p.partSize i) g x‖ ≤ B ^ p.length := by
    calc
      _ ≤ ∏ _i : Fin p.length, B := Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
        (fun i _ ↦ (hinner _ ((p.partSize_le i).trans hn) x hx).2)
      _ = _ := by simp
  calc
    _ ≤ A * p.length * B ^ (p.length - 1) * η + η * B ^ p.length := by
      gcongr
      · exact houter _ (p.length_le.trans hn) x hx
      · exact max_le h₀ h₁
      · exact houterDiff _ (p.length_le.trans hn) x hx
    _ = _ := by ring

end JanetCartan.HamiltonPhase.CompositionContinuity
