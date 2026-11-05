module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.AmplitudeDifference.Composition
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.AmplitudeDifference.Products

/-!
# Compact shell calculus for the literal density difference

The consumer is `PrimitiveDensity`: the finite product of primitive evaluations
and the final inverse substitution in `app:ch_osc:prop:osc-normal`, Step 4'.
Compact shells need not be convex. Smooth reference jets are Lipschitz on these
compact sets, even when segments between their points leave the shell.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference.PrimitiveDensity
open HamiltonPhase.CompositionContinuity FullPhaseCharts.InverseEstimates
variable {E F G H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Local polynomial composition bound used to derive every primitive
substitution bound in `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem cNorm_comp_le_from_bounds {K : Set E} {L : Set F}
    (hK : IsCompact K) (hL : IsCompact L) (s : ℕ)
    {f : F → G} {g : E → F}
    (hf : ∀ y ∈ L, ContDiffAt ℝ ∞ f y)
    (hg : ∀ x ∈ K, ContDiffAt ℝ ∞ g x) (hrange : MapsTo g K L)
    {A B : ℝ} (hA : 0 ≤ A)
    (houter : cNorm L s f ≤ A) (hinner : cNorm K s g ≤ B) :
    cNorm K s (f ∘ g) ≤ compositionMultiplicity s * A * (1 + B) ^ s := by
  have h := cNorm_comp_le_polynomial
    (fun x hx ↦ (hg x hx).of_le (by simp))
    (fun x hx ↦ (hf _ (hrange hx)).of_le (by simp))
    (fun _ hi ↦ bddAbove_norm_iteratedFDeriv_of_contDiffAt hK
      (fun x hx ↦ (hg x hx).of_le (by simp)) hi) hA
    (fun i hi x hx ↦ (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hL
      (fun y hy ↦ (hf y hy).of_le (by simp)) (hrange hx) hi).trans houter)
  apply h.trans
  apply mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith [cNorm_nonneg K s g]) (by linarith : 1 + cNorm K s g ≤ 1 + B) s)
  unfold compositionMultiplicity
  positivity

/-- Pairing adds primitive difference budgets. This is the telescoping-array
step for the two measurement, normal and reduced-covector evaluations in
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem cNorm_prod_sub_le {K : Set E} (hK : IsCompact K) (s : ℕ)
    {f f₀ : E → F} {g g₀ : E → G}
    (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x)
    (hf₀ : ∀ x ∈ K, ContDiffAt ℝ ∞ f₀ x)
    (hg : ∀ x ∈ K, ContDiffAt ℝ ∞ g x)
    (hg₀ : ∀ x ∈ K, ContDiffAt ℝ ∞ g₀ x) :
    cNorm K s ((fun x ↦ (f x, g x)) - (fun x ↦ (f₀ x, g₀ x))) ≤
      cNorm K s (f - f₀) + cNorm K s (g - g₀) := by
  exact cNorm_prodMk_le_on K hK s
    (fun x hx ↦ ((hf x hx).sub (hf₀ x hx)).of_le (by simp))
    (fun x hx ↦ ((hg x hx).sub (hg₀ x hx)).of_le (by simp))

/-- Pairing the proved evaluation bounds retains linear dependence on the
primitive error. Consumer: the full shell array and its inverse substitution in
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem pair_evaluation_bounds {K : Set E} (hK : IsCompact K) (s : ℕ)
    {f f₀ : E → F} {g g₀ : E → G} {A B d : ℝ}
    (hf : (∀ x ∈ K, ContDiffAt ℝ ∞ f x ∧ ContDiffAt ℝ ∞ f₀ x) ∧
      cNorm K s f ≤ A ∧ cNorm K s f₀ ≤ A ∧ cNorm K s (f - f₀) ≤ A * d)
    (hg : (∀ x ∈ K, ContDiffAt ℝ ∞ g x ∧ ContDiffAt ℝ ∞ g₀ x) ∧
      cNorm K s g ≤ B ∧ cNorm K s g₀ ≤ B ∧ cNorm K s (g - g₀) ≤ B * d) :
    (∀ x ∈ K, ContDiffAt ℝ ∞ (fun x ↦ (f x, g x)) x ∧
      ContDiffAt ℝ ∞ (fun x ↦ (f₀ x, g₀ x)) x) ∧
    cNorm K s (fun x ↦ (f x, g x)) ≤ A + B ∧
    cNorm K s (fun x ↦ (f₀ x, g₀ x)) ≤ A + B ∧
    cNorm K s ((fun x ↦ (f x, g x)) - (fun x ↦ (f₀ x, g₀ x))) ≤ (A + B) * d := by
  refine ⟨fun x hx ↦ ⟨((hf.1 x hx).1).prodMk ((hg.1 x hx).1),
    ((hf.1 x hx).2).prodMk ((hg.1 x hx).2)⟩, ?_, ?_, ?_⟩
  · exact (cNorm_prodMk_le_on K hK s
      (fun x hx ↦ ((hf.1 x hx).1).of_le (by simp))
      (fun x hx ↦ ((hg.1 x hx).1).of_le (by simp))).trans
        (add_le_add hf.2.1 hg.2.1)
  · exact (cNorm_prodMk_le_on K hK s
      (fun x hx ↦ ((hf.1 x hx).2).of_le (by simp))
      (fun x hx ↦ ((hg.1 x hx).2).of_le (by simp))).trans
        (add_le_add hf.2.2.1 hg.2.2.1)
  · exact (cNorm_prod_sub_le hK s (fun x hx ↦ (hf.1 x hx).1)
      (fun x hx ↦ (hf.1 x hx).2) (fun x hx ↦ (hg.1 x hx).1)
      (fun x hx ↦ (hg.1 x hx).2)).trans
        ((add_le_add hf.2.2.2 hg.2.2.2).trans_eq (by ring))

/-- Fixed smooth reference substitution on an arbitrary compact shell. The
constant precedes the varying outer field, both inner maps and the error.
The actual inputs are separate outer and inner differences; no composed
estimate is assumed. Consumed first by the literal algebraic density operation,
then by inverse substitution in `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_cNorm_comp_sub_le_fixed_reference
    {K : Set E} {L : Set F} (hK : IsCompact K) (hL : IsCompact L)
    {f₀ : F → G} (hf₀ : ∀ y ∈ L, ContDiffAt ℝ ∞ f₀ y)
    (s : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C > 0, ∀ (f : F → G) (g g₀ : E → F) (d : ℝ), 0 ≤ d →
      (∀ y ∈ L, ContDiffAt ℝ ∞ f y) →
      (∀ x ∈ K, ContDiffAt ℝ ∞ g x) →
      (∀ x ∈ K, ContDiffAt ℝ ∞ g₀ x) →
      MapsTo g K L → MapsTo g₀ K L →
      cNorm K s g ≤ B → cNorm K s g₀ ≤ B →
      cNorm L s (f - f₀) ≤ d → cNorm K s (g - g₀) ≤ d →
      cNorm K s (f ∘ g - f₀ ∘ g₀) ≤ C * d := by
  have hlip (i : ℕ) : ∃ R : NNReal, LipschitzOnWith R (iteratedFDeriv ℝ i f₀) L := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hL
    intro y hy
    obtain ⟨R, V, hV, hv⟩ :=
      ((hf₀ y hy).iteratedFDeriv_right (m := 1) (by simp)).exists_lipschitzOnWith
    exact ⟨R, V, mem_nhdsWithin_of_mem_nhds hV, hv⟩
  choose R hR using hlip
  let T : ℝ := ∑ i ∈ Finset.range (s + 1), (R i : ℝ)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let A := cNorm L s f₀
  have hA : 0 ≤ A := cNorm_nonneg _ _ _
  let C := jetDifferenceConstant s A B * (1 + T)
  have hC : 0 ≤ C := mul_nonneg (jetDifferenceConstant_nonneg s hA hB) (by positivity)
  refine ⟨1 + C, by positivity, ?_⟩
  intro f g g₀ d hd hf hg hg₀ hrange hrange₀ hinner hinner₀ hfdiff hgdiff
  have hdg (i : ℕ) (hi : i ≤ s) (x : E) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g₀ x‖ ≤ d :=
    (norm_iteratedFDeriv_sub_le_cNorm hK
      (fun x hx ↦ (hg x hx).of_le (by simp))
      (fun x hx ↦ (hg₀ x hx).of_le (by simp)) hi hx).trans hgdiff
  have hv (x : E) (hx : x ∈ K) : ‖g x - g₀ x‖ ≤ d := by
    have h := hdg 0 (Nat.zero_le _) x hx
    rw [← iteratedFDeriv_sub_apply ((hg x hx).of_le (by simp))
      ((hg₀ x hx).of_le (by simp)), norm_iteratedFDeriv_zero] at h
    exact h
  have hshift (i : ℕ) (hi : i ≤ s) (x : E) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ i f₀ (g x) - iteratedFDeriv ℝ i f₀ (g₀ x)‖ ≤ T * d := by
    have hr : (R i : ℝ) ≤ T := Finset.single_le_sum (fun j _ ↦ (R j).coe_nonneg)
      (Finset.mem_range.mpr (by omega))
    have hh := (hR i).norm_sub_le (hrange hx) (hrange₀ hx)
    exact hh.trans (mul_le_mul hr (hv x hx) (norm_nonneg _) hT)
  have hb := cNorm_comp_sub_le_of_jet_bounds (m := s)
    (fun x hx ↦ (hf _ (hrange hx)).of_le (by simp))
    (fun x hx ↦ (hf₀ _ (hrange₀ hx)).of_le (by simp))
    (fun x hx ↦ (hg x hx).of_le (by simp))
    (fun x hx ↦ (hg₀ x hx).of_le (by simp)) hA hB
    (show 0 ≤ (1 + T) * d by positivity) ?_ ?_ ?_ ?_
  · exact hb.trans (by dsimp [C]; nlinarith)
  · intro i hi x hx
    exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hL
      (fun y hy ↦ (hf₀ y hy).of_le (by simp)) (hrange₀ hx) hi
  · intro i hi x hx
    exact ⟨(norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
        (fun x hx ↦ (hg₀ x hx).of_le (by simp)) hx hi).trans hinner₀,
      (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
        (fun x hx ↦ (hg x hx).of_le (by simp)) hx hi).trans hinner⟩
  · intro i hi x hx
    rw [norm_sub_rev]
    have hsame := (norm_iteratedFDeriv_sub_le_cNorm hL
      (fun y hy ↦ (hf y hy).of_le (by simp))
      (fun y hy ↦ (hf₀ y hy).of_le (by simp)) hi (hrange hx)).trans hfdiff
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      ((add_le_add hsame (hshift i hi x hx)).trans_eq (by ring))
  · intro i hi x hx
    rw [norm_sub_rev]
    exact (hdg i hi x hx).trans (by nlinarith)

end JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference.PrimitiveDensity
