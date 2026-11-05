module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.PrimitiveNorms
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.Composition.Continuity

/-!
# Quantitative composition for carrier amplitude differences

The consumer is the primitive coefficient substitution in
`app:ch_osc:prop:osc-normal`, Step 4', and
`app:ch_background:eq:bg-full-complex-amplitude`. Common finite bounds and
primitive differences control the composition at two different inverse points.
The extra derivative bounds the displacement of the reference outer jets.
This module neither assumes nor asserts a bound for the full amplitude.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff
namespace JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference
open ContinuumNormalReduction.TransportSymbol HamiltonPhase.CompositionContinuity
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Quantitative substitution on fixed compact domains. The outer domain is
convex so its next jet controls displacement between the two genuine inverse
points. The constant uses only the fixed order and common bounds, and the
smallness input is on the original two functions. Consumer: substitution of
each primitive coefficient in the full transport density. Source:
`app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem cNorm_comp_sub_le_common_bounds
    {K : Set E} {L : Set F} (hK : IsCompact K) (hL : IsCompact L)
    (hconv : Convex ℝ L) (s : ℕ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {f f₀ : F → G} {g g₀ : E → F} {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ y ∈ L, ContDiffAt ℝ ∞ f y)
    (hf₀ : ∀ y ∈ L, ContDiffAt ℝ ∞ f₀ y)
    (hg : ∀ x ∈ K, ContDiffAt ℝ ∞ g x)
    (hg₀ : ∀ x ∈ K, ContDiffAt ℝ ∞ g₀ x)
    (hrange : MapsTo g K L) (hrange₀ : MapsTo g₀ K L)
    (houter : cNorm L (s + 1) f₀ ≤ A)
    (hinner : cNorm K s g ≤ B) (hinner₀ : cNorm K s g₀ ≤ B)
    (hfdiff : cNorm L s (f - f₀) ≤ ε)
    (hgdiff : cNorm K s (g - g₀) ≤ ε) :
    cNorm K s (f ∘ g - f₀ ∘ g₀) ≤
      (jetDifferenceConstant s A B * (1 + A)) * ε := by
  have hdg (i : ℕ) (hi : i ≤ s) (x : E) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g₀ x‖ ≤ ε :=
    (norm_iteratedFDeriv_sub_le_cNorm hK
      (fun x hx ↦ (hg x hx).of_le (by simp))
      (fun x hx ↦ (hg₀ x hx).of_le (by simp)) hi hx).trans hgdiff
  have hv (x : E) (hx : x ∈ K) : ‖g x - g₀ x‖ ≤ ε := by
    have h := hdg 0 (Nat.zero_le _) x hx
    rw [← iteratedFDeriv_sub_apply ((hg x hx).of_le (by simp))
      ((hg₀ x hx).of_le (by simp)), norm_iteratedFDeriv_zero] at h
    exact h
  have hshift (i : ℕ) (hi : i ≤ s) (x : E) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ i f₀ (g x) - iteratedFDeriv ℝ i f₀ (g₀ x)‖ ≤ A * ε := by
    apply le_trans (hconv.norm_image_sub_le_of_norm_fderiv_le
      (fun y hy ↦ ((hf₀ y hy).iteratedFDeriv_right (m := 1) (by simp)).differentiableAt
        (by simp)) (C := A) ?_ (hrange₀ hx) (hrange hx))
      (mul_le_mul_of_nonneg_left (hv x hx) hA)
    intro y hy
    rw [norm_fderiv_iteratedFDeriv]
    exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hL
      (fun y hy ↦ (hf₀ y hy).of_le (by simp)) hy
      (Nat.add_le_add_right hi 1)).trans houter
  have hb := cNorm_comp_sub_le_of_jet_bounds (m := s)
    (fun x hx ↦ (hf _ (hrange hx)).of_le (by simp))
    (fun x hx ↦ (hf₀ _ (hrange₀ hx)).of_le (by simp))
    (fun x hx ↦ (hg x hx).of_le (by simp))
    (fun x hx ↦ (hg₀ x hx).of_le (by simp)) hA hB
    (show 0 ≤ (1 + A) * ε by positivity) ?_ ?_ ?_ ?_
  · exact hb.trans_eq (by ring)
  · intro i hi x hx
    exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hL
      (fun y hy ↦ (hf₀ y hy).of_le (by simp)) (hrange₀ hx)
      (hi.trans (Nat.le_succ _))).trans houter
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

/-- Specialization to the existing primitive coefficient norm domains. The
input differences are measured on `D.carrier`, before inverse substitution;
no norm of a composed coefficient is assumed. Consumer: the measurement,
angular, high-mask, normal and reduced-covector factors of
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem PrimitiveNormChart.cNorm_comp_sub_le
    [FiniteDimensional ℝ F] (D : PrimitiveNormChart F)
    {K : Set E} (hK : IsCompact K) (s : ℕ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {f f₀ : F → G} {g g₀ : E → F} {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ContDiffOn ℝ ∞ f D.region) (hf₀ : ContDiffOn ℝ ∞ f₀ D.region)
    (hg : ∀ x ∈ K, ContDiffAt ℝ ∞ g x)
    (hg₀ : ∀ x ∈ K, ContDiffAt ℝ ∞ g₀ x)
    (hrange : MapsTo g K D.carrier) (hrange₀ : MapsTo g₀ K D.carrier)
    (houter : cNorm D.carrier (s + 1) f₀ ≤ A)
    (hinner : cNorm K s g ≤ B) (hinner₀ : cNorm K s g₀ ≤ B)
    (hfdiff : cNorm D.carrier s (f - f₀) ≤ ε)
    (hgdiff : cNorm K s (g - g₀) ≤ ε) :
    cNorm K s (f ∘ g - f₀ ∘ g₀) ≤
      (jetDifferenceConstant s A B * (1 + A)) * ε := by
  exact cNorm_comp_sub_le_common_bounds hK (isCompact_closedBall _ _)
    (convex_closedBall _ _) s hA hB hε
    (fun y hy ↦ hf.contDiffAt (D.isOpen_region.mem_nhds (D.ball_subset hy)))
    (fun y hy ↦ hf₀.contDiffAt (D.isOpen_region.mem_nhds (D.ball_subset hy)))
    hg hg₀ hrange hrange₀ houter hinner hinner₀ hfdiff hgdiff

end JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference
