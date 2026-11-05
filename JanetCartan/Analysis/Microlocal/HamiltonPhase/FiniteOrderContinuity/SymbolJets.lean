module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SymbolStability

/-!
# Symbol seminorm inputs for finite-order phase continuity

These are the inputs to the differentiated root and ODE comparisons in
`app:lem:common-hamilton-phase`. The compact state set can be the fixed
`closedBall (transverseSectionState j ν (s₀, τ₀)) R` used by
`exists_common_buffered_symbol_charts`, inside a normalized covector patch.
The Hamilton field costs exactly one symbol derivative; the section energy
pullback costs none. The separate fixed `C³` neighborhood is still needed to
construct the common domains. No higher-order flow comparison is assumed here.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.HamiltonPhase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Scalar jet control at every finite order, for the differentiated root and
Hamilton equations of `app:lem:common-hamilton-phase`. -/
theorem norm_symbol_jet_sub_le_cNorm
    (H H₀ : HomogeneousSymbol E) {D K : Set (E × E)} (hD : IsOpen D)
    {m n : ℕ} (hH : ContDiffOn ℝ m H.h D) (hH₀ : ContDiffOn ℝ m H₀.h D)
    (hK : IsCompact K) (hKD : K ⊆ D) (hn : n ≤ m)
    {z : E × E} (hz : z ∈ K) :
    ‖iteratedFDeriv ℝ n (fun w ↦ H.h w - H₀.h w) z‖ ≤
      cNorm K m (fun w ↦ H.h w - H₀.h w) :=
  norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
    (fun _ hw ↦ (hH.sub hH₀).contDiffAt (hD.mem_nhds (hKD hw))) hz hn

/-- The actual Hamilton field has `C^m` perturbation bounded by the scalar
`C^(m+1)` perturbation on the same normalized state domain
(`app:lem:common-hamilton-phase`). This is the input to finite-order ODE stability.
-/
theorem cNorm_vectorField_sub_le [CompleteSpace E]
    (H H₀ : HomogeneousSymbol E) {D K : Set (E × E)} (hD : IsOpen D)
    (hDH : D ⊆ H.domain) (hDH₀ : D ⊆ H₀.domain)
    (m : ℕ) (hH : ContDiffOn ℝ (m + 1) H.h D)
    (hH₀ : ContDiffOn ℝ (m + 1) H₀.h D)
    (hK : IsCompact K) (hKD : K ⊆ D) :
    cNorm K m (fun w ↦ H.vectorField w - H₀.vectorField w) ≤
      (m + 1 : ℝ) * cNorm K (m + 1) (fun w ↦ H.h w - H₀.h w) := by
  apply (cNorm_le_sum_of_bounds
    (C := fun _ ↦ cNorm K (m + 1) (fun w ↦ H.h w - H₀.h w))
    (fun _ _ ↦ cNorm_nonneg _ _ _) ?_).trans_eq
  · simp
  · intro n hn z hz
    have hn' : (n + 1 : ℕ∞ω) ≤ m + 1 := by exact_mod_cast Nat.add_le_add_right hn 1
    exact (norm_iteratedFDeriv_vectorField_sub_le H H₀ hD hDH hDH₀
      (hH.of_le hn') (hH₀.of_le hn') (hKD hz)).trans
      (norm_symbol_jet_sub_le_cNorm H H₀ hD hH hH₀ hK hKD
        (Nat.add_le_add_right hn 1) hz)

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- The energy-equation perturbation at order `m` is bounded by the symbol
perturbation at the same order. The constant depends only on the fixed section
map and compact cylinder, not on the perturbed symbol
(`app:lem:common-hamilton-phase`). The consumer is finite-order root stability.
-/
theorem exists_sectionEnergy_finiteOrder_bound
    (j : U →ₗᵢ[ℝ] E) (ν : E) {K : Set (InitialData U × ℝ)}
    (hK : IsCompact K) (m : ℕ) :
    ∃ B > (0 : ℝ), ∀ (H H₀ : HomogeneousSymbol E) (D L : Set (E × E)),
      IsOpen D → ContDiffOn ℝ m H.h D → ContDiffOn ℝ m H₀.h D →
      IsCompact L → L ⊆ D → MapsTo (transverseSectionState j ν) K L →
      cNorm K m (sectionEnergyEquation H j ν - sectionEnergyEquation H₀ j ν) ≤
        B * cNorm L m (fun z ↦ H.h z - H₀.h z) := by
  let B := compositionMultiplicity m * (1 + cNorm K m (transverseSectionState j ν)) ^ m
  refine ⟨1 + |B|, by positivity, ?_⟩
  intro H H₀ D L hD hH hH₀ hL hLD hmap
  have he : sectionEnergyEquation H j ν - sectionEnergyEquation H₀ j ν =
      (fun z ↦ H.h z - H₀.h z) ∘ transverseSectionState j ν := by
    funext w
    simp only [Pi.sub_apply, sectionEnergyEquation, Function.comp_apply]
    ring
  rw [he]
  have hs : ContDiff ℝ m (transverseSectionState j ν) :=
    (contDiff_transverseSectionState j ν).of_le (by simp)
  have hb := cNorm_comp_le_polynomial (s := K) (r := m)
    (fun _ _ ↦ hs.contDiffAt)
    (fun w hw ↦ (hH.sub hH₀).contDiffAt (hD.mem_nhds (hLD (hmap hw))))
    (fun _ hn ↦ CompositionBounds.bddAbove_derivative_image hK hs hn)
    (cNorm_nonneg L m (fun z ↦ H.h z - H₀.h z))
    (fun n hn w hw ↦ norm_symbol_jet_sub_le_cNorm H H₀ hD hH hH₀ hL hLD hn (hmap hw))
  calc
    _ ≤ B * cNorm L m (fun z ↦ H.h z - H₀.h z) := by
      convert hb using 1
      dsimp [B]
      ring
    _ ≤ (1 + |B|) * cNorm L m (fun z ↦ H.h z - H₀.h z) :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self B]) (cNorm_nonneg _ _ _)

end JanetCartan.HamiltonPhase
