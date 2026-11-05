module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.Composition.Continuity
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SymbolStability
public import JanetCartan.Analysis.ContDiff.Norm.Composition

/-!
# Finite-order continuity of root-initialized flow evaluation

For `app:lem:common-hamilton-phase`, root and flow seminorm estimates imply the
section-flow estimate on fixed domains. The actual root and ODE estimates are
inputs supplied by their respective constructions, not asserted here.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.HamiltonPhase

open CompositionContinuity

variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance : NormedSpace ℝ U := InnerProductSpace.toNormedSpace

namespace SectionEnergy

/-- `app:lem:common-hamilton-phase`: root seminorm control gives control of the
initial-state/time insertion, at exactly the same order. The constant is fixed
before choosing either root. Consumed by `exists_cNorm_sectionFlowState_sub_lt`. -/
theorem exists_cNorm_sectionFlowInput_sub_le (j : U →ₗᵢ[ℝ] E) (ν : E)
    {K : Set (ℝ × InitialData U)} {P : Set (InitialData U)}
    (hK : IsCompact K) (hP : IsCompact P) (hKP : Set.MapsTo Prod.snd K P) (m : ℕ) :
    ∃ C > 0, ∀ (g g₀ : InitialData U → ℝ),
      (∀ s ∈ P, ContDiffAt ℝ m g s) → (∀ s ∈ P, ContDiffAt ℝ m g₀ s) →
      cNorm K m (sectionFlowInput j ν g - sectionFlowInput j ν g₀) ≤
        C * cNorm P m (g - g₀) := by
  let V : ℝ →L[ℝ] ((E × E) × ℝ) :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight ((0, ν), 0)
  let π : (ℝ × InitialData U) → InitialData U := Prod.snd
  let D := compositionMultiplicity m * (1 + cNorm K m π) ^ m
  have hD : 0 ≤ D := by
    dsimp [D, compositionMultiplicity]
    exact mul_nonneg (Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _))
      (pow_nonneg (by linarith [cNorm_nonneg K m π]) _)
  let C := (m + 1 : ℝ) * ‖V‖ * D
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by positivity) (norm_nonneg _)) hD
  refine ⟨C + 1, by positivity, ?_⟩
  intro g g₀ hg hg₀
  let u := (g - g₀) ∘ π
  have hu : ∀ x ∈ K, ContDiffAt ℝ m u x := fun x hx ↦
    ((hg _ (hKP hx)).sub (hg₀ _ (hKP hx))).comp x contDiff_snd.contDiffAt
  have heq : sectionFlowInput j ν g - sectionFlowInput j ν g₀ = V ∘ u := by
    funext q
    simp [sectionFlowInput, transverseSectionState, V, u, π, sub_smul]
  have huB : cNorm K m u ≤ D * cNorm P m (g - g₀) := by
    have hp : ContDiff ℝ m π := contDiff_snd
    have hh := cNorm_comp_le_polynomial (s := K) (r := m) (f := π) (g := g - g₀)
      (fun _ _ ↦ hp.contDiffAt)
      (fun x hx ↦ (hg _ (hKP hx)).sub (hg₀ _ (hKP hx)))
      (fun i hi ↦ bddAbove_norm_iteratedFDeriv hK hp hi) (cNorm_nonneg P m (g - g₀))
      (fun i hi x hx ↦ norm_iteratedFDeriv_le_cNorm_of_contDiffAt hP
        (fun s hs ↦ (hg s hs).sub (hg₀ s hs)) (hKP hx) hi)
    simpa only [D, u, mul_right_comm] using hh
  have hv : cNorm K m (V ∘ u) ≤ (m + 1 : ℝ) * (‖V‖ * cNorm K m u) := by
    refine (cNorm_le_sum_of_bounds (C := fun _ ↦ ‖V‖ * cNorm K m u)
      (fun _ _ ↦ mul_nonneg (norm_nonneg _) (cNorm_nonneg _ _ _)) ?_).trans_eq ?_
    · intro i hi x hx
      rw [V.iteratedFDeriv_comp_left (hu x hx) (by exact_mod_cast hi)]
      exact (V.norm_compContinuousMultilinearMap_le _).trans
        (mul_le_mul_of_nonneg_left
          (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hu hx hi) (norm_nonneg _))
    · simp
  rw [heq]
  calc
    _ ≤ (m + 1 : ℝ) * (‖V‖ * cNorm K m u) := hv
    _ ≤ (m + 1 : ℝ) * (‖V‖ * (D * cNorm P m (g - g₀))) := by gcongr
    _ = C * cNorm P m (g - g₀) := by dsimp [C]; ring
    _ ≤ (C + 1) * cNorm P m (g - g₀) :=
      mul_le_mul_of_nonneg_right (by linarith) (cNorm_nonneg _ _ _)

/-- `app:lem:common-hamilton-phase`: finite-order continuity of the actual
root-initialized flow. Root and flow seminorms are the only smallness inputs.
Range containment in the fixed compact flow domain remains explicit. The root
and ODE continuity producers must instantiate these inputs separately. -/
theorem exists_cNorm_sectionFlowState_sub_lt (j : U →ₗᵢ[ℝ] E) (ν : E)
    {K : Set (ℝ × InitialData U)} {P : Set (InitialData U)}
    {L : Set ((E × E) × ℝ)} (hK : IsCompact K) (hP : IsCompact P) (hL : IsCompact L)
    (hKP : Set.MapsTo Prod.snd K P) {m : ℕ}
    {g₀ : InitialData U → ℝ} {Ψ₀ : (E × E) × ℝ → E × E}
    (hg₀ : ∀ s ∈ P, ContDiffAt ℝ m g₀ s)
    (hΨ₀ : ∀ z ∈ L, ContDiffAt ℝ m Ψ₀ z)
    (hrange₀ : Set.MapsTo (sectionFlowInput j ν g₀) K L) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (g : InitialData U → ℝ) (Ψ : (E × E) × ℝ → E × E),
      (∀ s ∈ P, ContDiffAt ℝ m g s) → (∀ z ∈ L, ContDiffAt ℝ m Ψ z) →
      Set.MapsTo (sectionFlowInput j ν g) K L →
      cNorm P m (g - g₀) < δ → cNorm L m (Ψ - Ψ₀) < δ →
      cNorm K m (sectionFlowState j ν g Ψ - sectionFlowState j ν g₀ Ψ₀) < ε := by
  have hinput : ∀ g : InitialData U → ℝ, (∀ s ∈ P, ContDiffAt ℝ m g s) →
      ∀ q ∈ K, ContDiffAt ℝ m (sectionFlowInput j ν g) q := by
    intro g hg q hq
    exact (((contDiff_transverseSectionState j ν).contDiffAt.of_le (by simp)).comp q
      (contDiff_snd.contDiffAt.prodMk
        ((hg _ (hKP hq)).comp q contDiff_snd.contDiffAt))).prodMk contDiff_fst.contDiffAt
  obtain ⟨d, hd, hcomp⟩ := exists_cNorm_comp_sub_lt hK hL hΨ₀ (hinput g₀ hg₀) hrange₀ hε
  obtain ⟨C, hC, hroot⟩ := exists_cNorm_sectionFlowInput_sub_le j ν hK hP hKP m
  refine ⟨min d (d / C), lt_min hd (div_pos hd hC), ?_⟩
  intro g Ψ hg hΨ hrange hsmallg hsmallΨ
  apply hcomp Ψ (sectionFlowInput j ν g) hΨ (hinput g hg) hrange
    (hsmallΨ.trans_le (min_le_left _ _))
  apply (hroot g g₀ hg hg₀).trans_lt
  exact (mul_lt_mul_of_pos_left (hsmallg.trans_le (min_le_right _ _)) hC).trans_eq
    (mul_div_cancel₀ d hC.ne')

end SectionEnergy

end JanetCartan.HamiltonPhase
