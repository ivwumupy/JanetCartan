module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.Composition.SectionFlow

/-!
# Composition continuity on fixed buffered domains

For `app:lem:common-hamilton-phase`, composition is jointly continuous in the
finite-order `cNorm` seminorms. `exists_cNorm_comp_sub_lt_on_open` is the open
neighborhood interface; `CompositionContinuity.exists_cNorm_comp_sub_lt` uses
pointwise local regularity instead. Both retain explicit range containment.
They apply in particular to compact closed balls inside open buffered balls.

`SectionEnergy.exists_cNorm_sectionFlowState_sub_lt` specializes this to the
actual section flow, with seminorm control of the root on its parameter set
and of the flow on its state/time set. It does not assert the separate root
and ODE stability estimates needed to instantiate those inputs.
-/

@[expose] public noncomputable section

namespace JanetCartan.HamiltonPhase.CompositionContinuity

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `app:lem:common-hamilton-phase`: the buffered-domain interface for joint
composition continuity. Compact inner sets lie in fixed open neighborhoods;
the constants are chosen before the perturbations. Only order `m` regularity
and order `m` difference seminorms are used. -/
theorem exists_cNorm_comp_sub_lt_on_open {K O : Set E} {L V : Set F}
    (hK : IsCompact K) (hL : IsCompact L) (hO : IsOpen O) (hV : IsOpen V)
    (hKO : K ⊆ O) (hLV : L ⊆ V) {m : ℕ} {f₀ : F → G} {g₀ : E → F}
    (hf₀ : ContDiffOn ℝ m f₀ V) (hg₀ : ContDiffOn ℝ m g₀ O)
    (hrange₀ : Set.MapsTo g₀ K L) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (f : F → G) (g : E → F),
      ContDiffOn ℝ m f V → ContDiffOn ℝ m g O → Set.MapsTo g K L →
      cNorm L m (f - f₀) < δ → cNorm K m (g - g₀) < δ →
      cNorm K m (f ∘ g - f₀ ∘ g₀) < ε := by
  obtain ⟨δ, hδ, h⟩ := exists_cNorm_comp_sub_lt hK hL
    (fun y hy ↦ hf₀.contDiffAt (hV.mem_nhds (hLV hy)))
    (fun x hx ↦ hg₀.contDiffAt (hO.mem_nhds (hKO hx))) hrange₀ hε
  exact ⟨δ, hδ, fun f g hf hg ↦ h f g
    (fun y hy ↦ hf.contDiffAt (hV.mem_nhds (hLV hy)))
    (fun x hx ↦ hg.contDiffAt (hO.mem_nhds (hKO hx)))⟩

end JanetCartan.HamiltonPhase.CompositionContinuity
