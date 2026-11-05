module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SourceParameterCoordinates.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.Basic

/-!
# Global joint regularity of the original localized physical source

The original parameter cutoff has closed support inside the phase domain.
Outside that support the physical source is zero. Thus local phase
regularity and the original source support give a globally jointly smooth
compact spatial source, without imposing global regularity on a phase
extension outside its original parameter domain.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace JanetCartan.FixedDomainInverse

open ResponseTransfer ResponseTransfer.SourceNegative

variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CF" => EuclideanSpace ℂ (Fin q)

/-- The original parameter-localized physical source is jointly smooth on
all parameters and retains the original compact spatial support. Apply
with `Z = tsupport θ`, where the source producer's parameter cutoff `θ`
was fixed before histories. This supplies the graph-test family used by
the SAME complete solver's joint realization
(`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiff_original_product_physical_source_of_parameter_support
    {V Z : Set Par} {Ω X : Set E} (hV : IsOpen V) (hΩ : IsOpen Ω)
    (hZ : IsClosed Z) (hZV : Z ⊆ V) (hX : IsCompact X) (hXΩ : X ⊆ Ω)
    {φ : Par → E → ℝ} (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ Ω))
    {f : Par → E → CF} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (f c) ⊆ X) (hzero : ∀ c, c ∉ Z → f c = 0)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (ρ : ℝ) :
    let g := fun c ↦ modulatedSource χ (φ c) (f c) ρ
    ContDiff ℝ ∞ (fun z : E × Par ↦ g z.2 z.1) ∧
      (∀ c, tsupport (g c) ⊆ X) := by
  intro g
  have hg : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ) :=
    (hχ.comp_contDiffOn contDiffOn_snd).smul
      (contDiffOn_productParameterSourceFunction_localized hV hΩ hX.isClosed hXΩ ρ hφ hf hs)
  have hglobal : ContDiff ℝ ∞ (Function.uncurry g) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z.1 ∈ V
    · exact (hg z ⟨hz, mem_univ _⟩).contDiffAt
        ((hV.prod isOpen_univ).mem_nhds ⟨hz, mem_univ _⟩)
    · have hzZ : z.1 ∉ Z := fun h ↦ hz (hZV h)
      have he : Function.uncurry g =ᶠ[nhds z] (fun _ ↦ 0) := by
        filter_upwards [(hZ.isOpen_compl.prod isOpen_univ).mem_nhds ⟨hzZ, mem_univ z.2⟩]
          with w hw
        simp only [Function.uncurry, g, modulatedSource, hzero w.1 hw.1, Pi.zero_apply, smul_zero]
      exact contDiffAt_const.congr_of_eventuallyEq he
  refine ⟨hglobal.comp (contDiff_snd.prodMk contDiff_fst), ?_⟩
  intro c
  by_cases hc : c ∈ V
  · exact (tsupport_smul_subset_right _ _).trans
      ((tsupport_smul_subset_right _ _).trans (hs c hc))
  · have he : g c = 0 := by
      funext x
      simp only [g, modulatedSource, hzero c (fun h ↦ hc (hZV h)), Pi.zero_apply, smul_zero]
    rw [he, tsupport_zero]
    exact empty_subset X

end JanetCartan.FixedDomainInverse
