module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterRealization.Expressions

/-!
# Smooth selected kernels from a buffered frequency chart

Only the selected carrier needs phase smoothness in
`app:ch_response:eq:direct-envelope-profile`. Outside its compact support the
amplitude vanishes on an open neighborhood, so the full kernel is smooth
without extending the homogeneous phase across the zero covector.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ResponseTransfer.NearCarrierParameter
open FourierIntegral
variable {d p : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => EuclideanSpace ℝ (Fin p)
local notation "Z" => JointAmplitudePoint d p

/-- A smooth compact selector permits a factor defined smoothly only on a
buffered frequency chart. The product is smooth on the entire parameter
neighborhood. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem contDiffOn_selectedProduct
    {U : Set P} (hU : IsOpen U) {F V : Set E} (hF : IsClosed F) (hV : IsOpen V)
    (hFV : F ⊆ V) {b Ω : Z → ℂ}
    (hb : ContDiffOn ℝ ∞ b ((U ×ˢ univ) ×ˢ univ))
    (hb0 : ∀ c ∈ U, ∀ z δ, δ ∉ F → b ((c, z), δ) = 0)
    (hΩ : ContDiffOn ℝ ∞ Ω ((U ×ˢ univ) ×ˢ V)) :
    ContDiffOn ℝ ∞ (fun z ↦ Ω z * b z) ((U ×ˢ univ) ×ˢ univ) := by
  intro z hz
  by_cases hv : z.2 ∈ V
  · exact ((hΩ.contDiffAt (((hU.prod isOpen_univ).prod hV).mem_nhds ⟨hz.1, hv⟩)).mul
      (hb.contDiffAt (((hU.prod isOpen_univ).prod isOpen_univ).mem_nhds hz))).contDiffWithinAt
  · have he : (fun z ↦ Ω z * b z) =ᶠ[𝓝 z] (fun _ ↦ (0 : ℂ)) := by
      filter_upwards [((hU.prod isOpen_univ).prod hF.isOpen_compl).mem_nhds
        (show z ∈ (U ×ˢ univ) ×ˢ Fᶜ from ⟨hz.1, fun h ↦ hv (hFV h)⟩)] with w hw
      rw [hb0 w.1.1 hw.1.1 w.1.2 w.2 hw.2, mul_zero]
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt

/-- Joint smoothness of the selected forward kernel from phase jets on the
buffer and smooth full-amplitude jets. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem contDiffOn_forwardScalarKernel_of_chart
    {U : Set P} (hU : IsOpen U) {X Y F V : Set E}
    (hF : IsClosed F) (hV : IsOpen V) (hFV : F ⊆ V)
    {S : E → E → ℝ} {ζ : P → E} {ρ : ℝ}
    (hΦ : ContDiffOn ℝ ∞ (fun z : (P × E) × E ↦
      phaseIncrement S (ζ z.1.1) ρ z.1.2 z.2) ((U ×ˢ univ) ×ˢ V))
    {b : Z → ℂ} (hb : ParameterAmplitudeAdmissible U X Y F b) :
    ContDiffOn ℝ ∞ (fun z : Z ↦
      forwardScalarKernel S ζ ρ (fun c w δ ↦ b ((c, w), δ)) z.1.1 z.1.2 z.2)
        ((U ×ˢ univ) ×ˢ univ) := by
  apply contDiffOn_selectedProduct hU hF hV hFV hb.1 hb.2.2
  apply (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn _)).cexp
  exact (hΦ.comp
    ((contDiff_fst.fst.prodMk contDiff_fst.snd.fst).prodMk contDiff_snd).contDiffOn
    (fun z hz ↦ ⟨⟨hz.1.1, mem_univ _⟩, hz.2⟩)).sub
      (contDiff_fst.snd.snd.inner ℝ contDiff_snd).contDiffOn

/-- Joint smoothness of the selected reverse kernel on the same local chart.
No global smoothness of the homogeneous phase is assumed. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem contDiffOn_reverseScalarKernel_of_chart
    {U : Set P} (hU : IsOpen U) {X Y F V : Set E}
    (hF : IsClosed F) (hV : IsOpen V) (hFV : F ⊆ V)
    {S : E → E → ℝ} {ζ : P → E} {ρ : ℝ}
    (hΦ : ContDiffOn ℝ ∞ (fun z : (P × E) × E ↦
      phaseIncrement S (ζ z.1.1) ρ z.1.2 z.2) ((U ×ˢ univ) ×ˢ V))
    {b : Z → ℂ} (hb : ParameterAmplitudeAdmissible U X Y F b) :
    ContDiffOn ℝ ∞ (fun z : Z ↦
      reverseScalarKernel S ζ ρ (fun c w δ ↦ b ((c, w), δ)) z.1.1 z.1.2 z.2)
        ((U ×ˢ univ) ×ˢ univ) := by
  apply contDiffOn_selectedProduct hU hF hV hFV hb.1 hb.2.2
  apply (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn _)).cexp
  exact (contDiff_fst.snd.fst.inner ℝ contDiff_snd).contDiffOn.sub
    (hΦ.comp ((contDiff_fst.fst.prodMk contDiff_fst.snd.snd).prodMk contDiff_snd).contDiffOn
      (fun z hz ↦ ⟨⟨hz.1.1, mem_univ _⟩, hz.2⟩))

end JanetCartan.ResponseTransfer.NearCarrierParameter
