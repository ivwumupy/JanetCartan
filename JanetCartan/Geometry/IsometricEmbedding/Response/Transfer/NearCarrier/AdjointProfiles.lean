module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.RawPrimitiveFields
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.FullLow.Identification
public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.Masks

/-!
# Raw profiles of the literal adjoint amplitude

Conjugate transpose and exchange of physical positions preserve the normalized
jet norms and the complete selected support. The selector is conjugated too.
Consumers: the adjoint spatial and parameter estimates in
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.NearCarrierAssembly
open FourierIntegral GradedPrimitives NearCarrierFullLow
variable {n r p : ℕ}
local notation "E" => Euclidean n
local notation "P" => Euclidean p
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local instance adjointProfileMatrixTopology : TopologicalSpace Mat :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- Exchange the two physical positions, preserving the normalized covector
and the product norm. Source: `app:ch_response:eq:direct-envelope-profile`. -/
def fullAmplitudePositionSwap : (E × E × E) ≃ₗᵢ[ℝ] (E × E × E) where
  toFun z := (z.2.1, z.1, z.2.2)
  invFun z := (z.2.1, z.1, z.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' z := by simp only [Prod.norm_def]; exact max_left_comm _ _ _

/-- The literal adjoint keeps every normalized full-amplitude jet, with the
physical evaluation point exchanged. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_jet_normalizedFullAmplitude_exchangedAdjoint
    (A : FullAmplitude n r) (ρ : ℝ) (k : ℕ) (z : E × E × E) :
    ‖iteratedFDeriv ℝ k (normalizedFullAmplitude (exchangedAdjointAmplitude A) ρ) z‖ =
      ‖iteratedFDeriv ℝ k (normalizedFullAmplitude A ρ) (z.2.1, z.1, z.2.2)‖ := by
  change ‖iteratedFDeriv ℝ k
    (fun z ↦ ((normalizedFullAmplitude A ρ) (fullAmplitudePositionSwap z)).conjTranspose) z‖ = _
  rw [norm_iteratedFDeriv_transport_conjTranspose]
  exact fullAmplitudePositionSwap.norm_iteratedFDeriv_comp_right (normalizedFullAmplitude A ρ) z k

/-- Smoothness of the raw adjoint symbol on the same physical buffer.
The two positions are exchanged before taking conjugate transpose.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem contDiffOn_normalizedFullAmplitude_exchangedAdjoint
    (A : FullAmplitude n r) (ρ : ℝ) {X D : Set E}
    (hA : ContDiffOn ℝ ∞ (normalizedFullAmplitude A ρ) (X ×ˢ X ×ˢ D)) :
    ContDiffOn ℝ ∞ (normalizedFullAmplitude (exchangedAdjointAmplitude A) ρ) (X ×ˢ X ×ˢ D) :=
  (starL ℝ : Mat ≃L[ℝ] Mat).contDiff.comp_contDiffOn
    (hA.comp fullAmplitudePositionSwap.contDiff.contDiffOn
      (fun _ hz ↦ ⟨hz.2.1, hz.1, hz.2.2⟩))

/-- Conjugating the selector spends no derivative reserve. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_jet_conjugateSelector (q : P × E → ℂ) (k : ℕ) (z : P × E) :
    ‖iteratedFDeriv ℝ k (fun z ↦ star (q z)) z‖ = ‖iteratedFDeriv ℝ k q z‖ :=
  Complex.conjLIE.norm_iteratedFDeriv_comp_left q z k

/-- Every original selected mask is retained by the literal adjoint. The
compact physical box may be common, while the two actual factors of the
amplitude remain distinct. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem tsupport_normalizedParameterAmplitude_exchangedAdjoint
    (A : FullAmplitude n r) (q : P × E → ℂ) (ζ : P → E) (ρ : ℝ)
    {X F : Set E} {C : Set P}
    (hs : tsupport (normalizedParameterAmplitude A q ζ ρ) ⊆ (X ×ˢ X ×ˢ F) ×ˢ C) :
    tsupport (normalizedParameterAmplitude (exchangedAdjointAmplitude A)
      (fun z ↦ star (q z)) ζ ρ) ⊆ (X ×ˢ X ×ˢ F) ×ˢ C := by
  let σ : ((E × E × E) × P) →L[ℝ] ((E × E × E) × P) :=
    fullAmplitudePositionSwap.toContinuousLinearEquiv.toContinuousLinearMap.prodMap
      (ContinuousLinearMap.id ℝ P)
  have he : normalizedParameterAmplitude (exchangedAdjointAmplitude A)
      (fun z ↦ star (q z)) ζ ρ =
      (starL ℝ : Mat ≃L[ℝ] Mat) ∘ normalizedParameterAmplitude A q ζ ρ ∘ σ := by
    funext z
    simp [normalizedParameterAmplitude, exchangedAdjointAmplitude, σ,
      fullAmplitudePositionSwap, Function.comp_def, Matrix.star_eq_conjTranspose]
  rw [he]
  have h := ((tsupport_comp_subset (map_zero (starL ℝ : Mat ≃L[ℝ] Mat)) _).trans
    (tsupport_comp_subset_preimage _ σ.continuous)).trans (preimage_mono hs)
  intro z hz
  have hz' := h hz
  exact ⟨⟨hz'.1.2.1, hz'.1.1, hz'.1.2.2⟩, hz'.2⟩

end JanetCartan.ResponseTransfer.NearCarrierAssembly
