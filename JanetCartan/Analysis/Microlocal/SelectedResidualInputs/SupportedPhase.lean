module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.GraphIdentification
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.OperatorIdentity

/-!
# Supported phase equality for the full direct residual

The retained cancellation germ applies to the solver and to its full physical
derivative, since differentiation cannot enlarge the amplitude's closed support.
This is the pointwise equality needed to transfer the literal regularizations.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedResidualInputs
open RegularSector.Characteristic RegularSector.Characteristic.AmplitudeBounds
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.ResidualCoordinates
open CharacteristicTransport.CompleteResidual
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "T" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- The retained supported cancellation germ gives phase equality on both
original direct amplitudes, including the full `B` in `PW₁`. Consumer:
`ResponseTransfer.RetainedFactors.CappedGraphRealizations.of_supported_phase_eq`,
applied to the canonical frequency regularizations of
`SelectedLocalization.exists_selected_common_graph_regularizations`, which
must use the same conic phase as the primitive profiles
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem directRetardedAmplitudes_phase_eq_of_supported_germ
    (A : E → Fin (d+1) → Mat) (B : E → Mat)
    (F₀ F₁ : T → Mat) (Ψ G : T → ℝ)
    (hG : ∀ v ∈ tsupport F₀ ∪ tsupport F₁, G =ᶠ[𝓝 v] Ψ)
    (χout χsource β : E → ℂ) :
    let b := directRetardedAmplitudes A B
      (curryCharacteristicMatrix F₀) (curryCharacteristicMatrix F₁)
    ∀ k r x y ξ, elapsedAmplitude (b k) χout χsource β r x y ξ ≠ 0 →
      elapsedPhase (fun t s u η ↦ G (t, (s, (u, η)))) r x ξ =
        elapsedPhase (fun t s u η ↦ Ψ (t, (s, (u, η)))) r x ξ := by
  intro b k r x y ξ hnonzero
  have hzero k t s u η (hv : (t, (s, (u, η))) ∉ tsupport F₀ ∪ tsupport F₁) :
      b k t s u η = 0 := by
    cases k
    · have h₀ : F₀ (t, (s, (u, η))) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hv (Or.inl h))
      have h₁ : F₁ (t, (s, (u, η))) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hv (Or.inr h))
      simp only [b, directRetardedAmplitudes,
        Pi.add_apply, curryCharacteristicMatrix, h₀, h₁, add_zero]
    · exact twoTimePhysicalApply_eq_zero_off_support A B F₁ t s u η
        (fun h ↦ hv (Or.inr h))
  have hv : (x 0, (x 0-r, (spatialPart x, spatialPart ξ))) ∈ tsupport F₀ ∪ tsupport F₁ := by
    by_contra h
    exact hnonzero (by simp [elapsedAmplitude, hzero k _ _ _ _ h])
  exact congrArg (fun a : ℝ ↦ (x 0-r)*ξ 0+a) ((hG _ hv).eq_of_nhds)

end JanetCartan.ArbitraryAccuracy.SelectedResidualInputs
