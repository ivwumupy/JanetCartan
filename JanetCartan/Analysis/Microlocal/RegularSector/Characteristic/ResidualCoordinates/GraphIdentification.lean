module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.SupportedCancellation

/-!
# The supported phase preserves both actual retarded graph operators

The phase constructed on the support of the two matrices leaves both the
solver graph and the full `P W₁` graph unchanged, with the original right
multiplier and both physical masks. Differentiation cannot create support
outside the correction's topological support: this is proved using zero
germs. Equality of bounded operators also preserves their literal adjoints.
Consumer: `CompleteResidual.completeResidual_operators_of_graph_regularizations`.
Source: `app:ch_regular_base:eq:fixed-time-representation` and
`app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification AmplitudeBounds
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d n : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "T" => TwoTimePoint (Euclidean d)
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

/-- The full physical derivative cannot leave the topological support of
its two-time amplitude. Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem twoTimePhysicalApply_eq_zero_off_support
    (A : E → Fin (d + 1) → Mat) (B : E → Mat) (F : T → Mat)
    (t s : ℝ) (y η : Euclidean d) (hp : (t, (s, (y, η))) ∉ tsupport F) :
    twoTimePhysicalApply A B (curryCharacteristicMatrix F) t s y η = 0 := by
  let x := timeSpacePoint t y
  have hsl : ContinuousAt (fun z : E ↦ (z 0, (s, (spatialPart z, η)))) x :=
    (contDiff_physicalSlice (coordinateSplit (0 : Fin (d + 1))) s η).continuous.continuousAt
  have hz : (fun z : E ↦ F (z 0, (s, (spatialPart z, η)))) =ᶠ[𝓝 x] 0 := by
    have he := (notMem_tsupport_iff_eventuallyEq.mp hp)
    have hpoint : (x 0, (s, (spatialPart x, η))) = (t, (s, (y, η))) := by simp [x]
    rw [← hpoint] at he
    exact he.comp_tendsto hsl
  have he : (fun z : E ↦ curryCharacteristicMatrix F (z 0) s (spatialPart z) η) =ᶠ[𝓝 x]
      fun z ↦ (0 : ℂ) • curryCharacteristicMatrix F (z 0) s (spatialPart z) η := by
    filter_upwards [hz] with z hz
    simpa [curryCharacteristicMatrix] using hz
  have hid := twoTimePhysicalApply_eq_of_scaled_germ A B
    (curryCharacteristicMatrix F) (curryCharacteristicMatrix F) 0 s η x he
  simpa [x] using hid

/-- The same auxiliary phase preserves the exact two graph operators used
by the residual: the solver amplitude and its differentiated correction.
`hG` is the output of `exists_smooth_supported_conic_cancellation` for the
literal supported matrices. The physical source and output masks and the
original multiplier are arbitrary and unchanged.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem elapsedGraphs_eq_of_supported_phase
    (A : E → Fin (d + 1) → Mat) (B : E → Mat)
    (F₀ F₁ : T → Mat) (Ψ G : T → ℝ)
    (hG : ∀ p ∈ tsupport F₀ ∪ tsupport F₁, G =ᶠ[𝓝 p] Ψ)
    (χout χsource β : E → ℂ) (r : ℝ) :
    let W₀ := curryCharacteristicMatrix F₀
    let W₁ := curryCharacteristicMatrix F₁
    elapsedGraph (fun t s y η ↦ G (t, (s, (y, η)))) (W₀ + W₁) χout χsource β r =
      elapsedGraph (fun t s y η ↦ Ψ (t, (s, (y, η)))) (W₀ + W₁) χout χsource β r ∧
    elapsedGraph (fun t s y η ↦ G (t, (s, (y, η)))) (twoTimePhysicalApply A B W₁)
      χout χsource β r =
      elapsedGraph (fun t s y η ↦ Ψ (t, (s, (y, η)))) (twoTimePhysicalApply A B W₁)
        χout χsource β r := by
  dsimp only
  have hgraph (b : TwoTimeAmplitude d n)
      (hb : ∀ t s y η, (t, (s, (y, η))) ∉ tsupport F₀ ∪ tsupport F₁ → b t s y η = 0) :
      elapsedGraph (fun t s y η ↦ G (t, (s, (y, η)))) b χout χsource β r =
        elapsedGraph (fun t s y η ↦ Ψ (t, (s, (y, η)))) b χout χsource β r := by
    apply FourierIntegral.FullLowBounds.fullGraphOperator_phase_congr
    intro x z ξ hA
    have hp : (x 0, (x 0 - r, (spatialPart x, spatialPart ξ))) ∈ tsupport F₀ ∪ tsupport F₁ := by
      by_contra hn
      exact hA (by simp [elapsedAmplitude, hb _ _ _ _ hn])
    exact congrArg (fun a ↦ (x 0 - r) * ξ 0 + a) ((hG _ hp).eq_of_nhds)
  constructor
  · apply hgraph
    intro t s y η hp
    have h₀ : F₀ (t, (s, (y, η))) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hp (Or.inl h))
    have h₁ : F₁ (t, (s, (y, η))) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hp (Or.inr h))
    simp only [Pi.add_apply, curryCharacteristicMatrix, h₀, h₁, add_zero]
  · apply hgraph
    intro t s y η hp
    exact twoTimePhysicalApply_eq_zero_off_support A B F₁ t s y η (fun h ↦ hp (Or.inr h))

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
