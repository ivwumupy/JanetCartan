module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.TransverseCompatibility

/-!
# Hamilton uniqueness for locally equal symbols

The coefficient extension in `app:ch_regular:eq:coefficient-extension` only
agrees locally with the original symbol. Reinterpret the existing trajectories
using that local equality, then apply the root and ODE uniqueness of
`app:lem:common-hamilton-phase`. No flow, initial root or chart is chosen here.
The consumer is the original-target frame agreement in `LocalFrameAgreement`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology

namespace JanetCartan.ActualCarriers.CurrentFullPhase.LocalFrameAgreement
open HamiltonPhase

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance : NormedSpace ℝ U := InnerProductSpace.toNormedSpace

omit [FiniteDimensional ℝ E] in
private theorem symbol_gradients_eqOn
    {H H' : HomogeneousSymbol E} {D : Set (E × E)} (hD : IsOpen D)
    (hDH : D ⊆ H.domain) (hDH' : D ⊆ H'.domain) (he : EqOn H.h H'.h D) :
    EqOn H.hx H'.hx D ∧ EqOn H.hp H'.hp D := by
  have hd (z) (hz : z ∈ D) :
      hamiltonDifferential (H.hx z) (H.hp z) =
        hamiltonDifferential (H'.hx z) (H'.hp z) :=
    ((H.hasFDerivAt_h z (hDH hz)).congr_of_eventuallyEq
      (eventuallyEq_of_mem (hD.mem_nhds hz) (fun _ hw ↦ (he hw).symm))).unique
        (H'.hasFDerivAt_h z (hDH' hz))
  constructor
  · intro z hz
    apply ext_inner_right ℝ
    intro v
    simpa using congrArg (fun L : E × E →L[ℝ] ℝ ↦ L (v, 0)) (hd z hz)
  · intro z hz
    apply ext_inner_right ℝ
    intro v
    simpa using congrArg (fun L : E × E →L[ℝ] ℝ ↦ L (0, v)) (hd z hz)

/-- Reinterpret the identical trajectory and variations for a symbol agreeing
on their open state neighborhood (`app:lem:common-hamilton-phase`). This is a
concrete relabeling of an existing solution, not an existence interface. -/
private def flowForLocallyEqualSymbol
    {H H' : HomogeneousSymbol E} (Ψ : HamiltonFlow H' U)
    {D : Set (E × E)} (hD : IsOpen D)
    (hDH : D ⊆ H.domain) (hDH' : D ⊆ H'.domain) (he : EqOn H.h H'.h D)
    (hrange : ∀ q ∈ Ψ.time ×ˢ Ψ.parameters, (Ψ.position q, Ψ.momentum q) ∈ D) :
    HamiltonFlow H U := by
  have hg := symbol_gradients_eqOn hD hDH hDH' he
  have hdp : EqOn H.hpDerivative H'.hpDerivative D := by
    intro z hz
    exact ((H.hasFDerivAt_hp z (hDH hz)).congr_of_eventuallyEq
      (eventuallyEq_of_mem (hD.mem_nhds hz) (fun _ hw ↦ (hg.2 hw).symm))).unique
        (H'.hasFDerivAt_hp z (hDH' hz))
  exact {
    time := Ψ.time
    isOpen_time := Ψ.isOpen_time
    isPreconnected_time := Ψ.isPreconnected_time
    zero_mem_time := Ψ.zero_mem_time
    parameters := Ψ.parameters
    isOpen_parameters := Ψ.isOpen_parameters
    sectionMap := Ψ.sectionMap
    position := Ψ.position
    momentum := Ψ.momentum
    positionVariation := Ψ.positionVariation
    momentumVariation := Ψ.momentumVariation
    state_mem := fun t ht s hs ↦ hDH (hrange (t, s) ⟨ht, hs⟩)
    position_derivative := fun t ht s hs ↦ by
      rw [hg.2 (hrange (t, s) ⟨ht, hs⟩)]
      exact Ψ.position_derivative t ht s hs
    momentum_derivative := fun t ht s hs ↦ by
      rw [hg.1 (hrange (t, s) ⟨ht, hs⟩)]
      exact Ψ.momentum_derivative t ht s hs
    variation_equation := fun t ht s hs v ↦ by
      rw [hdp (hrange (t, s) ⟨ht, hs⟩)]
      exact Ψ.variation_equation t ht s hs v
    initial_position := Ψ.initial_position
    initial_energy := fun s hs ↦ by
      rw [he (hrange (0, s) ⟨Ψ.zero_mem_time, hs⟩)]
      exact Ψ.initial_energy s hs
    initial_momentum := Ψ.initial_momentum }

/-- Locally equal symbols have identical actual states on the original common
source ball. Initial energy and tangential momentum determine the same root on
the retained transverse state ball; ODE uniqueness then applies without any
source or target shrink (`app:lem:common-hamilton-phase`). -/
theorem state_eqOn_of_local_symbol_eq
    {H H' : HomogeneousSymbol E} (Φ : HamiltonFlow H U) (Ψ : HamiltonFlow H' U)
    {D : Set (E × E)} (hD : IsOpen D)
    (hDH : D ⊆ H.domain) (hDH' : D ⊆ H'.domain)
    (hH : ContDiffOn ℝ ∞ H.h D) (he : EqOn H.h H'.h D)
    {w : E × E} {R d : ℝ} (hRD : closedBall w R ⊆ D) (hd : 0 < d)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (hν : ν ≠ 0)
    (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    (hj : Φ.sectionMap = j.toContinuousLinearMap)
    (hj' : Ψ.sectionMap = j.toContinuousLinearMap)
    (hgap : ∀ z ∈ closedBall w R, ⟪H.hp z, ν⟫_ℝ ≠ 0)
    {s₀ : InitialData U}
    (hadm : ball ((0 : ℝ), s₀) d ⊆ Φ.time ×ˢ Φ.parameters)
    (hadm' : ball ((0 : ℝ), s₀) d ⊆ Ψ.time ×ˢ Ψ.parameters)
    (hrange : ∀ q ∈ Φ.time ×ˢ Φ.parameters,
      (Φ.position q, Φ.momentum q) ∈ closedBall w R)
    (hrange' : ∀ q ∈ Ψ.time ×ˢ Ψ.parameters,
      (Ψ.position q, Ψ.momentum q) ∈ closedBall w R) :
    EqOn (fun q ↦ (Φ.position q, Φ.momentum q))
      (fun q ↦ (Ψ.position q, Ψ.momentum q)) (ball ((0 : ℝ), s₀) d) := by
  let Ψ' := flowForLocallyEqualSymbol Ψ hD hDH hDH' he
    (fun q hq ↦ hRD (hrange' q hq))
  exact Φ.state_eq_on_transverse_ball Ψ' hD hDH hH hRD hd
    j ν hν horth hspan hj hj' hgap hadm hadm' hrange hrange'

end JanetCartan.ActualCarriers.CurrentFullPhase.LocalFrameAgreement
