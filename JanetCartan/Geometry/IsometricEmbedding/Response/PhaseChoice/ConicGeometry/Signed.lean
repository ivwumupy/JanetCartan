module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PhaseChoice.ConicGeometry.Inverse
public import JanetCartan.Geometry.IsometricEmbedding.Response.PhaseChoice.ConicGeometry.AngularBuffers

/-!
# Exact conjugate phase and full-energy equation

The signed partner in `app:ch_response:thm:response-compatible-choice` uses
the original physical covectors, the same section, and the exact reflection
`S₋(x,η) = -S₊(x,-η)`. No Fourier or `2π` convention is changed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Full-energy eikonal and physical covector nonvanishing on the entire
continued cone (`app:ch_response:eq:response-energy-root`). -/
theorem conicSectionEnergyPhase_eikonal
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) {r : ℝ}
    (hr : r ≤ min T.family.radius (3 * T.family.sourceRadius)) (Q : _)
    {x : Euclidean n} (hx : x ∈ ball 0 T.physicalRadius)
    {η : ℝ × Euclidean (n - 1)} (hη : η ∈ T.sectionEnergyCone ℓ r) :
    gradient (fun y ↦ T.conicSectionEnergyPhase ℓ Q y η) x ≠ 0 ∧
      normalizedSymbol Q.1 (x, gradient (fun y ↦ T.conicSectionEnergyPhase ℓ Q y η) x) = η.1 := by
  have hc : (normalizedHomogeneousSymbol hU Q.1 Q.2.1).ConicHomogeneous := {
    scale_mem := by
      intro z hz a ha
      exact ⟨hz.1, smul_ne_zero ha.ne' hz.2⟩
    scale_symbol := by
      intro z _ a ha
      exact normalizedSymbol_pos_homogeneous Q.1 z ha }
  have he := (T.currentChart Q).conicPhase_eikonal ℓ hc (z := (x, η))
    ⟨hη.1, T.sectionEnergyDomain_subset_target Q hx (ball_subset_ball hr hη.2)⟩
  exact ⟨he.1.2, he.2⟩

/-- The conjugate continuation has exactly the opposite physical gradient
at the reflected canonical covector
(`app:ch_response:eq:response-exact-phase`). -/
theorem conjugateConicSectionEnergyPhase_gradient
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) (Q : _)
    (x : Euclidean n) (η : ℝ × Euclidean (n - 1)) :
    gradient (fun y ↦ T.conjugateConicSectionEnergyPhase ℓ Q y η) x =
      -gradient (fun y ↦ T.conicSectionEnergyPhase ℓ Q y (-η)) x := by
  change gradient (-(fun y ↦ T.conicSectionEnergyPhase ℓ Q y (-η))) x = _
  simp only [gradient, fderiv_neg, map_neg]

/-- Positive degree one for the literal signed partner
(`app:ch_response:thm:response-compatible-choice`). -/
theorem conjugateConicSectionEnergyPhase_smul
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) (Q : _)
    (x : Euclidean n) (η : ℝ × Euclidean (n - 1)) {a : ℝ} (ha : 0 < a) :
    T.conjugateConicSectionEnergyPhase ℓ Q x (a • η) =
      a * T.conjugateConicSectionEnergyPhase ℓ Q x η := by
  simp only [conjugateConicSectionEnergyPhase, ← smul_neg,
    T.conicSectionEnergyPhase_smul ℓ Q x (-η) ha, mul_neg]

/-- The exact conjugate agrees on the reflected buffered overlap
(`app:ch_response:eq:response-exact-phase`). -/
theorem conjugateConicSectionEnergyPhase_eq_on_overlap
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) {r : ℝ}
    (hr : r ≤ min T.family.radius (3 * T.family.sourceRadius)) (Q : _)
    {x : Euclidean n} (hx : x ∈ ball 0 T.physicalRadius)
    {η : ℝ × Euclidean (n - 1)} (hη : -η ∈ T.sectionEnergyDomain)
    (hc : -η ∈ T.sectionEnergyCone ℓ r) :
    T.conjugateConicSectionEnergyPhase ℓ Q x η = T.conjugateSectionEnergyPhase Q x η := by
  exact congrArg Neg.neg (T.conicSectionEnergyPhase_eq_on_overlap ℓ hr Q hx hη hc)

/-- Both signed continuations have the same positive section pairing on their
respective cones (`app:ch_response:eq:response-energy-Cauchy`). -/
theorem conjugateConicSectionEnergyPhase_section
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) {r : ℝ}
    (hr : r ≤ min T.family.radius (3 * T.family.sourceRadius)) (Q : _)
    {u : Euclidean (n - 1)} (hu : T.reference.sectionEmbedding u ∈ ball 0 T.physicalRadius)
    {η : ℝ × Euclidean (n - 1)} (hη : -η ∈ T.sectionEnergyCone ℓ r) :
    T.conjugateConicSectionEnergyPhase ℓ Q (T.reference.sectionEmbedding u) η = ⟪u, η.2⟫_ℝ := by
  rw [conjugateConicSectionEnergyPhase, T.conicSectionEnergyPhase_section ℓ hr Q hu hη]
  simp

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
