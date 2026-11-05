module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.CompletionBounds.Annulus

/-!
# Primitive assembly on the fixed completion annulus

The only quantitative inputs concern primitive fields. The actual inverse and
Jacobian identities discharge the substituted-density estimates. The parent must
instantiate the relative buffer and the containment of the fixed annulus in the
working chart. These are independent of radial regularization.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- The closed frequency annulus that can carry the completion discrepancy,
restricted to the specified physical domain `X`. Its inner gap is chosen with
`ℓ ≤ 1` and `Cupper * ℓ ≤ 1`; its outer radius is the exact completion threshold.
Source: the paragraph following `app:ch_background:eq:bg-symbol`. -/
def completionAnnulus (X : Set (Variables n)) (ℓ C : ℝ) : Set (Variables n) :=
  X ∩ {x | ℓ ≤ ‖x.2.2‖ ∧ ‖x.2.2‖ ≤ max 2 (2 * C)}

/-- Uniform discrepancy jets from primitive coefficient profiles and primitive
geometry norms, with the single fixed high-order shift two. The profiles here
are produced from finite primitive norms in `CompletionBounds`. `Z` contains the
support of the homogeneous masks, and its image has a relative buffer on `R`.
The parent must put `completionAnnulus X ℓ Clower` in `R` and all active spectator
points there in the fixed output ball. No amplitude, density, or inverse-jet
estimate is assumed. Source: the smoothing paragraph after
`app:ch_background:eq:bg-symbol`. -/
theorem exists_transportCompletion_discrepancy_bound_of_profiles
    (c : TransportSliceCoordinates n) (a : InputVariables n)
    (b : Variables n × Euclidean 2) {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ)
    {W K : Set (InputVariables n)} (hW : IsOpen W)
    (hball : closedBall a ρ ⊆ W) (hK : IsCompact K) (hWK : W ⊆ K)
    {O : Set (Variables n × Euclidean 2)} (hO : IsOpen O)
    (houtput : closedBall b τ ⊆ O)
    {V L : Set (Euclidean n × (ℝ × Euclidean 2))}
    (hV : IsOpen V) (hL : IsCompact L) (hLV : L ⊆ V)
    {T : Set ℝ} (hT : IsOpen T) (hIT : Icc (0 : ℝ) 1 ⊆ T)
    (hsegT : ∀ t ∈ T, MapsTo (transportSegmentInput n t) W V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W L)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {M E δ ε B : ℝ} (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hδ : 0 < δ) (hε : 0 < ε) (hB : 0 ≤ B)
    (hη : ∀ p ∈ closedBall a ρ, ε ≤ ‖p.2.2‖)
    {Cupper Clower ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hClower : 0 < Clower)
    (_hℓ : 0 < ℓ) (hℓone : ℓ ≤ 1) (hlow : Cupper * ℓ ≤ 1)
    {S : Set (Euclidean 2)} (hS : IsCompact S) (s : ℕ) (hs : 2 ≤ s) :
    ∃ C > 0, ∀ (d : Coefficients n N)
      (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (J : InputVariables n → ℝ) (Ω : Set (Variables n × Euclidean 2))
      (U Z : Set (InputVariables n)) (X R : Set (Variables n)) (H : ℝ),
      ContDiffOn ℝ ∞ Y V → cNorm L 3 Y ≤ M →
      IsOpen Ω → O ⊆ Ω → ContDiffOn ℝ ∞ u Ω →
      MapsTo (inverseCoordinates u) (closedBall b τ) (closedBall a ρ) →
      (∀ q ∈ closedBall a ρ,
        ‖(A.symm : (Variables n × Euclidean 2) →L[ℝ] InputVariables n).comp
          (fderiv ℝ (augmentedTransportGradient Y) q) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      (∀ p ∈ Ω, transportAveragedGradient Y (inverseCoordinates u p) = p.1.2.2) →
      EqOn J (transportAbsoluteJacobian c Y) W → (∀ p ∈ W, J p ≠ 0) →
      (∀ q ∈ closedBall a ρ, δ ≤ transportAbsoluteJacobian c Y q) →
      1 ≤ H → 1 + cNorm L (s + 2) Y ≤ B * H →
      PrimitiveRegularity d J U → MapsTo (inverseCoordinates u) Ω U →
      (∀ p ∈ U, d.measurement p.1.1 ≠ 0 → d.measurement p.1.2 ≠ 0 →
        d.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Z) →
      IsOpen R → completionAnnulus X ℓ Clower ⊆ R →
      closure (augmentedTransportGradient Y '' Z) ∩ (R ×ˢ univ) ⊆ Ω →
      (∀ x ∈ completionAnnulus X ℓ Clower, ∀ v ∈ S, (x, v) ∈ Ω → (x, v) ∈ closedBall b τ) →
      (∀ p ∈ closedBall a ρ, CoefficientShellProfiles s H E d p) →
      (∀ r : ℝ, r ≤ 1 → d.high r = 0) →
      (∀ r : ℝ, 2 ≤ r → d.high r = 1) →
      (∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖) →
      (∀ p ∈ Ω, ‖p.1.2.2‖ ≤ Clower * ‖(u p).2‖) →
      ∀ x ∈ X, ∀ k ≤ s, ‖iteratedFDeriv ℝ k
        (fun p ↦ amplitude d J u Ω S p - completedAmplitude d J u Ω S p) x‖ ≤ C * H := by
  obtain ⟨Acut, hAcut, hcut⟩ := exists_completionCutoff_joint_jet_bound (n := n)
    (max 2 (2 * Clower)) s
  obtain ⟨C, hC, hb⟩ := exists_transportAmplitude_shell_bound (N := N)
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM (show 0 ≤ E + 1 by linarith) hδ hε hB hη hS s hs
  refine ⟨(1 + 2 ^ s * Acut) * C, by positivity, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hzero hone hupper hlower
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hcoeff' (p) (hp : p ∈ closedBall a ρ) :
      CoefficientShellProfiles s H (E + 1) d p := by
    have h := hcoeff p hp
    exact {
      leftMeasurement := h.leftMeasurement.mono (by linarith) hH0
      rightMeasurement := h.rightMeasurement.mono (by linarith) hH0
      angular := h.angular.mono (by linarith) hH0
      high := h.high.mono (by linarith) hH0
      leftNormal := h.leftNormal.mono (by linarith) hH0
      rightNormal := h.rightNormal.mono (by linarith) hH0
      leftReduced := h.leftReduced.mono (by linarith) hH0
      rightReduced := h.rightReduced.mono (by linarith) hH0 }
  have hb₁ := hb d Y u J Ω U Z (completionAnnulus X ℓ Clower) R H
    hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet hH hhigh hreg hmap
    (fun p hp h₁ h₂ h₃ _ ↦ hsupp p hp h₁ h₂ h₃) hR hXR hbuffer hshell hcoeff'
  have hb₂ := hb (homogeneousCoefficients d) Y u J Ω U Z
    (completionAnnulus X ℓ Clower) R H
    hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet hH hhigh hreg.homogeneous hmap
    (fun p hp h₁ h₂ h₃ _ ↦ hsupp p hp h₁ h₂ h₃) hR hXR hbuffer hshell
    (fun p hp ↦ (hcoeff p hp).homogeneous hE hH0)
  have hright := augmentedTransportGradient_inverseCoordinates Y u heq
  have ha := amplitude_contDiffOn_of_relative_buffer d J u (augmentedTransportGradient Y)
    hΩ hR hreg hu hmap hright (fun p hp h₁ h₂ h₃ _ ↦ hsupp p hp h₁ h₂ h₃) hbuffer hS
  have hh := amplitude_contDiffOn_of_relative_buffer (homogeneousCoefficients d) J u
    (augmentedTransportGradient Y) hΩ hR hreg.homogeneous hu hmap hright
    (fun p hp h₁ h₂ h₃ _ ↦ hsupp p hp h₁ h₂ h₃) hbuffer hS
  intro x hx k hk
  by_cases hlowx : ‖x.2.2‖ < ℓ
  · rw [iteratedFDeriv_completion_discrepancy_eq_zero_of_low_frequency
      d J u Ω S hzero hCupper hℓone hlow hupper x hlowx k, norm_zero]
    positivity
  by_cases hhighx : max 2 (2 * Clower) < ‖x.2.2‖
  · rw [iteratedFDeriv_completion_discrepancy_eq_zero_of_large_frequency
      d J u Ω S hone hClower hlower x hhighx k, norm_zero]
    positivity
  have hxann : x ∈ completionAnnulus X ℓ Clower :=
    ⟨hx, le_of_not_gt hlowx, le_of_not_gt hhighx⟩
  have hbound := norm_iteratedFDeriv_completion_discrepancy_on_le d J u Ω S hR ha hh hk
    (hXR hxann) hAcut.le (mul_nonneg hC.le hH0)
    (hcut x hxann.2.2) (hb₁ x hxann k hk) (hb₂ x hxann)
  convert hbound using 1
  ring

end JanetCartan.ContinuumNormalReduction.TransportSymbol
