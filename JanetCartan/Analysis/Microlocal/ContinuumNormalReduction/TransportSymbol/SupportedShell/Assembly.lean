module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.Assembly
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.SupportedShell.Localization

/-!
# Primitive transport bounds on the supported shell

This supplies the supported shell estimate for the homogeneous and high-cutoff
bounds consumed by `jc-carrier-supported-shell-construction`. All inverse and
Jacobian profiles are derived by the existing geometry producer; the only
changed premise is containment on the closed transported mask support.
Source: `app:ch_background:eq:bg-mixed-input` and `app:ch_background:prop:bg-frame`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- One-high finite mixed jets of the literal spectator amplitude from
primitive coefficient profiles and primitive mixed jets of `Y`. All inverse
and Jacobian quantitative premises of the shell estimate are discharged here
using the actual averaged-gradient identity and absolute determinant.

The low geometry bound is fixed before the fields vary. The high geometry
order is exactly `s+2`; a primitive producer shift `D` therefore becomes
`D+2`, independently of `s`. The same `H` can include the high norms of allowed
initial multipliers, whose composition is proved in `ShellBounds.InitialMultiplier`.
Shell containment is required only on the closure of the transported original
support. Chart regularity and relative support buffers remain geometric inputs. The open region `R` may exclude zero frequency.
Source: `app:ch_background:eq:bg-full-complex-amplitude` and
`app:ch_regular_base:eq:joint-primitive-product`. -/
theorem exists_transportAmplitude_supported_shell_bound
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
        d.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → d.high ‖p.2.2‖ ≠ 0 → p ∈ Z) →
      IsOpen R → X ⊆ R →
      closure (augmentedTransportGradient Y '' Z) ∩ (R ×ˢ univ) ⊆ Ω →
      (∀ x ∈ X, ∀ v ∈ S, (x, v) ∈ closure (augmentedTransportGradient Y '' Z) →
        (x, v) ∈ closedBall b τ) →
      (∀ p ∈ closedBall a ρ, CoefficientShellProfiles s H E d p) →
      ∀ x ∈ X, ∀ k ≤ s, ‖iteratedFDeriv ℝ k (amplitude d J u Ω S) x‖ ≤ C * H := by
  obtain ⟨D, hD, hprofiles⟩ := exists_transportInverseJacobian_shellProfiles
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM hδ hB s hs
  obtain ⟨C, hC, hbound⟩ := exists_amplitude_shell_bound_of_supported_buffer (N := N)
    s hs (add_nonneg hE hD.le) hD.le (isCompact_closedBall a ρ)
    (isCompact_closedBall b τ) hδ hε hη hS
  refine ⟨C, hC, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff
  obtain ⟨hjp, hup⟩ := hprofiles Y u J Ω H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne
    hdet hH hhigh
  have hH0 := zero_le_one.trans hH
  have hEC : E ≤ E + D := le_add_of_nonneg_right hD.le
  have hDC : D ≤ E + D := le_add_of_nonneg_left hE
  have hprim (p) (hp : p ∈ closedBall a ρ) : PrimitiveShellProfiles s H (E + D) d J p := {
    leftMeasurement := (hcoeff p hp).leftMeasurement.mono hEC hH0
    rightMeasurement := (hcoeff p hp).rightMeasurement.mono hEC hH0
    angular := (hcoeff p hp).angular.mono hEC hH0
    high := (hcoeff p hp).high.mono hEC hH0
    leftNormal := (hcoeff p hp).leftNormal.mono hEC hH0
    rightNormal := (hcoeff p hp).rightNormal.mono hEC hH0
    leftReduced := (hcoeff p hp).leftReduced.mono hEC hH0
    rightReduced := (hcoeff p hp).rightReduced.mono hEC hH0
    jacobian := (hjp p hp).mono hDC hH0 }
  apply hbound d J u (augmentedTransportGradient Y) Ω U Z X R H hH hΩ hreg hu hmap
    (augmentedTransportGradient_inverseCoordinates Y u heq) hsupp hR hXR hbuffer
  · intro x hx v hv hΩx
    have hp := hshell x hx v hv hΩx
    exact ⟨hp, hrange hp⟩
  · intro p hp
    rw [hJ (hball hp), abs_of_nonneg (hδ.le.trans (hdet p hp))]
    exact hdet p hp
  · exact hprim
  · exact hup

end JanetCartan.ContinuumNormalReduction.TransportSymbol
