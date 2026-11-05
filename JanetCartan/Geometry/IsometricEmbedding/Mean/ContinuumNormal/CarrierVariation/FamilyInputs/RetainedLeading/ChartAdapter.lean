module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Chart

/-!
# The retained leading maps as a comparison chart

The inputs below are the primitive outputs of
`CurrentCoefficientProfiles.exists_full_joint_leading_wave_before_geometry_with_carrier_data`,
also retained by the finite-cover and history variants. No new flow, minor or
scalar is chosen. Consumer: the original-scalar primitive comparison for
`app:ch_background:prop:bg-frame` and `app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open PositiveReference.FlowConstruction

/-- Package the SAME retained carrier maps and selected minor into the existing
ODE comparison interface. Every argument is exported jointly with these maps by
the full-leading producer (`app:ch_waves:thm:leading`, `app:ch_waves:eq:joint-tame`).
The output maps and frame are definitionally the supplied ones. -/
def chartOfRetainedCarrierData
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (hQ : Q.1 = ProjectedStressFrame.projectedStress F)
    {Ω K : Set (Euclidean n × Euclidean 3)}
    {p₀ : Euclidean (n - 1) × Euclidean 3} {R B τ g : ℝ} {row col : Fin n}
    (D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)))
    (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (hk : ContDiffOn ℝ ∞ (carrierNullvector T Q col) Ω)
    (hl : ContDiffOn ℝ ∞ (carrierConullvector T Q row) Ω)
    (hd : ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ω)
    (hc : ContDiffOn ℝ ∞ (carrierTransportPotential T Q F row col) Ω)
    (hB : cNorm K 1 (carrierTransportDirection T Q row col) ≤ B)
    (hsymm : ∀ w ∈ Ω, ∀ i, (Q.1 w.1 i).IsSymm)
    (hnull : ∀ w ∈ Ω,
      carrierNullvector T Q col w ≠ 0 ∧ carrierConullvector T Q row w ≠ 0 ∧
      reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
        (fun j ↦ carrierNullvector T Q col w j) = 0 ∧
      carrierConullvector T Q row w ᵥ*
        reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
      g ≤ |carrierAdaptedDenominator T Q row col w| ∧
      carrierAdaptedDenominator T Q row col w ≠ 0 ∧
      |(carrierAdaptedDenominator T Q row col w)⁻¹| ≤ g⁻¹)
    (himage : D = (fun q ↦ (q.1, φ q)) '' (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)))
    (hcoeff : D ⊆ (coordinates (adaptedCoordinates T.data.adapted)).symm ⁻¹' Ω)
    (hφ : ContDiffOn ℝ ∞ φ (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)))
    (hy : ContDiffOn ℝ ∞ y D)
    (hφz : ∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ, (φ (t, p)).2 = p.2)
    (hyz : ∀ q ∈ D, (y q).2 = q.2.2)
    (hybuffer : ContDiffOn ℝ ∞ y (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)))
    (hD : IsOpen D) (hsmall : Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D)
    (hbig : D ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 4))
    (hφD : MapsTo (fun q ↦ (q.1, φ q)) (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) D)
    (hyL : MapsTo (fun q ↦ (q.1, y q)) D (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)))
    (hφ₀ : ∀ p ∈ ball p₀ (R / 8), φ (0, p) = p)
    (hyφ : ∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ, y (t, φ (t, p)) = p)
    (hφy : ∀ q ∈ D, φ (q.1, y q) = q.2)
    (hode : ∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun s ↦ φ (s, p))
        ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Q row col
          ((coordinates (adaptedCoordinates T.data.adapted)).symm (t, φ (t, p))))).2, 0) t)
    (hφbuffer : ContDiffOn ℝ ∞ φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4))) :
    Chart T Ω K p₀ R B τ row col F where
  Q := Q
  frame_eq := hQ
  null_smooth := hk
  conull_smooth := hl
  direction_smooth := hd
  potential_smooth := hc
  direction_bound := hB
  symm := hsymm
  null_spec := fun w hw ↦ ⟨(hnull w hw).1, (hnull w hw).2.1,
    (hnull w hw).2.2.1, (hnull w hw).2.2.2.1, (hnull w hw).2.2.2.2.2.1⟩
  D := D
  forward := φ
  inverse := y
  domain_eq := himage
  domain_open := hD
  small_subset := hsmall
  subset_big := hbig
  domain_coefficients := hcoeff
  forward_smooth := hφ
  inverse_smooth := hy
  forward_range := hφD
  inverse_range := hyL
  initial := hφ₀
  inverse_forward := hyφ
  forward_inverse := hφy
  forward_parameter := hφz
  inverse_parameter := hyz
  ode := hode
  forward_buffer_smooth := hφbuffer
  inverse_buffer_smooth := hybuffer

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
