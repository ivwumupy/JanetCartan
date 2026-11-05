module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Chart

/-!
# The original leading null-flow as a retained chart

This constructor repackages the coefficient and ODE clauses of the common
initializer's original `hleading` continuation, without choosing another flow.
Its `Q`, `D`, `forward` and `inverse` are definitionally the supplied witnesses.
Consumer: `exists_common_initializer_with_capped_history_inverse`, which passes
this chart and the same full leading `Φ/Y` to the history inverse. This local
constructor is not the original-data existence theorem
(`app:ch_waves:thm:leading`, `app:ch_background:prop:bg-adjoint`).
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumInverse.InitializedCappedHistory
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow
open FlowAmplitude ProjectedStressFrame
open ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction

/-- Package the literal original leading coefficient/ODE data, not a new
existential chart. The two arguments are projections of the initializer's
finite-history leading continuation; no inverse estimate is an argument. -/
def chartOfOriginalLeading
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {F : Euclidean n → Euclidean N}
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (hframe : Q.val = projectedStress F)
    {Ω : Set (Euclidean n × Euclidean 3)} {K : Set (Euclidean n)}
    {z : Euclidean 3} {ρ M g R τ : ℝ} {row col : Fin n}
    (D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)))
    (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (hcoeff :
      ContDiffOn ℝ ∞ (carrierNullvector T Q col) Ω ∧
      ContDiffOn ℝ ∞ (carrierConullvector T Q row) Ω ∧
      ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ω ∧
      ContDiffOn ℝ ∞ (carrierTransportPotential T Q F row col) Ω ∧
      cNorm (closedBall ((0 : Euclidean n), z) ρ) 1
        (carrierTransportDirection T Q row col) ≤ M ∧
      (∀ w ∈ Ω, ∀ i, (Q.val w.1 i).IsSymm) ∧
      (∀ w ∈ Ω,
        carrierNullvector T Q col w ≠ 0 ∧ carrierConullvector T Q row w ≠ 0 ∧
        reducedSymbol (Q.val w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
          (fun j ↦ carrierNullvector T Q col w j) = 0 ∧
        carrierConullvector T Q row w ᵥ*
          reducedSymbol (Q.val w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
        g ≤ |carrierAdaptedDenominator T Q row col w| ∧
        carrierAdaptedDenominator T Q row col w ≠ 0 ∧
        |(carrierAdaptedDenominator T Q row col w)⁻¹| ≤ g⁻¹) ∧
      D = (fun q ↦ (q.1, φ q)) ''
        (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) ∧
      D ⊆ (coordinates (adaptedCoordinates T.data.adapted)).symm ⁻¹' Ω ∧
      (coordinates (adaptedCoordinates T.data.adapted)) ⁻¹' D ⊆ Ω ∧
      (coordinates (adaptedCoordinates T.data.adapted)) ⁻¹' D ⊆
        (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
          parameterInterior (3 * P.radius / 2) ∧
      ContDiffOn ℝ ∞ φ (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) ∧
      ContDiffOn ℝ ∞ y D ∧
      (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8),
        ∀ t ∈ Ioo (-τ) τ, (φ (t, p)).2 = p.2) ∧
      (∀ q ∈ D, (y q).2 = q.2.2) ∧
      ContDiffOn ℝ ∞ y
        (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 4)))
    (hflow :
      IsOpen D ∧ Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 32) ⊆ D ∧
      D ⊆ Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 4) ∧
      MapsTo (fun q ↦ (q.1, φ q))
        (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) D ∧
      MapsTo (fun q ↦ (q.1, y q)) D
        (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) ∧
      (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), φ (0, p) = p) ∧
      (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), ∀ t ∈ Ioo (-τ) τ,
        y (t, φ (t, p)) = p) ∧
      (∀ q ∈ D, φ (q.1, y q) = q.2) ∧
      (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), ∀ t ∈ Ioo (-τ) τ,
        HasDerivAt (fun s ↦ φ (s, p))
          ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Q row col
            ((coordinates (adaptedCoordinates T.data.adapted)).symm (t, φ (t, p))))).2, 0) t) ∧
      ContDiffOn ℝ ∞ φ
        (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 4))) :
    Chart T Ω (closedBall ((0 : Euclidean n), z) ρ)
      ((0 : Euclidean (n - 1)), z) R M τ row col F := by
  obtain ⟨hn, hcn, hd, hp, hdb, hsymm, hns, hDeq, hDcoeff, _, _, hφs, hys, hφp, hyp, hyb⟩ := hcoeff
  obtain ⟨hD, hsmall, hbig, hφD, hyRange, hφ₀, hyφ, hφy, hode, hφBuffer⟩ := hflow
  exact {
    Q := Q
    frame_eq := hframe
    null_smooth := hn
    conull_smooth := hcn
    direction_smooth := hd
    potential_smooth := hp
    direction_bound := hdb
    symm := hsymm
    null_spec := fun w hw ↦ ⟨(hns w hw).1, (hns w hw).2.1, (hns w hw).2.2.1,
      (hns w hw).2.2.2.1, (hns w hw).2.2.2.2.2.1⟩
    D := D
    forward := φ
    inverse := y
    domain_eq := hDeq
    domain_open := hD
    small_subset := hsmall
    subset_big := hbig
    domain_coefficients := hDcoeff
    forward_smooth := hφs
    inverse_smooth := hys
    forward_range := hφD
    inverse_range := hyRange
    initial := hφ₀
    inverse_forward := hyφ
    forward_inverse := hφy
    forward_parameter := hφp
    inverse_parameter := hyp
    ode := hode
    forward_buffer_smooth := hφBuffer
    inverse_buffer_smooth := hyb }

/-- The packaged chart uses exactly the original coefficient, domain and
forward/inverse maps; all four equalities are definitional. -/
theorem chartOfOriginalLeading_same_witnesses
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {F : Euclidean n → Euclidean N}
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (hframe : Q.val = projectedStress F)
    {Ω : Set (Euclidean n × Euclidean 3)} {K : Set (Euclidean n)}
    {z : Euclidean 3} {ρ M g R τ : ℝ} {row col : Fin n}
    (D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)))
    (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (hcoeff hflow) :
    let current := chartOfOriginalLeading T Q hframe (Ω := Ω) (K := K) (z := z)
      (ρ := ρ) (M := M) (g := g) (R := R) (τ := τ) (row := row) (col := col)
      D φ y hcoeff hflow
    current.Q = Q ∧ current.D = D ∧ current.forward = φ ∧ current.inverse = y :=
  ⟨rfl, rfl, rfl, rfl⟩

end JanetCartan.ContinuumInverse.InitializedCappedHistory
