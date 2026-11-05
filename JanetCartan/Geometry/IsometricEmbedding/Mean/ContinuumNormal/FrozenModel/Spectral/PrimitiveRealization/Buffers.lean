module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Coefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.CoefficientBuffers.FiniteDomains

/-!
# Construct the frozen coefficient charts and their finite budgets

Specialize the existing finite-domain producer to the actual seed coefficient
region. The resulting charts precede the current frame and immersion, while
their finite coefficient budgets are proved for each fixed seed. The parent
still constructs a common input/output ball and its supported shell geometry.

Consumer: `exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`.
Sources: `new:lem:scaling`, `app:ch_background:eq:bg-mixed-input`, and
`app:ch_background:prop:bg-frame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol TransportKernel

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The fixed seed parameter buffer produces finite coefficient charts,
segment buffers, a positive input-frequency bound, and all primitive norm
controls for the literal measured unit-initial frozen carrier. The cap and
charts precede `Q`, `F`, and all derivative orders. The norm constants may
depend on the fixed seed; no uniform varying-immersion estimate is claimed.

The input-ball inclusion is purely geometric and is to be instantiated by
the frozen supported-shell construction. No coefficient smoothness or bound
is assumed (`new:lem:scaling`, `app:ch_background:eq:bg-mixed-input`). -/
theorem exists_frozenMeasured_coefficient_buffers
    {c C : ℝ} (hP : P.IsValid c C)
    (z₀ : Euclidean 3) (hz₀ : z₀ ∈ parameterInterior P.radius)
    (ηb : Euclidean (n - 1)) (hηb : ηb ≠ 0) :
    ∃ cap > (0 : ℝ), ∀ {r a ρ : ℝ}, 0 < ρ → ρ < cap →
      let p₀ : InputVariables n := ((0, 0), (z₀ 0, spectatorCenter z₀), ηb)
      closedBall p₀ ρ ⊆ symbolInputDomain z₀ ηb r (6 * a) →
      ∃ (W K : Set (InputVariables n))
        (Vphase Lphase : Set (Euclidean n × CarrierParameter))
        (I : Set ℝ) (D : CoefficientNormCharts n) (ε : ℝ),
        IsOpen W ∧ IsCompact K ∧ closedBall p₀ ρ ⊆ W ∧ W ⊆ K ∧
        K ⊆ symbolInputDomain z₀ ηb r (6 * a) ∧
        IsOpen Vphase ∧ IsCompact Lphase ∧ Lphase ⊆ Vphase ∧
        IsOpen I ∧ (∃ l u : ℝ, I = Ioo l u) ∧ Icc (0 : ℝ) 1 ⊆ I ∧
        (∀ t ∈ I, MapsTo (transportSegmentInput n t) W Vphase) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W Lphase) ∧
        D.field.carrier = Lphase ∧ D.field.region = Vphase ∧
        Vphase ⊆ coefficientDomain z₀ r (6 * a) ∧
        MapsTo (fun p : Euclidean n × CarrierParameter ↦ p.2) D.field.region
          (parameter ⁻¹' parameterInterior (2 * P.radius)) ∧
        (∀ p ∈ closedBall p₀ ρ, D.Contains p) ∧
        (∀ {a' : ℝ} (ha' : 0 < a'), 4 * a' < ρ →
          tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
            carrierSupport z₀ (r := a') ⊆ D.field.carrier) ∧
        0 < ε ∧ (∀ p ∈ closedBall p₀ ρ, ε ≤ ‖p.2.2‖) ∧
        ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold})
          {N : ℕ} (F : Euclidean n → Euclidean N) (row col : Fin n)
          (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
          {r' a' : ℝ} (hr' : 0 < r') (ha' : 0 < a') (hcell : 4 * a' < 1 / 2),
          ∃ M ≥ 0, ∃ B : ℕ → ℝ, (∀ s, 1 ≤ B s) ∧ ∀ s H, 1 ≤ H →
            D.Controls s M (B s) H
              (coefficientsOfCarrier
                (normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) ha' hcell
                  (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
                  FixedCutoffs.highFrequency 0) (FixedCutoffs.physical ha' 1)) := by
  let E : Set (Euclidean n × CarrierParameter) :=
    (fun p ↦ parameter p.2) ⁻¹' parameterInterior (2 * P.radius)
  have hE : IsOpen E := (isOpen_parameterInterior _).preimage
    (parameter.continuous.comp continuous_snd)
  have hcenter : ((0 : Euclidean n), (z₀ 0, spectatorCenter z₀)) ∈ E := by
    change carrierParameters (spectatorCenter z₀, z₀ 0) ∈ parameterInterior (2 * P.radius)
    rw [carrierParameters_spectatorCenter]
    exact parameterCube_subset_doubledInterior hP.1 (fun i ↦ (hz₀ i).le)
  obtain ⟨cap, hcap, hbuffers⟩ := exists_coefficient_buffers_cap z₀ ηb hηb E hE hcenter
  refine ⟨cap, hcap, ?_⟩
  intro r a ρ hρ hρcap
  dsimp only
  intro hinput
  obtain ⟨W, K, Vphase, Lphase, I, D, ε, hW, hK, hball, hWK, hKdom,
    hV, hL, hLV, hI, hinterval, hIT, hsegT, hseg, hDcar, hDreg, hDom, hfoot,
    hsupport, hε, hη⟩ := hbuffers hρ hρcap hinput
  have hfield : MapsTo (fun p : Euclidean n × CarrierParameter ↦ p.2)
      D.field.region (parameter ⁻¹' parameterInterior (2 * P.radius)) := by
    intro p hp
    exact (hDom (hDreg ▸ hp)).1
  refine ⟨W, K, Vphase, Lphase, I, D, ε, hW, hK, hball, hWK, hKdom,
    hV, hL, hLV, hI, hinterval, hIT, hsegT, hseg, hDcar, hDreg,
    fun _ hp ↦ (hDom hp).2, hfield, hfoot, hsupport, hε, hη, ?_⟩
  intro Q N F row col Φ Y r' a' hr' ha' hcell
  exact exists_frozenMeasured_primitive_controls_unit T Q F row col Φ Y
    hηb hr' ha' hcell hP D hfield

end JanetCartan.ContinuumNormal.FrozenModel
