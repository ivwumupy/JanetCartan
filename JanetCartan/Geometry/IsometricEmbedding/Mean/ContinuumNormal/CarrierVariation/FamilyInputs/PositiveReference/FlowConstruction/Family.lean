module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Construction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Comparison

/-!
# Actual families with instantiated primitive dependence

Choose the maps for every geometrically admissible immersion before choosing
an output order or tolerance. Instantiate the coefficient-to-flow implication
for this family. The parent retains only the comparison of the primitive
projected stress and Hamilton gradient, and matching its Hamilton target to the
supplied open restriction (`app:ch_background:prop:bg-frame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow ProjectedStressFrame

/-- Exactly the primitive geometric hypotheses of the actual coefficient
producer, including the strict reference margin. This set has no transport or
continuity hypotheses (`app:ch_waves:thm:leading`). -/
def admissibleImmersions {n N : ℕ} (U KF : Set (Euclidean n)) (C₀ κmet κnormal η : ℝ) :
    Set (Euclidean n → Euclidean N) :=
  {F | ContDiffOn ℝ ∞ F U ∧ IsImmersionOn F U ∧ HasFullNormalRankOn F U ∧
    cNorm KF 4 F ≤ C₀ ∧
    (∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
    (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
      κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
    cNorm KF 6 (projectedStress F - fun _ ↦ cubeStress n) < η}

/-- The actual family of positive null flows, with every primitive comparison
hypothesis instantiated. The threshold precedes the supplied open Hamilton
restriction; the maps, coefficient buffer and exact time precede all output
orders and tolerances. Every reference in the original admissible set remains
allowed after restricting the buffers. The only remaining differences are the
literal projected stress, retained Hamilton gradient and immersion.

The same smooth positive initial scalar is used for both immersions; in
particular `fun _ ↦ 1` is permitted. The fixed output cylinder and physical/
carrier compact sets support the forward, inverse, scalar and literal density
footpoint estimates simultaneously. The compact range and positive scalar PDE
are `Chart.densityFootpoint_spec` and `Chart.scalar_spec` for these very charts.
This does not assert the parent's final immersion-only estimate.
Source: `app:ch_waves:thm:leading`, `app:ch_background:prop:bg-frame`,
`app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_restricted_positive_family_dependence {n N : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {KF : Set (Euclidean n)} (hKF : IsCompact KF) (hKFU : KF ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ KF)
    (C₀ : ℝ) {κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (z : Euclidean 3) (hz : z ∈ parameterCube P.radius) :
    ∃ row col : Fin n, ∃ η M g : ℝ, 0 < η ∧ 0 < M ∧ 0 < g ∧
      ∀ O : Set (Euclidean n × Euclidean 3), IsOpen O → ((0 : Euclidean n), z) ∈ O →
      ∃ Ω : Set (Euclidean n × Euclidean 3), ∃ ρ R τ : ℝ,
        IsOpen Ω ∧ 0 < ρ ∧ 0 < R ∧ 0 < τ ∧
        τ = existenceTime R (liftedLowBound T M) / 4 ∧ τ ≤ R / 16 ∧
        Ω ⊆ O ∧
        Ω ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior KF) ×ˢ
          parameterInterior (3 * P.radius / 2) ∧
        closedBall ((0 : Euclidean n), z) ρ ⊆ Ω ∧
        MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) ρ)
          (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
        MapsTo (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
          (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z)) R)
          (closedBall ((0 : Euclidean n), z) ρ) ∧
        ∃ χ : ∀ F : Euclidean n → Euclidean N,
          F ∈ admissibleImmersions U KF C₀ κmet κnormal η →
          Chart T Ω (closedBall ((0 : Euclidean n), z) ρ)
            ((0 : Euclidean (n - 1)), z) R M τ row col F,
          (∀ F hF, ∀ w ∈ Ω, g ≤ |carrierAdaptedDenominator T (χ F hF).Q row col w| ∧
            |(carrierAdaptedDenominator T (χ F hF).Q row col w)⁻¹| ≤ g⁻¹) ∧
          ∀ (Kphysical : Set (Euclidean n × Euclidean 3))
            (Kcarrier : Set (Euclidean n × ContinuumRow.CarrierParameter)),
            IsCompact Kphysical → IsCompact Kcarrier →
            MapsTo (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)) Kphysical
              (outputCylinder ((0 : Euclidean (n - 1)), z) R τ) →
            MapsTo (densityCoordinates T) Kcarrier
              (outputCylinder ((0 : Euclidean (n - 1)), z) R τ) →
            ∀ (F₀ : Euclidean n → Euclidean N)
              (hF₀ : F₀ ∈ admissibleImmersions U KF C₀ κmet κnormal η)
              (initial : Euclidean (n - 1) × Euclidean 3 → ℝ),
              ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n - 1)), z) (R / 8)) →
              (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), 0 < initial p) →
              ∀ m : ℕ, ∀ ε > 0, ∃ δ > 0,
              ∀ (F : Euclidean n → Euclidean N)
                (hF : F ∈ admissibleImmersions U KF C₀ κmet κnormal η),
                cNorm KF (m + 1) (projectedStress F - projectedStress F₀) +
                  cNorm (closedBall ((0 : Euclidean n), z) ρ) (m + 1)
                    (fun w ↦ T.carrierGradient (χ F hF).Q w.1 w.2 -
                      T.carrierGradient (χ F₀ hF₀).Q w.1 w.2) +
                  cNorm KF (m + 2) (F - F₀) < δ →
                let c := χ F hF
                let c₀ := χ F₀ hF₀
                (∀ w ∈ Kphysical, 0 < c.scalar initial w) ∧
                (∀ w ∈ Kcarrier,
                  0 < c.scalar initial (w.1, ContinuumRow.CanonicalCarrier.parameter w.2)) ∧
                cNorm (outputCylinder ((0 : Euclidean (n - 1)), z) R τ) m
                    (c.forward - c₀.forward) +
                  cNorm (outputCylinder ((0 : Euclidean (n - 1)), z) R τ) m
                    (c.inverse - c₀.inverse) +
                  cNorm Kphysical m (c.scalar initial - c₀.scalar initial) +
                  cNorm Kcarrier m
                    ((fun w ↦ c.scalar initial (w.1, ContinuumRow.CanonicalCarrier.parameter w.2)) -
                      (fun w ↦ c₀.scalar initial (w.1, ContinuumRow.CanonicalCarrier.parameter w.2))) +
                  cNorm Kcarrier m
                    (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse) < ε := by
  classical
  obtain ⟨row, col, η, M, g, hη, hM, hg, hrestrict⟩ :=
    exists_restricted_positive_charts (N := N) hn hP T hKF hKFU hball C₀ hκmet hκnormal z hz
  refine ⟨row, col, η, M, g, hη, hM, hg, ?_⟩
  intro O hO hzO
  obtain ⟨Ω, ρ, R, τ, hΩ, hρ, hR, hτ, hτeq, hτR, hΩO, hΩphys, hKΩ, hx, hbuffer, hcharts⟩ :=
    hrestrict O hO hzO
  have hbuild (F : Euclidean n → Euclidean N)
      (hF : F ∈ admissibleImmersions U KF C₀ κmet κnormal η) :=
    hcharts F hF.1 hF.2.1 hF.2.2.1 hF.2.2.2.1 hF.2.2.2.2.1 hF.2.2.2.2.2.1 hF.2.2.2.2.2.2
  choose χ hgap using hbuild
  refine ⟨Ω, ρ, R, τ, hΩ, hρ, hR, hτ, hτeq, hτR, hΩO, hΩphys, hKΩ, hx, hbuffer,
    χ, hgap, ?_⟩
  intro Kphysical Kcarrier hKphysical hKcarrier hphysical hcarrier F₀ hF₀ initial hi hipos m ε hε
  have hKU : closedBall ((0 : Euclidean n), z) ρ ⊆ CoefficientBounds.inputDomain T := by
    intro w hw
    have hh := hΩphys (hKΩ hw)
    exact ⟨⟨hKFU (interior_subset hh.1.2), hh.1.1⟩,
      fun i ↦ (hh.2 i).trans (by linarith [hP.1])⟩
  obtain ⟨δ, hδ, hcompare⟩ := (χ F₀ hF₀).exists_primitive_transport_sub_tolerance
    hP hΩ (isCompact_closedBall _ _) hKΩ hR hM.le hbuffer hτeq hKF hKFU
    hKU (fun _ hw ↦ hball (hx hw)) hKphysical hKcarrier hphysical hcarrier
    hF₀.1 hF₀.2.1 initial hi hipos m hε
  refine ⟨δ, hδ, ?_⟩
  intro F hF hsmall
  apply hcompare F (χ F hF) hF.1
  simpa only [(χ F hF).frame_eq, (χ F₀ hF₀).frame_eq] using hsmall

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction
