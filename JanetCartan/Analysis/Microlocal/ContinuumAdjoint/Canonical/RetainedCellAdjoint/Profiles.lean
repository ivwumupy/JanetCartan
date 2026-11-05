module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.RetainedCellAdjoint.Buffers
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.RetainedLeading.NormalProfiles

/-!
# Complete-normal profiles on the original retained cell

Transfer the reserve-fourteen full-normal bound on the original compact `J`
through the fixed carrier graph. The scalar norm set `Kinitial` is arbitrary
and unchanged. The cap precedes all mask choices and source budgets; every
smaller literal canonical mask is allowed.

Consumer: the uniform scalar endpoint for `app:ch_background:prop:bg-adjoint`.
The analytic inputs are exactly those of `RetainedCover.Finite` and
`RetainedCover.History`, via `app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumAdjoint.Canonical.RetainedCellAdjoint
open ContinuumRow PhaseExtension AmplitudeProfiles RetainedLeading LeadingPrimitive
open ActualCarriers FrozenMenu CurrentFullPhase DerivativeKernels ProjectedStressFrame
open NullTransport ActualFlow FlowAmplitude LeadingWave.FullModulation

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The full-normal smoothness, exact scalar compatibility and reserve-fourteen
jets on the original compact set produce the complete component profiles for
ANY canonical masks below one fixed cap. No carrier-normal, normalized-jet or
operator estimate is assumed. In particular the incidence root and the center
of `J` or `Kinitial` need not coincide (`bg-adjoint`, `joint-tame`). -/
theorem exists_retained_cell_normal_profiles {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (Kinitial : Set (Euclidean (n - 1) × Euclidean 3))
    {J : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))} (hJ : IsCompact J)
    (E : Set (Euclidean n × CarrierParameter)) (hE : IsOpen E)
    (hgraph : MapsTo (carrierGraph T) E J)
    (z : Euclidean 3) (hz : z ∈ parameterCube P.radius)
    (hcenter : chartCenter z ∈ E) :
    ∃ cap > (0 : ℝ), ∀ {a : ℝ} (ha : 0 < a), a < cap →
    ∀ (Bfull : ℕ → ℝ), (∀ j, 0 < Bfull j) →
    ∀ {MF Mr κmet κ : ℝ}, 0 ≤ MF → 0 ≤ Mr → 0 < κmet → 0 < κ →
    ∀ s : ℕ, ∃ C₀ : Fin n → ℕ → ℝ, (∀ j i, 0 ≤ C₀ j i) ∧
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (F : Euclidean n → Euclidean N) (row col : Fin n)
        (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (O : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
        (Vcomp : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))),
      Q.1 = projectedStress F → ContDiffOn ℝ ∞ F U → IsImmersionOn F U →
      HasFullNormalRankOn F U → cNorm K (2*(n+1)+14) F ≤ MF →
      cNorm Kinitial (2*(n+1)+14) initial ≤ Mr →
      (∀ x ∈ K, ∀ v, κmet * ‖v‖^2 ≤ ‖fderiv ℝ F x v‖^2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      IsOpen O → MapsTo Prod.fst O U → O ⊆ domain T → J ⊆ O →
      MapsTo (carrierGraph T) E O →
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        coordinates (adaptedCoordinates T.data.adapted) (p.1, CanonicalCarrier.parameter p.2))
        E Vcomp →
      ContDiffOn ℝ ∞
        (fun w ↦ scalarAmplitude T Q F row col Φ Y initial w • nullvector T Q col w) O →
      (∀ q ∈ Vcomp,
        let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
        scalarAmplitude T Q F row col Φ Y initial
            (w.1, (w.2, T.reference.spatialPatch w.2)) =
          carrierScalarAmplitude T Q F row col φ y initial w) →
      (∀ j, cNorm J j (fullNormal T Q F row col Φ Y initial) ≤
        Bfull j * (1 + cNorm K (j+14) F + cNorm Kinitial (j+14) initial)) →
      let ν := extendedRetainedNormal T Q F row col φ y initial z ha
      ContDiff ℝ ∞ ν ∧
      ∀ (hcell : 4 * a < 1 / 2) (angular : CarrierParameter → Euclidean (n - 1) → ℝ)
        (high : ℝ → ℝ),
      let d := CanonicalCarrier.data T Q F row col φ y initial ha hcell angular high
      (∀ j, ContDiff ℝ ∞ (carrierChartGeometryComponent d (FixedCutoffs.physical ha 1) ν j)) ∧
      ∀ H : ℝ, 1 + cNorm K (s+2*(n+1)+14) F + cNorm Kinitial (s+2*(n+1)+14) initial ≤ H →
      ∀ j p, ∀ i ≤ s+2*(n+1),
        ‖iteratedFDeriv ℝ i (carrierChartGeometryComponent d (FixedCutoffs.physical ha 1) ν j) p‖ ≤
          C₀ j i * H ^ (((i-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ)) := by
  obtain ⟨ρ, σ, hρ, hσ, hx, hc, hmap, hbuffer⟩ :=
    exists_normal_buffers_in_retained_cell T hP hKU hball z hz E hE hcenter
  let D : ContinuumNormalReduction.TransportSymbol.PrimitiveNormChart
      (Euclidean n × CarrierParameter) :=
    ⟨chartCenter z, σ, hσ, ball (chartCenter z) (2*σ), isOpen_ball,
      closedBall_subset_ball (by linarith)⟩
  have hparameter : D.region ⊆ univ ×ˢ
      (CanonicalCarrier.parameter ⁻¹' parameterInterior (2 * P.radius)) :=
    fun p hp ↦ ⟨mem_univ _, (hc (hmap (x := p) hp)).2⟩
  obtain ⟨Apull, hApull, hpull⟩ := exists_normalField_pullback_bounds T (N := N) hP
    D hparameter hJ (fun p hp ↦ hgraph (hbuffer (D.ball_subset hp)))
  refine ⟨σ/12, by positivity, ?_⟩
  intro a ha hacap Bfull hBfull MF Mr κmet κ hMF hMr hκmet hκ s
  obtain ⟨C₀, hC₀, hprofiles⟩ := exists_extendedRetainedNormal_profiles T (N := N)
    hP hK hKU hball Kinitial z hρ hσ ha (by linarith) hx hc hmap
    (fun j ↦ Apull j * Bfull j) (fun j ↦ mul_pos (hApull j) (hBfull j))
    hMF hMr hκmet hκ s
  refine ⟨C₀, hC₀, ?_⟩
  intro Q F row col φ y Φ Y initial O Vcomp hQ hF hi hrank hFM hIM hmet hnormal
    hO hOU hOdom hJO hgraphO hcompE hnull hcomp hfull
  obtain ⟨hν, hνB⟩ := hpull Q F row col Φ Y φ y initial O Vcomp
    hO hOU hOdom hJO (fun _ hp ↦ hgraphO (hbuffer hp))
    (fun _ hp ↦ hcompE (hbuffer hp)) hF hi hrank hnull hcomp
  apply hprofiles Q F row col φ y initial hQ hF hi hrank hFM hIM hmet hnormal hν
  intro j
  exact ((hνB j).trans (mul_le_mul_of_nonneg_left (hfull j) (hApull j).le)).trans_eq
    (mul_assoc _ _ _).symm

end JanetCartan.ContinuumAdjoint.Canonical.RetainedCellAdjoint
