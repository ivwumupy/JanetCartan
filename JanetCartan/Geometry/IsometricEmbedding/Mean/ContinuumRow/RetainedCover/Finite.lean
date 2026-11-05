module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.FullModulationConstruction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingCarrier.Buffers
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Density
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PhaseAssembly.Buffers

/-!
# Retained compatible carrier cover before geometry

For the continuum row (`app:ch_background:defn:bg-row`, `bg-T`), choose the
carrier neighborhoods inside the SAME local full-modulation witnesses before
selecting a finite subcover. The intersection with the original graph balls
also preserves the original full-parameter cover. All choices precede the
geometric gaps, immersion budgets and initial-scalar budgets
(`new:sec:order-of-choices` in paper-v2.tex).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.CurrentCoefficientProfiles
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase FlowAmplitude
open ProjectedStressFrame AmbientResponse ResponseTransfer
open LeadingWave LeadingWave.FullModulation LeadingWave.FullModulation.CarrierCompatibility
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.LeadingPrimitive ContinuumRow.LeadingCarrier
open FullPhaseCharts.ActualComparison

/-- Strengthen the finite leading constructor by retaining open carrier cells
inside both the joint-estimate ball and the original compatibility cylinder.
The cells cover every frozen parameter and retain the field, phase and detector
domains needed by `LeadingPrimitive.exists_primitive_controls_of_jointLeading`.
All original flow, scalar and reconstruction conclusions, including reserve
fourteen, concern these same witnesses (`app:ch_waves:thm:leading`,
`app:ch_waves:eq:joint-tame`, `app:ch_background:defn:bg-row`). The coefficient
domains, compact buffers and exact carrier existence times precede budgets;
their primitive evidence supplies `PositiveReference.FlowConstruction.Chart`
on these selected centers for `app:ch_osc:prop:osc-normal`, Step 4' in paper-v2.tex.
The original scalar-estimate, coefficient and source-covector working-ball
containments are retained before budgets for the correction on these same
covering cells (`app:ch_waves:eq:primary-algebraic-correction`,
`app:ch_waves:eq:WKB-grading`, `app:ch_waves:thm:individual`).
The comparison bound `8 * rcomp ≤ Rc / 32` is retained from
`CarrierCompatibility.exists_comparison_radii` before budgets and finite selection.
It supplies `RetainedRowGeometry.exists_original_outputCylinder_region` on these
same witnesses (`app:ch_background:eq:bg-Psi`, `app:ch_background:prop:bg-frame`,
paper-v2.tex `app:ch_osc:prop:osc-normal`, Step 4').
The same selection also retains source contraction of the carrier domain,
its doubled frozen-minor buffers, and the full-modulation direction bound,
adapted buffer and exact existence time. These supply the common initializer
and `NormalizedChartFamily.exists_finite_source_charts_with_lifts`, the
normalized carrier baseline, and the original-cylinder full-flow profiles
for `app:ch_background:prop:bg-normalized`; no new cells are selected. -/
theorem exists_finite_retained_leading_family_before_geometry_with_source_geometry {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
 :
    ∃ η ε : ℝ, 0 < η ∧ 0 < ε ∧
      ∃ centers : Finset (parameterCube P.radius),
      ∃ row col : centers → Fin n,
      ∃ ρ R τ Rc τc Mc rcomp δcomp σ : centers → ℝ,
        (∀ j, 8 * rcomp j ≤ Rc j / 32) ∧
        (∀ j, 0 < ρ j ∧ 0 < R j ∧ 0 < τ j ∧ 0 < Rc j ∧ 0 < τc j ∧
          0 < Mc j ∧ 0 < rcomp j ∧ 0 < δcomp j ∧ 0 < σ j) ∧
        ∃ Ωc : centers → Set (Euclidean n × Euclidean 3),
        ∃ ρc Bc gc μc Bfull : centers → ℝ,
          (∀ j : centers, let z₀ := j.1.1
            0 < μc j ∧
            (∀ s ∈ Ioc (0 : ℝ) 1,
              MapsTo (fun w : Euclidean n × Euclidean 3 ↦ (s • w.1, w.2)) (Ωc j) (Ωc j)) ∧
            closedBall ((0 : Euclidean n), z₀) (2 * ρc j) ⊆ Ωc j ∧
            closedBall ((0 : Euclidean n), z₀) (2 * ρc j) ⊆
              (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
                parameterInterior (3 * P.radius / 2) ∧
            MapsTo Prod.fst (closedBall ((0 : Euclidean n), z₀) (2 * ρc j))
              (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
            ∀ w ∈ closedBall ((0 : Euclidean n), z₀) (2 * ρc j),
              2 * μc j ≤ |(cubePencil (P.toFun w.2)).adjugate (row j) (col j)|) ∧
          (∀ j : centers, let z₀ := j.1.1
            let a := ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀))
            0 < Bfull j ∧
            τ j = existenceTime (R j) (LeadingWave.FullModulation.liftedLowBound T (Bfull j)) / 4 ∧
            τ j ≤ R j / 16 ∧
            MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
              (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)),
                (z₀, T.reference.spatialPatch z₀))) (R j)) (closedBall a (ρ j))) ∧
          (∀ j : centers, let z₀ := j.1.1
            let Ωc := Ωc j
            let ρc := ρc j
            let Bc := Bc j
            let gc := gc j
            let Rc := Rc j
            let τc := τc j
            (0 < ρc ∧ 0 < Bc ∧ 0 < gc ∧ IsOpen Ωc ∧
              closedBall ((0 : Euclidean n), z₀) ρc ⊆ Ωc ∧
              Ωc ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
                parameterInterior (3 * P.radius / 2) ∧
              MapsTo Prod.fst (closedBall ((0 : Euclidean n), z₀) ρc)
                (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
              MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
                (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z₀)) Rc)
                (closedBall ((0 : Euclidean n), z₀) ρc) ∧
              τc = existenceTime Rc (NullTransport.ActualFlow.liftedLowBound T Bc) / 4 ∧
              τc ≤ Rc / 16)) ∧
        (∀ j : centers, let z₀ := j.1.1
          let a := ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀))
          closedBall a (2 * σ j) ⊆
            (coordinates (adaptedCoordinates T.data.adapted)).symm ''
              (Icc (-τ j / 2) (τ j / 2) ×ˢ
                closedBall ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀))
                  (R j / 64)) ∧
          closedBall a (2 * σ j) ⊆ closedBall a (ρ j) ∧
          ∀ w ∈ closedBall a (2 * σ j),
            w.2.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T)
              (min T.family.radius (3 * T.family.sourceRadius))) ∧
        ∃ εcarrier ρdet : centers → ℝ,
          (∀ j, 0 < εcarrier j ∧ 0 < ρdet j ∧
            let z := j.1.1
            let cell := ball (0 : Euclidean n) (εcarrier j) ×ˢ
              ball (z 0, spectatorCenter z) (εcarrier j)
            let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)
            MapsTo (carrierGraph T) cell
              (ball ((0 : Euclidean n), (z, T.reference.spatialPatch z)) (σ j)) ∧
            MapsTo (fun p ↦ coordinates (adaptedCoordinates T.data.adapted) (ψ p)) cell
              (Ioo (-δcomp j) (δcomp j) ×ˢ ball ((0 : Euclidean (n - 1)), z) (rcomp j)) ∧
            cell ⊆ (U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
              (parameter ⁻¹' parameterInterior (2 * P.radius)) ∧
            cell ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
              (parameter ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
            MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) (ρdet j))
              (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
            closedBall ((0 : Euclidean n), z) (ρdet j) ⊆
              ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius) ∧
            MapsTo ψ cell (closedBall ((0 : Euclidean n), z) (ρdet j))) ∧
          (∀ z ∈ parameterCube P.radius, ∃ j : centers,
            ((0 : Euclidean n), (z 0, spectatorCenter z)) ∈
              ball (0 : Euclidean n) (εcarrier j) ×ˢ
                ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier j)) ∧
        ∃ V : Set (Euclidean 3 × Euclidean (n - 1)),
          IsOpen V ∧ (∀ z ∈ parameterCube P.radius, (z, T.reference.spatialPatch z) ∈ V) ∧
          (ball (0 : Euclidean n) ε ×ˢ V ⊆
            ⋃ j : centers, closedBall ((0 : Euclidean n),
              (j.1.1, T.reference.spatialPatch j.1.1)) (σ j)) ∧
      ∀ M Mᵣ κmet κnormal m : ℝ, 0 ≤ M → 0 ≤ Mᵣ →
        0 < κmet → 0 < κnormal → 0 < m →
      ∃ c : ℝ, ∃ E : ℕ → ℝ, ∃ A H B : centers → ℕ → ℝ,
        0 < c ∧ (∀ j, 0 < E j) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 14 F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ j : centers,
        let z₀ := j.1.1
        let Ωc := Ωc j
        let ρc := ρc j
        let Bc := Bc j
        let gc := gc j
        let row := row j
        let col := col j
        let ρ := ρ j
        let R := R j
        let τ := τ j
        let Rc := Rc j
        let τc := τc j
        let Mc := Mc j
        let rcomp := rcomp j
        let δcomp := δcomp j
        let σ := σ j
        let A := A j
        let H := H j
        let B := B j
        let g := c
        let b := c
        let cν := c
        let a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
          (0, (z₀, T.reference.spatialPatch z₀))
        let Ω := ball a (2 * ρ)
        closedBall a (2 * ρ) ⊆ domain T ∧
        MapsTo Prod.fst (closedBall a (2 * ρ))
          (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
            (ball (0 : Euclidean n) T.physicalRadius ∩ interior K)) ∧
        let e := adaptedCoordinates T.data.adapted
        let Cc := coordinates (Z := Euclidean 3) e
        let pc := ((0 : Euclidean (n - 1)), z₀)
        cNorm (closedBall a ρ) 1 (transportDirection T Q row col) ≤ Bfull j ∧
        ∃ Dc : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        ∃ φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
          (ContDiffOn ℝ ∞ (carrierNullvector T Q col) Ωc ∧
            ContDiffOn ℝ ∞ (carrierConullvector T Q row) Ωc ∧
            ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ωc ∧
            ContDiffOn ℝ ∞ (carrierTransportPotential T Q F row col) Ωc ∧
            cNorm (closedBall ((0 : Euclidean n), z₀) ρc) 1
              (carrierTransportDirection T Q row col) ≤ Bc ∧
            (∀ w ∈ Ωc, ∀ i, (Q.1 w.1 i).IsSymm) ∧
            (∀ w ∈ Ωc,
              carrierNullvector T Q col w ≠ 0 ∧ carrierConullvector T Q row w ≠ 0 ∧
              reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
                (fun j ↦ carrierNullvector T Q col w j) = 0 ∧
              carrierConullvector T Q row w ᵥ*
                reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
              gc ≤ |carrierAdaptedDenominator T Q row col w| ∧
              carrierAdaptedDenominator T Q row col w ≠ 0 ∧
              |(carrierAdaptedDenominator T Q row col w)⁻¹| ≤ gc⁻¹) ∧
            Dc = (fun q ↦ (q.1, φ q)) ''
              (Ioo (-τc) τc ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8)) ∧
            Dc ⊆ Cc.symm ⁻¹' Ωc ∧ Cc ⁻¹' Dc ⊆ Ωc ∧
            Cc ⁻¹' Dc ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
              parameterInterior (3 * P.radius / 2) ∧
            ContDiffOn ℝ ∞ φ
              (Ioo (-τc) τc ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8)) ∧
            ContDiffOn ℝ ∞ y Dc ∧
            (∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8),
              ∀ t ∈ Ioo (-τc) τc, (φ (t, p)).2 = p.2) ∧
            (∀ q ∈ Dc, (y q).2 = q.2.2) ∧
            ContDiffOn ℝ ∞ y (Ioo (-(2 * τc)) (2 * τc) ×ˢ
              ball ((0 : Euclidean (n - 1)), z₀) (Rc / 4))) ∧
          IsOpen Dc ∧ Ioo (-τc) τc ×ˢ ball pc (Rc / 32) ⊆ Dc ∧
          Dc ⊆ Ioo (-τc) τc ×ˢ ball pc (Rc / 4) ∧
          MapsTo (fun q ↦ (q.1, φ q)) (Ioo (-τc) τc ×ˢ ball pc (Rc / 8)) Dc ∧
          MapsTo (fun q ↦ (q.1, y q)) Dc (Ioo (-τc) τc ×ˢ ball pc (Rc / 8)) ∧
          (∀ p ∈ ball pc (Rc / 8), φ (0, p) = p) ∧
          (∀ p ∈ ball pc (Rc / 8), ∀ t ∈ Ioo (-τc) τc, y (t, φ (t, p)) = p) ∧
          (∀ q ∈ Dc, φ (q.1, y q) = q.2) ∧
          (∀ p ∈ ball pc (Rc / 8), ∀ t ∈ Ioo (-τc) τc, HasDerivAt (fun s ↦ φ (s, p))
            ((e (carrierTransportDirection T Q row col (Cc.symm (t, φ (t, p))))).2, 0) t) ∧
          ContDiffOn ℝ ∞ φ (Ioo (-(2 * τc)) (2 * τc) ×ˢ ball pc (Rc / 4)) ∧
          cNorm (Icc (-τc) τc ×ˢ closedBall pc (Rc / 8)) 1 φ ≤ Mc ∧
      let p₀ := ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀))
      let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1))
        (adaptedCoordinates T.data.adapted)
      let Bρ := closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) ρ
      let I := Ioo (-τ) τ
      let L := ball p₀ (R / 8)
      let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
      let W := C.symm '' (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64))
      ∃ D : Set (ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))),
      ∃ Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
        Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)),
        IsOpen D ∧ I ×ˢ ball p₀ (R / 32) ⊆ D ∧ D ⊆ I ×ˢ ball p₀ (R / 4) ∧
        C ⁻¹' D ⊆ Ω ∧
        closedBall a (2 * σ) ⊆ C ⁻¹' D ∧
        (∀ (y : Euclidean (n - 1)) (z : Euclidean 3) (ζ : Euclidean (n - 1)),
          (T.data.adapted.embedding y, (z, ζ)) ∈ closedBall a (2 * σ) →
          phase T Q (T.data.adapted.embedding y) ζ = inner ℝ y ζ) ∧
        ContDiffOn ℝ ∞ Φ (I ×ˢ L) ∧ ContDiffOn ℝ ∞ Y D ∧
        MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ L) D ∧
        MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ L) ∧
        (∀ p ∈ L, Φ (0, p) = p) ∧
        (∀ p ∈ L, ∀ t ∈ I, Y (t, Φ (t, p)) = p) ∧
        (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
        (∀ p ∈ L, ∀ t ∈ I, (Φ (t, p)).2.1 = p.2.1 ∧ (Φ (t, p)).2.2 = p.2.2) ∧
        (∀ q ∈ D, (Y q).2.1 = q.2.2.1 ∧ (Y q).2.2 = q.2.2.2) ∧
        (∀ p ∈ L, ∀ t ∈ I, HasDerivAt (fun s ↦ Φ (s, p))
          ((adaptedCoordinates T.data.adapted
            (transportDirection T Q row col (C.symm (t, Φ (t, p))))).2, 0) t) ∧
        ContDiffOn ℝ ∞ Φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
        ContDiffOn ℝ ∞ Y (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
        (∀ j, cNorm J j Φ + cNorm J j Y ≤ H j * (1 + cNorm K (j + 5) F)) ∧
        (∀ w ∈ C ⁻¹' D,
          b ≤ ‖nullvector T Q col w‖ ∧ b ≤ ‖phaseGradient T Q w.1 w.2.2‖ ∧
          reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
            (fun i ↦ nullvector T Q col w i) = 0 ∧
          conullvector T Q row w ᵥ*
            reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) = 0) ∧
        (∀ j, cNorm Bρ j (nullvector T Q col) +
          cNorm Bρ j (conullvector T Q row) +
          cNorm Bρ j (adaptedDenominator T Q row col) +
          cNorm Bρ j (fun w ↦ (adaptedDenominator T Q row col w)⁻¹) +
          cNorm Bρ j (transportDirection T Q row col) +
          cNorm Bρ j (transportPotential T Q F row col) ≤ A j * (1 + cNorm K (j + 5) F)) ∧
        (∀ q ∈ Ioo (-δcomp) δcomp ×ˢ ball pc rcomp,
          q ∈ Dc ∧ (q.1, carrierLabel T q.2) ∈ D ∧
          (∀ t ∈ Ioo (-δcomp) δcomp,
            Φ (t, carrierLabel T (y q)) = carrierLabel T (φ (t, y q))) ∧
          Y (q.1, carrierLabel T q.2) = carrierLabel T (y q) ∧
          ∀ initial : Euclidean (n - 1) × Euclidean 3 → ℝ,
            let w := Cc.symm q
            scalarAmplitude T Q F row col Φ Y initial
                (w.1, (w.2, T.reference.spatialPatch w.2)) =
              carrierScalarAmplitude T Q F row col φ y initial w ∧
            scalarAmplitude T Q F row col Φ Y initial
                (w.1, (w.2, T.reference.spatialPatch w.2)) •
                nullvector T Q col (w.1, (w.2, T.reference.spatialPatch w.2)) =
              carrierScalarAmplitude T Q F row col φ y initial w • carrierNullvector T Q col w) ∧
        ∀ r : Euclidean (n - 1) × Euclidean 3 → ℝ,
          ContDiffOn ℝ ∞ r (ball ((0 : Euclidean (n - 1)), z₀) (R / 4)) →
          cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) 14 r ≤ Mᵣ →
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8), m ≤ r p) →
          let α := scalarAmplitude T Q F row col Φ Y r
          ContDiffOn ℝ ∞ α (C ⁻¹' D) ∧
          ContDiffOn ℝ ∞ (fun w ↦ α w • nullvector T Q col w) (C ⁻¹' D) ∧
          (∀ p ∈ L, α (T.data.adapted.embedding p.1, p.2) = r (p.1, p.2.1)) ∧
          (∀ w ∈ C ⁻¹' D, g ≤ α w ∧ 0 < α w ∧
            nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0 ∧
            α w • nullvector T Q col w ≠ 0) ∧
          (∀ w ∈ C ⁻¹' D,
            fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (transportDirection T Q row col w) +
              transportPotential T Q F row col w * α w = 0) ∧
          (∀ w ∈ C ⁻¹' D,
            reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
              (fun j ↦ (α w • nullvector T Q col w) j) = 0) ∧
          (∀ w ∈ C ⁻¹' D, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
            (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1 = 0) ∧
          (∀ j, cNorm W j α + cNorm W j (fun w ↦ α w • nullvector T Q col w) ≤
            B j * (1 + cNorm K (j + 13) F +
              cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 13) r)) ∧
              (∀ w ∈ C ⁻¹' D,
                cν ≤ ‖principalNormal (canonicalNormalCompletion F w.1)
                  (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)‖ ∧
                determinant (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) = 0 ∧
                (1 / 2 : ℝ) • linearizedMetric F
                    (reconstruction F (canonicalNormalCompletion F) (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2))) w.1 =
                  stressProjection F w.1 (symmCovariantDeriv F (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1) ∧
                (∀ τ' : ℝ, τ' ≠ 0 →
                  completedVariationComplex F
                    (fun x ↦ (τ' : ℂ) ^ 2 •
                      Complex.exp (Complex.I * (phase T Q x w.2.2 : ℂ) / (τ' : ℂ)) •
                        euclideanComplexInclusion (α (x, w.2) • nullvector T Q col (x, w.2))) 0 w.1 =
                    Complex.exp (Complex.I * (phase T Q w.1 w.2.2 : ℂ) / (τ' : ℂ)) •
                      ((Complex.I * (τ' : ℂ)) • euclideanComplexInclusion
                        (principalNormal (canonicalNormalCompletion F w.1)
                          (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)) +
                      (τ' : ℂ) ^ 2 • euclideanComplexInclusion
                        (reconstruction F (canonicalNormalCompletion F) (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1))) ∧
                hermitianTensor ((principalMatrix
                    (principalNormal (canonicalNormalCompletion F w.1)
                      (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w))
                    (phaseGradient T Q w.1 w.2.2)).map Complex.ofReal) =
                  fun i j ↦ ‖principalNormal (canonicalNormalCompletion F w.1)
                    (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)‖ ^ 2 *
                      phaseGradient T Q w.1 w.2.2 i * phaseGradient T Q w.1 w.2.2 j) ∧
          let J₀ := closedBall a σ
          let b₀ := fun w ↦ α w • nullvector T Q col w
          let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
            phaseGradient T Q w.1 w.2.2
          let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
          let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
          ∀ j, cNorm J₀ j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J₀ j b₀ +
            cNorm J₀ j ν + cNorm J₀ j V + cNorm J₀ j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
              E j * (1 + cNorm K (j + 14) F +
                cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r) := by
  classical
  choose row col ρ R η τ b Rc τc Mc rcomp δcomp σ Ωc ρc Bc gc μc Bfull
    hsource hBfull hτeq hrc hρ hR hη hτ hb hRc hτc hMc hrcomp hδcomp hσ hτR
    hdom hx hbuffer hgeometryc hworking hlocal using
    fun z : parameterCube P.radius ↦ exists_full_joint_leading_wave_before_geometry_with_source_geometry
      hn hP T hK hKU hball z.1 z.2
  choose εcarrier hεcarrier ρdet hρdet hcell using
    fun z : parameterCube P.radius ↦ exists_leading_carrier_buffers hP T hKU hball
      z.1 z.2 (hσ z) (hrcomp z) (hδcomp z)
  let carrier := fun z : Euclidean 3 ↦ (z 0, spectatorCenter z)
  have hcarrier : Continuous carrier := by
    dsimp [carrier, spectatorCenter]
    fun_prop
  let graph := fun z : Euclidean 3 ↦ (z, T.reference.spatialPatch z)
  have hgraph : ContinuousOn graph (parameterCube P.radius) :=
    continuousOn_id.prodMk ((T.reference.spatialPatch_smooth hP).continuousOn.mono
      (parameterCube_subset_doubledInterior hP.1))
  -- Select using the compatibility cells themselves, together with the
  -- original graph neighborhoods; no later shrinking of a finite cover occurs.
  let Osub := fun z : parameterCube P.radius ↦
    (fun q : parameterCube P.radius ↦ graph q.1) ⁻¹' ball (graph z.1) (σ z / 2) ∩
    (fun q : parameterCube P.radius ↦ carrier q.1) ⁻¹' ball (carrier z.1) (εcarrier z)
  have hOsub (z) : IsOpen (Osub z) :=
    (isOpen_ball.preimage hgraph.domRestrict).inter
      (isOpen_ball.preimage (hcarrier.comp continuous_subtype_val))
  have hcoverSub : (univ : Set (parameterCube P.radius)) ⊆ ⋃ z, Osub z := by
    intro z _
    exact mem_iUnion.mpr ⟨z, mem_ball_self (half_pos (hσ z)), mem_ball_self (hεcarrier z)⟩
  let : CompactSpace (parameterCube P.radius) := isCompact_iff_compactSpace.mp
    (isCompact_parameterCube P.radius)
  obtain ⟨centers, hcenters⟩ := isCompact_univ.elim_finite_subcover Osub hOsub hcoverSub
  obtain ⟨ε, d, _, hε, _, hd, _, hcommon⟩ := exists_common_phase_buffers
    (fun j : centers ↦ σ j.1 / 2)
    (fun j : centers ↦ η j.1)
    (fun _ ↦ 0) (fun j ↦ half_pos (hσ j.1)) (fun j ↦ hη j.1)
  let V := ⋃ j : centers, ball (graph j.1.1) (σ j.1 / 2)
  refine ⟨min d T.family.threshold, ε,
    lt_min hd T.family.threshold_pos, hε, centers,
    (fun j ↦ row j.1), (fun j ↦ col j.1),
    (fun j ↦ ρ j.1), (fun j ↦ R j.1), (fun j ↦ τ j.1),
    (fun j ↦ Rc j.1), (fun j ↦ τc j.1), (fun j ↦ Mc j.1),
    (fun j ↦ rcomp j.1), (fun j ↦ δcomp j.1), (fun j ↦ σ j.1),
    (fun j ↦ hrc j.1),
    (fun j ↦ ⟨hρ j.1, hR j.1, hτ j.1, hRc j.1, hτc j.1, hMc j.1,
      hrcomp j.1, hδcomp j.1, hσ j.1⟩),
    (fun j ↦ Ωc j.1), (fun j ↦ ρc j.1), (fun j ↦ Bc j.1), (fun j ↦ gc j.1),
    (fun j ↦ μc j.1), (fun j ↦ Bfull j.1), (fun j ↦ hsource j.1),
    (fun j ↦ ⟨hBfull j.1, hτeq j.1, hτR j.1, hbuffer j.1⟩),
    (fun j ↦ hgeometryc j.1), (fun j ↦ hworking j.1),
    (fun j ↦ εcarrier j.1), (fun j ↦ ρdet j.1),
    (fun j ↦ ⟨hεcarrier j.1, hρdet j.1, hcell j.1⟩), ?_,
    V, isOpen_iUnion (fun _ ↦ isOpen_ball), ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hcenters (mem_univ (⟨z, hz⟩ : parameterCube P.radius)))
    obtain ⟨hq', hzq⟩ := mem_iUnion.mp hq
    exact ⟨⟨q, hq'⟩, mem_ball_self (hεcarrier q), hzq.2⟩
  · intro z hz
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hcenters (mem_univ (⟨z, hz⟩ : parameterCube P.radius)))
    obtain ⟨hq', hzq⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨⟨q, hq'⟩, hzq.1⟩
  · rintro ⟨x, zf⟩ ⟨hx₀, hz⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    apply mem_iUnion.mpr ⟨j, ?_⟩
    rw [mem_closedBall, Prod.dist_eq, max_le_iff]
    have he : ε ≤ σ j.1 := by
      have hh := (hcommon j).1
      change 3 * ε < σ j.1 / 2 at hh
      linarith
    exact ⟨(mem_ball.mp hx₀).le.trans he,
      (mem_ball.mp hj).le.trans (by linarith [hσ j.1])⟩
  · intro M Mᵣ κmet κnormal m hM hMᵣ hκmet hκnormal hm
    choose g cν A H B E hg hcν hA hH hB hE hactual using
      fun j : centers ↦ hlocal j.1 M Mᵣ κmet κnormal m hM hMᵣ hκmet hκnormal hm
    obtain ⟨_, c, _, _, _, hc, _, hgapCommon⟩ := exists_common_phase_buffers
      (fun _ : centers ↦ (1 : ℝ))
      (fun j : centers ↦ min (g j) (min (b j.1) (cν j)))
      (fun _ ↦ 0) (fun _ ↦ by norm_num)
      (fun j ↦ lt_min (hg j) (lt_min (hb j.1) (hcν j)))
    let Emax := fun k ↦ 1 + ∑ j : centers, E j k
    have hEmax (k) : 0 < Emax k := by
      have hh : 0 ≤ ∑ j : centers, E j k := Finset.sum_nonneg (fun j _ ↦ (hE j k).le)
      change 0 < 1 + ∑ j : centers, E j k
      linarith
    have hEE (j : centers) (k) : E j k ≤ Emax k := by
      have hh := Finset.single_le_sum (f := fun i : centers ↦ E i k)
        (fun i _ ↦ (hE i k).le) (Finset.mem_univ j)
      change E j k ≤ 1 + ∑ i : centers, E i k
      linarith
    refine ⟨c, Emax, A, H, B, hc, hEmax, ?_⟩
    intro F hF hi hrank hFM hmet hnormal hclose
    have hframe := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
    have hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold := by
      apply (cNorm_mono_set_of_contDiffAt hball hK _).trans_lt
        (hclose.trans_le (min_le_right _ _))
      intro x hxK
      exact ((hframe.contDiffAt (hU.mem_nhds (hKU hxK))).sub contDiffAt_const).of_le (by simp)
    refine ⟨hlow, ?_⟩
    dsimp only
    intro j
    obtain ⟨hlowj, hdirLow, Dc, φ, y, hcarrierData, hDc, hcoverc, hbigc, hφDc, hyL, hφ₀, hyφ, hφy,
      hvelocityc, hφbuffer, hflowcLow, D, Φ, Y, hD, hcover, hbig, hphys, hballD, hphaseInitial,
      hΦ, hY, hΦD, hYL, hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity,
      hΦbuffer, hYbuffer, hflow, hgaps, hcoeff, hcompat, hsolution⟩ :=
      hactual j F hF hi hrank hFM hmet hnormal
        (hclose.trans_le ((min_le_left _ _).trans (hcommon j).2.1))
    have hcg : c ≤ g j := (hgapCommon j).2.1.trans (min_le_left _ _)
    have hcb : c ≤ b j.1 :=
      (hgapCommon j).2.1.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hcν' : c ≤ cν j :=
      (hgapCommon j).2.1.trans ((min_le_right _ _).trans (min_le_right _ _))
    refine ⟨hdom j.1, hx j.1, hdirLow, Dc, φ, y, hcarrierData, hDc, hcoverc, hbigc, hφDc, hyL, hφ₀, hyφ, hφy,
      hvelocityc, hφbuffer, hflowcLow, D, Φ, Y, hD, hcover, hbig, hphys, hballD, hphaseInitial,
      hΦ, hY, hΦD, hYL, hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity,
      hΦbuffer, hYbuffer, hflow, ?_, hcoeff, hcompat, ?_⟩
    · intro w hw
      exact ⟨hcb.trans (hgaps w hw).1, hcb.trans (hgaps w hw).2.1, (hgaps w hw).2.2⟩
    · intro r hr hrM hrmin
      obtain ⟨hα, hb₀, hinit, hpos, hpde, hsymbol, hreduce, habound, hidentity, hjoint⟩ :=
        hsolution r hr hrM hrmin
      refine ⟨hα, hb₀, hinit, (fun w hw ↦ ⟨hcg.trans (hpos w hw).1, (hpos w hw).2⟩),
        hpde, hsymbol, hreduce, habound,
        (fun w hw ↦ ⟨hcν'.trans (hidentity w hw).1, (hidentity w hw).2⟩), ?_⟩
      intro m
      exact (hjoint m).trans (mul_le_mul_of_nonneg_right (hEE j m)
        (by linarith [cNorm_nonneg K (m + 14) F,
          cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), j.1.1) (R j.1 / 8)) (m + 14) r]))

/-- Project the original comparison-radius constructor from the same finite
source-geometry selection, preserving all its witnesses and reserve-thirteen
and reserve-fourteen estimates (`app:ch_waves:thm:leading`,
`app:ch_waves:eq:joint-tame`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_finite_retained_leading_family_before_geometry_with_carrier_data_and_working_balls_and_comparison_radius {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
 :
    ∃ η ε : ℝ, 0 < η ∧ 0 < ε ∧
      ∃ centers : Finset (parameterCube P.radius),
      ∃ row col : centers → Fin n,
      ∃ ρ R τ Rc τc Mc rcomp δcomp σ : centers → ℝ,
        (∀ j, 8 * rcomp j ≤ Rc j / 32) ∧
        (∀ j, 0 < ρ j ∧ 0 < R j ∧ 0 < τ j ∧ 0 < Rc j ∧ 0 < τc j ∧
          0 < Mc j ∧ 0 < rcomp j ∧ 0 < δcomp j ∧ 0 < σ j) ∧
        ∃ Ωc : centers → Set (Euclidean n × Euclidean 3),
        ∃ ρc Bc gc : centers → ℝ,
          (∀ j : centers, let z₀ := j.1.1
            let Ωc := Ωc j
            let ρc := ρc j
            let Bc := Bc j
            let gc := gc j
            let Rc := Rc j
            let τc := τc j
            (0 < ρc ∧ 0 < Bc ∧ 0 < gc ∧ IsOpen Ωc ∧
              closedBall ((0 : Euclidean n), z₀) ρc ⊆ Ωc ∧
              Ωc ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
                parameterInterior (3 * P.radius / 2) ∧
              MapsTo Prod.fst (closedBall ((0 : Euclidean n), z₀) ρc)
                (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
              MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
                (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z₀)) Rc)
                (closedBall ((0 : Euclidean n), z₀) ρc) ∧
              τc = existenceTime Rc (NullTransport.ActualFlow.liftedLowBound T Bc) / 4 ∧
              τc ≤ Rc / 16)) ∧
        (∀ j : centers, let z₀ := j.1.1
          let a := ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀))
          closedBall a (2 * σ j) ⊆
            (coordinates (adaptedCoordinates T.data.adapted)).symm ''
              (Icc (-τ j / 2) (τ j / 2) ×ˢ
                closedBall ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀))
                  (R j / 64)) ∧
          closedBall a (2 * σ j) ⊆ closedBall a (ρ j) ∧
          ∀ w ∈ closedBall a (2 * σ j),
            w.2.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T)
              (min T.family.radius (3 * T.family.sourceRadius))) ∧
        ∃ εcarrier ρdet : centers → ℝ,
          (∀ j, 0 < εcarrier j ∧ 0 < ρdet j ∧
            let z := j.1.1
            let cell := ball (0 : Euclidean n) (εcarrier j) ×ˢ
              ball (z 0, spectatorCenter z) (εcarrier j)
            let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)
            MapsTo (carrierGraph T) cell
              (ball ((0 : Euclidean n), (z, T.reference.spatialPatch z)) (σ j)) ∧
            MapsTo (fun p ↦ coordinates (adaptedCoordinates T.data.adapted) (ψ p)) cell
              (Ioo (-δcomp j) (δcomp j) ×ˢ ball ((0 : Euclidean (n - 1)), z) (rcomp j)) ∧
            cell ⊆ (U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
              (parameter ⁻¹' parameterInterior (2 * P.radius)) ∧
            cell ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
              (parameter ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
            MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) (ρdet j))
              (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
            closedBall ((0 : Euclidean n), z) (ρdet j) ⊆
              ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius) ∧
            MapsTo ψ cell (closedBall ((0 : Euclidean n), z) (ρdet j))) ∧
          (∀ z ∈ parameterCube P.radius, ∃ j : centers,
            ((0 : Euclidean n), (z 0, spectatorCenter z)) ∈
              ball (0 : Euclidean n) (εcarrier j) ×ˢ
                ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier j)) ∧
        ∃ V : Set (Euclidean 3 × Euclidean (n - 1)),
          IsOpen V ∧ (∀ z ∈ parameterCube P.radius, (z, T.reference.spatialPatch z) ∈ V) ∧
          (ball (0 : Euclidean n) ε ×ˢ V ⊆
            ⋃ j : centers, closedBall ((0 : Euclidean n),
              (j.1.1, T.reference.spatialPatch j.1.1)) (σ j)) ∧
      ∀ M Mᵣ κmet κnormal m : ℝ, 0 ≤ M → 0 ≤ Mᵣ →
        0 < κmet → 0 < κnormal → 0 < m →
      ∃ c : ℝ, ∃ E : ℕ → ℝ, ∃ A H B : centers → ℕ → ℝ,
        0 < c ∧ (∀ j, 0 < E j) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 14 F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ j : centers,
        let z₀ := j.1.1
        let Ωc := Ωc j
        let ρc := ρc j
        let Bc := Bc j
        let gc := gc j
        let row := row j
        let col := col j
        let ρ := ρ j
        let R := R j
        let τ := τ j
        let Rc := Rc j
        let τc := τc j
        let Mc := Mc j
        let rcomp := rcomp j
        let δcomp := δcomp j
        let σ := σ j
        let A := A j
        let H := H j
        let B := B j
        let g := c
        let b := c
        let cν := c
        let a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
          (0, (z₀, T.reference.spatialPatch z₀))
        let Ω := ball a (2 * ρ)
        closedBall a (2 * ρ) ⊆ domain T ∧
        MapsTo Prod.fst (closedBall a (2 * ρ))
          (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
            (ball (0 : Euclidean n) T.physicalRadius ∩ interior K)) ∧
        let e := adaptedCoordinates T.data.adapted
        let Cc := coordinates (Z := Euclidean 3) e
        let pc := ((0 : Euclidean (n - 1)), z₀)
        ∃ Dc : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        ∃ φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
          (ContDiffOn ℝ ∞ (carrierNullvector T Q col) Ωc ∧
            ContDiffOn ℝ ∞ (carrierConullvector T Q row) Ωc ∧
            ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ωc ∧
            ContDiffOn ℝ ∞ (carrierTransportPotential T Q F row col) Ωc ∧
            cNorm (closedBall ((0 : Euclidean n), z₀) ρc) 1
              (carrierTransportDirection T Q row col) ≤ Bc ∧
            (∀ w ∈ Ωc, ∀ i, (Q.1 w.1 i).IsSymm) ∧
            (∀ w ∈ Ωc,
              carrierNullvector T Q col w ≠ 0 ∧ carrierConullvector T Q row w ≠ 0 ∧
              reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
                (fun j ↦ carrierNullvector T Q col w j) = 0 ∧
              carrierConullvector T Q row w ᵥ*
                reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
              gc ≤ |carrierAdaptedDenominator T Q row col w| ∧
              carrierAdaptedDenominator T Q row col w ≠ 0 ∧
              |(carrierAdaptedDenominator T Q row col w)⁻¹| ≤ gc⁻¹) ∧
            Dc = (fun q ↦ (q.1, φ q)) ''
              (Ioo (-τc) τc ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8)) ∧
            Dc ⊆ Cc.symm ⁻¹' Ωc ∧ Cc ⁻¹' Dc ⊆ Ωc ∧
            Cc ⁻¹' Dc ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
              parameterInterior (3 * P.radius / 2) ∧
            ContDiffOn ℝ ∞ φ
              (Ioo (-τc) τc ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8)) ∧
            ContDiffOn ℝ ∞ y Dc ∧
            (∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8),
              ∀ t ∈ Ioo (-τc) τc, (φ (t, p)).2 = p.2) ∧
            (∀ q ∈ Dc, (y q).2 = q.2.2) ∧
            ContDiffOn ℝ ∞ y (Ioo (-(2 * τc)) (2 * τc) ×ˢ
              ball ((0 : Euclidean (n - 1)), z₀) (Rc / 4))) ∧
          IsOpen Dc ∧ Ioo (-τc) τc ×ˢ ball pc (Rc / 32) ⊆ Dc ∧
          Dc ⊆ Ioo (-τc) τc ×ˢ ball pc (Rc / 4) ∧
          MapsTo (fun q ↦ (q.1, φ q)) (Ioo (-τc) τc ×ˢ ball pc (Rc / 8)) Dc ∧
          MapsTo (fun q ↦ (q.1, y q)) Dc (Ioo (-τc) τc ×ˢ ball pc (Rc / 8)) ∧
          (∀ p ∈ ball pc (Rc / 8), φ (0, p) = p) ∧
          (∀ p ∈ ball pc (Rc / 8), ∀ t ∈ Ioo (-τc) τc, y (t, φ (t, p)) = p) ∧
          (∀ q ∈ Dc, φ (q.1, y q) = q.2) ∧
          (∀ p ∈ ball pc (Rc / 8), ∀ t ∈ Ioo (-τc) τc, HasDerivAt (fun s ↦ φ (s, p))
            ((e (carrierTransportDirection T Q row col (Cc.symm (t, φ (t, p))))).2, 0) t) ∧
          ContDiffOn ℝ ∞ φ (Ioo (-(2 * τc)) (2 * τc) ×ˢ ball pc (Rc / 4)) ∧
          cNorm (Icc (-τc) τc ×ˢ closedBall pc (Rc / 8)) 1 φ ≤ Mc ∧
      let p₀ := ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀))
      let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1))
        (adaptedCoordinates T.data.adapted)
      let Bρ := closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) ρ
      let I := Ioo (-τ) τ
      let L := ball p₀ (R / 8)
      let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
      let W := C.symm '' (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64))
      ∃ D : Set (ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))),
      ∃ Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
        Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)),
        IsOpen D ∧ I ×ˢ ball p₀ (R / 32) ⊆ D ∧ D ⊆ I ×ˢ ball p₀ (R / 4) ∧
        C ⁻¹' D ⊆ Ω ∧
        closedBall a (2 * σ) ⊆ C ⁻¹' D ∧
        (∀ (y : Euclidean (n - 1)) (z : Euclidean 3) (ζ : Euclidean (n - 1)),
          (T.data.adapted.embedding y, (z, ζ)) ∈ closedBall a (2 * σ) →
          phase T Q (T.data.adapted.embedding y) ζ = inner ℝ y ζ) ∧
        ContDiffOn ℝ ∞ Φ (I ×ˢ L) ∧ ContDiffOn ℝ ∞ Y D ∧
        MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ L) D ∧
        MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ L) ∧
        (∀ p ∈ L, Φ (0, p) = p) ∧
        (∀ p ∈ L, ∀ t ∈ I, Y (t, Φ (t, p)) = p) ∧
        (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
        (∀ p ∈ L, ∀ t ∈ I, (Φ (t, p)).2.1 = p.2.1 ∧ (Φ (t, p)).2.2 = p.2.2) ∧
        (∀ q ∈ D, (Y q).2.1 = q.2.2.1 ∧ (Y q).2.2 = q.2.2.2) ∧
        (∀ p ∈ L, ∀ t ∈ I, HasDerivAt (fun s ↦ Φ (s, p))
          ((adaptedCoordinates T.data.adapted
            (transportDirection T Q row col (C.symm (t, Φ (t, p))))).2, 0) t) ∧
        ContDiffOn ℝ ∞ Φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
        ContDiffOn ℝ ∞ Y (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
        (∀ j, cNorm J j Φ + cNorm J j Y ≤ H j * (1 + cNorm K (j + 5) F)) ∧
        (∀ w ∈ C ⁻¹' D,
          b ≤ ‖nullvector T Q col w‖ ∧ b ≤ ‖phaseGradient T Q w.1 w.2.2‖ ∧
          reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
            (fun i ↦ nullvector T Q col w i) = 0 ∧
          conullvector T Q row w ᵥ*
            reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) = 0) ∧
        (∀ j, cNorm Bρ j (nullvector T Q col) +
          cNorm Bρ j (conullvector T Q row) +
          cNorm Bρ j (adaptedDenominator T Q row col) +
          cNorm Bρ j (fun w ↦ (adaptedDenominator T Q row col w)⁻¹) +
          cNorm Bρ j (transportDirection T Q row col) +
          cNorm Bρ j (transportPotential T Q F row col) ≤ A j * (1 + cNorm K (j + 5) F)) ∧
        (∀ q ∈ Ioo (-δcomp) δcomp ×ˢ ball pc rcomp,
          q ∈ Dc ∧ (q.1, carrierLabel T q.2) ∈ D ∧
          (∀ t ∈ Ioo (-δcomp) δcomp,
            Φ (t, carrierLabel T (y q)) = carrierLabel T (φ (t, y q))) ∧
          Y (q.1, carrierLabel T q.2) = carrierLabel T (y q) ∧
          ∀ initial : Euclidean (n - 1) × Euclidean 3 → ℝ,
            let w := Cc.symm q
            scalarAmplitude T Q F row col Φ Y initial
                (w.1, (w.2, T.reference.spatialPatch w.2)) =
              carrierScalarAmplitude T Q F row col φ y initial w ∧
            scalarAmplitude T Q F row col Φ Y initial
                (w.1, (w.2, T.reference.spatialPatch w.2)) •
                nullvector T Q col (w.1, (w.2, T.reference.spatialPatch w.2)) =
              carrierScalarAmplitude T Q F row col φ y initial w • carrierNullvector T Q col w) ∧
        ∀ r : Euclidean (n - 1) × Euclidean 3 → ℝ,
          ContDiffOn ℝ ∞ r (ball ((0 : Euclidean (n - 1)), z₀) (R / 4)) →
          cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) 14 r ≤ Mᵣ →
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8), m ≤ r p) →
          let α := scalarAmplitude T Q F row col Φ Y r
          ContDiffOn ℝ ∞ α (C ⁻¹' D) ∧
          ContDiffOn ℝ ∞ (fun w ↦ α w • nullvector T Q col w) (C ⁻¹' D) ∧
          (∀ p ∈ L, α (T.data.adapted.embedding p.1, p.2) = r (p.1, p.2.1)) ∧
          (∀ w ∈ C ⁻¹' D, g ≤ α w ∧ 0 < α w ∧
            nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0 ∧
            α w • nullvector T Q col w ≠ 0) ∧
          (∀ w ∈ C ⁻¹' D,
            fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (transportDirection T Q row col w) +
              transportPotential T Q F row col w * α w = 0) ∧
          (∀ w ∈ C ⁻¹' D,
            reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
              (fun j ↦ (α w • nullvector T Q col w) j) = 0) ∧
          (∀ w ∈ C ⁻¹' D, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
            (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1 = 0) ∧
          (∀ j, cNorm W j α + cNorm W j (fun w ↦ α w • nullvector T Q col w) ≤
            B j * (1 + cNorm K (j + 13) F +
              cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 13) r)) ∧
              (∀ w ∈ C ⁻¹' D,
                cν ≤ ‖principalNormal (canonicalNormalCompletion F w.1)
                  (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)‖ ∧
                determinant (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) = 0 ∧
                (1 / 2 : ℝ) • linearizedMetric F
                    (reconstruction F (canonicalNormalCompletion F) (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2))) w.1 =
                  stressProjection F w.1 (symmCovariantDeriv F (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1) ∧
                (∀ τ' : ℝ, τ' ≠ 0 →
                  completedVariationComplex F
                    (fun x ↦ (τ' : ℂ) ^ 2 •
                      Complex.exp (Complex.I * (phase T Q x w.2.2 : ℂ) / (τ' : ℂ)) •
                        euclideanComplexInclusion (α (x, w.2) • nullvector T Q col (x, w.2))) 0 w.1 =
                    Complex.exp (Complex.I * (phase T Q w.1 w.2.2 : ℂ) / (τ' : ℂ)) •
                      ((Complex.I * (τ' : ℂ)) • euclideanComplexInclusion
                        (principalNormal (canonicalNormalCompletion F w.1)
                          (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)) +
                      (τ' : ℂ) ^ 2 • euclideanComplexInclusion
                        (reconstruction F (canonicalNormalCompletion F) (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1))) ∧
                hermitianTensor ((principalMatrix
                    (principalNormal (canonicalNormalCompletion F w.1)
                      (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w))
                    (phaseGradient T Q w.1 w.2.2)).map Complex.ofReal) =
                  fun i j ↦ ‖principalNormal (canonicalNormalCompletion F w.1)
                    (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)‖ ^ 2 *
                      phaseGradient T Q w.1 w.2.2 i * phaseGradient T Q w.1 w.2.2 j) ∧
          let J₀ := closedBall a σ
          let b₀ := fun w ↦ α w • nullvector T Q col w
          let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
            phaseGradient T Q w.1 w.2.2
          let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
          let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
          ∀ j, cNorm J₀ j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J₀ j b₀ +
            cNorm J₀ j ν + cNorm J₀ j V + cNorm J₀ j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
              E j * (1 + cNorm K (j + 14) F +
                cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r) := by
  obtain ⟨η, ε, hη, hε, centers, row, col, ρ, R, τ, Rc, τc, Mc, rcomp, δcomp, σ,
    hrc, hpositive, Ωc, ρc, Bc, gc, _μc, _Bfull, _hsource, _hfull,
    hgeometryc, hworking, εcarrier, ρdet, hcell, hcarrierCover,
    V, hV, hgraph, hcover, hproduce⟩ :=
    exists_finite_retained_leading_family_before_geometry_with_source_geometry hn hP T hK hKU hball
  refine ⟨η, ε, hη, hε, centers, row, col, ρ, R, τ, Rc, τc, Mc, rcomp, δcomp, σ,
    hrc, hpositive, Ωc, ρc, Bc, gc, hgeometryc, hworking, εcarrier, ρdet, hcell,
    hcarrierCover, V, hV, hgraph, hcover, ?_⟩
  intro M Mᵣ κmet κnormal m hM hMᵣ hκmet hκnormal hm
  obtain ⟨c, E, A, H, B, hc, hE, hactual⟩ :=
    hproduce M Mᵣ κmet κnormal m hM hMᵣ hκmet hκnormal hm
  refine ⟨c, E, A, H, B, hc, hE, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  obtain ⟨hlow, hactual⟩ := hactual F hF hi hrank hFM hmet hnormal hclose
  exact ⟨hlow, fun j ↦ ⟨(hactual j).1, (hactual j).2.1, (hactual j).2.2.2⟩⟩

/-- Original entry point, retaining every witness and conclusion of the strengthened
comparison-radius constructor and forgetting only its additional bound
(`app:ch_background:eq:bg-Psi`, `app:ch_background:prop:bg-frame`). -/
theorem exists_finite_retained_leading_family_before_geometry_with_carrier_data_and_working_balls {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
 :
    ∃ η ε : ℝ, 0 < η ∧ 0 < ε ∧
      ∃ centers : Finset (parameterCube P.radius),
      ∃ row col : centers → Fin n,
      ∃ ρ R τ Rc τc Mc rcomp δcomp σ : centers → ℝ,
        (∀ j, 0 < ρ j ∧ 0 < R j ∧ 0 < τ j ∧ 0 < Rc j ∧ 0 < τc j ∧
          0 < Mc j ∧ 0 < rcomp j ∧ 0 < δcomp j ∧ 0 < σ j) ∧
        ∃ Ωc : centers → Set (Euclidean n × Euclidean 3),
        ∃ ρc Bc gc : centers → ℝ,
          (∀ j : centers, let z₀ := j.1.1
            let Ωc := Ωc j
            let ρc := ρc j
            let Bc := Bc j
            let gc := gc j
            let Rc := Rc j
            let τc := τc j
            (0 < ρc ∧ 0 < Bc ∧ 0 < gc ∧ IsOpen Ωc ∧
              closedBall ((0 : Euclidean n), z₀) ρc ⊆ Ωc ∧
              Ωc ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
                parameterInterior (3 * P.radius / 2) ∧
              MapsTo Prod.fst (closedBall ((0 : Euclidean n), z₀) ρc)
                (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
              MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
                (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z₀)) Rc)
                (closedBall ((0 : Euclidean n), z₀) ρc) ∧
              τc = existenceTime Rc (NullTransport.ActualFlow.liftedLowBound T Bc) / 4 ∧
              τc ≤ Rc / 16)) ∧
        (∀ j : centers, let z₀ := j.1.1
          let a := ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀))
          closedBall a (2 * σ j) ⊆
            (coordinates (adaptedCoordinates T.data.adapted)).symm ''
              (Icc (-τ j / 2) (τ j / 2) ×ˢ
                closedBall ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀))
                  (R j / 64)) ∧
          closedBall a (2 * σ j) ⊆ closedBall a (ρ j) ∧
          ∀ w ∈ closedBall a (2 * σ j),
            w.2.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T)
              (min T.family.radius (3 * T.family.sourceRadius))) ∧
        ∃ εcarrier ρdet : centers → ℝ,
          (∀ j, 0 < εcarrier j ∧ 0 < ρdet j ∧
            let z := j.1.1
            let cell := ball (0 : Euclidean n) (εcarrier j) ×ˢ
              ball (z 0, spectatorCenter z) (εcarrier j)
            let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)
            MapsTo (carrierGraph T) cell
              (ball ((0 : Euclidean n), (z, T.reference.spatialPatch z)) (σ j)) ∧
            MapsTo (fun p ↦ coordinates (adaptedCoordinates T.data.adapted) (ψ p)) cell
              (Ioo (-δcomp j) (δcomp j) ×ˢ ball ((0 : Euclidean (n - 1)), z) (rcomp j)) ∧
            cell ⊆ (U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
              (parameter ⁻¹' parameterInterior (2 * P.radius)) ∧
            cell ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
              (parameter ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
            MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) (ρdet j))
              (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
            closedBall ((0 : Euclidean n), z) (ρdet j) ⊆
              ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius) ∧
            MapsTo ψ cell (closedBall ((0 : Euclidean n), z) (ρdet j))) ∧
          (∀ z ∈ parameterCube P.radius, ∃ j : centers,
            ((0 : Euclidean n), (z 0, spectatorCenter z)) ∈
              ball (0 : Euclidean n) (εcarrier j) ×ˢ
                ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier j)) ∧
        ∃ V : Set (Euclidean 3 × Euclidean (n - 1)),
          IsOpen V ∧ (∀ z ∈ parameterCube P.radius, (z, T.reference.spatialPatch z) ∈ V) ∧
          (ball (0 : Euclidean n) ε ×ˢ V ⊆
            ⋃ j : centers, closedBall ((0 : Euclidean n),
              (j.1.1, T.reference.spatialPatch j.1.1)) (σ j)) ∧
      ∀ M Mᵣ κmet κnormal m : ℝ, 0 ≤ M → 0 ≤ Mᵣ →
        0 < κmet → 0 < κnormal → 0 < m →
      ∃ c : ℝ, ∃ E : ℕ → ℝ, ∃ A H B : centers → ℕ → ℝ,
        0 < c ∧ (∀ j, 0 < E j) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 14 F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ j : centers,
        let z₀ := j.1.1
        let Ωc := Ωc j
        let ρc := ρc j
        let Bc := Bc j
        let gc := gc j
        let row := row j
        let col := col j
        let ρ := ρ j
        let R := R j
        let τ := τ j
        let Rc := Rc j
        let τc := τc j
        let Mc := Mc j
        let rcomp := rcomp j
        let δcomp := δcomp j
        let σ := σ j
        let A := A j
        let H := H j
        let B := B j
        let g := c
        let b := c
        let cν := c
        let a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
          (0, (z₀, T.reference.spatialPatch z₀))
        let Ω := ball a (2 * ρ)
        closedBall a (2 * ρ) ⊆ domain T ∧
        MapsTo Prod.fst (closedBall a (2 * ρ))
          (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
            (ball (0 : Euclidean n) T.physicalRadius ∩ interior K)) ∧
        let e := adaptedCoordinates T.data.adapted
        let Cc := coordinates (Z := Euclidean 3) e
        let pc := ((0 : Euclidean (n - 1)), z₀)
        ∃ Dc : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        ∃ φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
          (ContDiffOn ℝ ∞ (carrierNullvector T Q col) Ωc ∧
            ContDiffOn ℝ ∞ (carrierConullvector T Q row) Ωc ∧
            ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ωc ∧
            ContDiffOn ℝ ∞ (carrierTransportPotential T Q F row col) Ωc ∧
            cNorm (closedBall ((0 : Euclidean n), z₀) ρc) 1
              (carrierTransportDirection T Q row col) ≤ Bc ∧
            (∀ w ∈ Ωc, ∀ i, (Q.1 w.1 i).IsSymm) ∧
            (∀ w ∈ Ωc,
              carrierNullvector T Q col w ≠ 0 ∧ carrierConullvector T Q row w ≠ 0 ∧
              reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
                (fun j ↦ carrierNullvector T Q col w j) = 0 ∧
              carrierConullvector T Q row w ᵥ*
                reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
              gc ≤ |carrierAdaptedDenominator T Q row col w| ∧
              carrierAdaptedDenominator T Q row col w ≠ 0 ∧
              |(carrierAdaptedDenominator T Q row col w)⁻¹| ≤ gc⁻¹) ∧
            Dc = (fun q ↦ (q.1, φ q)) ''
              (Ioo (-τc) τc ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8)) ∧
            Dc ⊆ Cc.symm ⁻¹' Ωc ∧ Cc ⁻¹' Dc ⊆ Ωc ∧
            Cc ⁻¹' Dc ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
              parameterInterior (3 * P.radius / 2) ∧
            ContDiffOn ℝ ∞ φ
              (Ioo (-τc) τc ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8)) ∧
            ContDiffOn ℝ ∞ y Dc ∧
            (∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8),
              ∀ t ∈ Ioo (-τc) τc, (φ (t, p)).2 = p.2) ∧
            (∀ q ∈ Dc, (y q).2 = q.2.2) ∧
            ContDiffOn ℝ ∞ y (Ioo (-(2 * τc)) (2 * τc) ×ˢ
              ball ((0 : Euclidean (n - 1)), z₀) (Rc / 4))) ∧
          IsOpen Dc ∧ Ioo (-τc) τc ×ˢ ball pc (Rc / 32) ⊆ Dc ∧
          Dc ⊆ Ioo (-τc) τc ×ˢ ball pc (Rc / 4) ∧
          MapsTo (fun q ↦ (q.1, φ q)) (Ioo (-τc) τc ×ˢ ball pc (Rc / 8)) Dc ∧
          MapsTo (fun q ↦ (q.1, y q)) Dc (Ioo (-τc) τc ×ˢ ball pc (Rc / 8)) ∧
          (∀ p ∈ ball pc (Rc / 8), φ (0, p) = p) ∧
          (∀ p ∈ ball pc (Rc / 8), ∀ t ∈ Ioo (-τc) τc, y (t, φ (t, p)) = p) ∧
          (∀ q ∈ Dc, φ (q.1, y q) = q.2) ∧
          (∀ p ∈ ball pc (Rc / 8), ∀ t ∈ Ioo (-τc) τc, HasDerivAt (fun s ↦ φ (s, p))
            ((e (carrierTransportDirection T Q row col (Cc.symm (t, φ (t, p))))).2, 0) t) ∧
          ContDiffOn ℝ ∞ φ (Ioo (-(2 * τc)) (2 * τc) ×ˢ ball pc (Rc / 4)) ∧
          cNorm (Icc (-τc) τc ×ˢ closedBall pc (Rc / 8)) 1 φ ≤ Mc ∧
      let p₀ := ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀))
      let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1))
        (adaptedCoordinates T.data.adapted)
      let Bρ := closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) ρ
      let I := Ioo (-τ) τ
      let L := ball p₀ (R / 8)
      let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
      let W := C.symm '' (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64))
      ∃ D : Set (ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))),
      ∃ Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
        Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)),
        IsOpen D ∧ I ×ˢ ball p₀ (R / 32) ⊆ D ∧ D ⊆ I ×ˢ ball p₀ (R / 4) ∧
        C ⁻¹' D ⊆ Ω ∧
        closedBall a (2 * σ) ⊆ C ⁻¹' D ∧
        (∀ (y : Euclidean (n - 1)) (z : Euclidean 3) (ζ : Euclidean (n - 1)),
          (T.data.adapted.embedding y, (z, ζ)) ∈ closedBall a (2 * σ) →
          phase T Q (T.data.adapted.embedding y) ζ = inner ℝ y ζ) ∧
        ContDiffOn ℝ ∞ Φ (I ×ˢ L) ∧ ContDiffOn ℝ ∞ Y D ∧
        MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ L) D ∧
        MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ L) ∧
        (∀ p ∈ L, Φ (0, p) = p) ∧
        (∀ p ∈ L, ∀ t ∈ I, Y (t, Φ (t, p)) = p) ∧
        (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
        (∀ p ∈ L, ∀ t ∈ I, (Φ (t, p)).2.1 = p.2.1 ∧ (Φ (t, p)).2.2 = p.2.2) ∧
        (∀ q ∈ D, (Y q).2.1 = q.2.2.1 ∧ (Y q).2.2 = q.2.2.2) ∧
        (∀ p ∈ L, ∀ t ∈ I, HasDerivAt (fun s ↦ Φ (s, p))
          ((adaptedCoordinates T.data.adapted
            (transportDirection T Q row col (C.symm (t, Φ (t, p))))).2, 0) t) ∧
        ContDiffOn ℝ ∞ Φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
        ContDiffOn ℝ ∞ Y (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
        (∀ j, cNorm J j Φ + cNorm J j Y ≤ H j * (1 + cNorm K (j + 5) F)) ∧
        (∀ w ∈ C ⁻¹' D,
          b ≤ ‖nullvector T Q col w‖ ∧ b ≤ ‖phaseGradient T Q w.1 w.2.2‖ ∧
          reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
            (fun i ↦ nullvector T Q col w i) = 0 ∧
          conullvector T Q row w ᵥ*
            reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) = 0) ∧
        (∀ j, cNorm Bρ j (nullvector T Q col) +
          cNorm Bρ j (conullvector T Q row) +
          cNorm Bρ j (adaptedDenominator T Q row col) +
          cNorm Bρ j (fun w ↦ (adaptedDenominator T Q row col w)⁻¹) +
          cNorm Bρ j (transportDirection T Q row col) +
          cNorm Bρ j (transportPotential T Q F row col) ≤ A j * (1 + cNorm K (j + 5) F)) ∧
        (∀ q ∈ Ioo (-δcomp) δcomp ×ˢ ball pc rcomp,
          q ∈ Dc ∧ (q.1, carrierLabel T q.2) ∈ D ∧
          (∀ t ∈ Ioo (-δcomp) δcomp,
            Φ (t, carrierLabel T (y q)) = carrierLabel T (φ (t, y q))) ∧
          Y (q.1, carrierLabel T q.2) = carrierLabel T (y q) ∧
          ∀ initial : Euclidean (n - 1) × Euclidean 3 → ℝ,
            let w := Cc.symm q
            scalarAmplitude T Q F row col Φ Y initial
                (w.1, (w.2, T.reference.spatialPatch w.2)) =
              carrierScalarAmplitude T Q F row col φ y initial w ∧
            scalarAmplitude T Q F row col Φ Y initial
                (w.1, (w.2, T.reference.spatialPatch w.2)) •
                nullvector T Q col (w.1, (w.2, T.reference.spatialPatch w.2)) =
              carrierScalarAmplitude T Q F row col φ y initial w • carrierNullvector T Q col w) ∧
        ∀ r : Euclidean (n - 1) × Euclidean 3 → ℝ,
          ContDiffOn ℝ ∞ r (ball ((0 : Euclidean (n - 1)), z₀) (R / 4)) →
          cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) 14 r ≤ Mᵣ →
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8), m ≤ r p) →
          let α := scalarAmplitude T Q F row col Φ Y r
          ContDiffOn ℝ ∞ α (C ⁻¹' D) ∧
          ContDiffOn ℝ ∞ (fun w ↦ α w • nullvector T Q col w) (C ⁻¹' D) ∧
          (∀ p ∈ L, α (T.data.adapted.embedding p.1, p.2) = r (p.1, p.2.1)) ∧
          (∀ w ∈ C ⁻¹' D, g ≤ α w ∧ 0 < α w ∧
            nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0 ∧
            α w • nullvector T Q col w ≠ 0) ∧
          (∀ w ∈ C ⁻¹' D,
            fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (transportDirection T Q row col w) +
              transportPotential T Q F row col w * α w = 0) ∧
          (∀ w ∈ C ⁻¹' D,
            reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
              (fun j ↦ (α w • nullvector T Q col w) j) = 0) ∧
          (∀ w ∈ C ⁻¹' D, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
            (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1 = 0) ∧
          (∀ j, cNorm W j α + cNorm W j (fun w ↦ α w • nullvector T Q col w) ≤
            B j * (1 + cNorm K (j + 13) F +
              cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 13) r)) ∧
              (∀ w ∈ C ⁻¹' D,
                cν ≤ ‖principalNormal (canonicalNormalCompletion F w.1)
                  (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)‖ ∧
                determinant (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) = 0 ∧
                (1 / 2 : ℝ) • linearizedMetric F
                    (reconstruction F (canonicalNormalCompletion F) (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2))) w.1 =
                  stressProjection F w.1 (symmCovariantDeriv F (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1) ∧
                (∀ τ' : ℝ, τ' ≠ 0 →
                  completedVariationComplex F
                    (fun x ↦ (τ' : ℂ) ^ 2 •
                      Complex.exp (Complex.I * (phase T Q x w.2.2 : ℂ) / (τ' : ℂ)) •
                        euclideanComplexInclusion (α (x, w.2) • nullvector T Q col (x, w.2))) 0 w.1 =
                    Complex.exp (Complex.I * (phase T Q w.1 w.2.2 : ℂ) / (τ' : ℂ)) •
                      ((Complex.I * (τ' : ℂ)) • euclideanComplexInclusion
                        (principalNormal (canonicalNormalCompletion F w.1)
                          (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)) +
                      (τ' : ℂ) ^ 2 • euclideanComplexInclusion
                        (reconstruction F (canonicalNormalCompletion F) (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1))) ∧
                hermitianTensor ((principalMatrix
                    (principalNormal (canonicalNormalCompletion F w.1)
                      (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w))
                    (phaseGradient T Q w.1 w.2.2)).map Complex.ofReal) =
                  fun i j ↦ ‖principalNormal (canonicalNormalCompletion F w.1)
                    (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)‖ ^ 2 *
                      phaseGradient T Q w.1 w.2.2 i * phaseGradient T Q w.1 w.2.2 j) ∧
          let J₀ := closedBall a σ
          let b₀ := fun w ↦ α w • nullvector T Q col w
          let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
            phaseGradient T Q w.1 w.2.2
          let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
          let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
          ∀ j, cNorm J₀ j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J₀ j b₀ +
            cNorm J₀ j ν + cNorm J₀ j V + cNorm J₀ j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
              E j * (1 + cNorm K (j + 14) F +
                cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r) := by
  obtain ⟨η, ε, hη, hε, centers, row, col, ρ, R, τ, Rc, τc, Mc, rcomp, δcomp, σ, _hrc, hrest⟩ :=
    exists_finite_retained_leading_family_before_geometry_with_carrier_data_and_working_balls_and_comparison_radius hn hP T hK hKU hball
  exact ⟨η, ε, hη, hε, centers, row, col, ρ, R, τ, Rc, τc, Mc, rcomp, δcomp, σ, hrest⟩

/-- Preserve the carrier-data endpoint by projecting the same witnesses from
the working-ball constructor (`app:ch_waves:thm:leading`,
`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem exists_finite_retained_leading_family_before_geometry_with_carrier_data {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
 :
    ∃ η ε : ℝ, 0 < η ∧ 0 < ε ∧
      ∃ centers : Finset (parameterCube P.radius),
      ∃ row col : centers → Fin n,
      ∃ ρ R τ Rc τc Mc rcomp δcomp σ : centers → ℝ,
        (∀ j, 0 < ρ j ∧ 0 < R j ∧ 0 < τ j ∧ 0 < Rc j ∧ 0 < τc j ∧
          0 < Mc j ∧ 0 < rcomp j ∧ 0 < δcomp j ∧ 0 < σ j) ∧
        ∃ Ωc : centers → Set (Euclidean n × Euclidean 3),
        ∃ ρc Bc gc : centers → ℝ,
          (∀ j : centers, let z₀ := j.1.1
            let Ωc := Ωc j
            let ρc := ρc j
            let Bc := Bc j
            let gc := gc j
            let Rc := Rc j
            let τc := τc j
            (0 < ρc ∧ 0 < Bc ∧ 0 < gc ∧ IsOpen Ωc ∧
              closedBall ((0 : Euclidean n), z₀) ρc ⊆ Ωc ∧
              Ωc ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
                parameterInterior (3 * P.radius / 2) ∧
              MapsTo Prod.fst (closedBall ((0 : Euclidean n), z₀) ρc)
                (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
              MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
                (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z₀)) Rc)
                (closedBall ((0 : Euclidean n), z₀) ρc) ∧
              τc = existenceTime Rc (NullTransport.ActualFlow.liftedLowBound T Bc) / 4 ∧
              τc ≤ Rc / 16)) ∧
        ∃ εcarrier ρdet : centers → ℝ,
          (∀ j, 0 < εcarrier j ∧ 0 < ρdet j ∧
            let z := j.1.1
            let cell := ball (0 : Euclidean n) (εcarrier j) ×ˢ
              ball (z 0, spectatorCenter z) (εcarrier j)
            let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)
            MapsTo (carrierGraph T) cell
              (ball ((0 : Euclidean n), (z, T.reference.spatialPatch z)) (σ j)) ∧
            MapsTo (fun p ↦ coordinates (adaptedCoordinates T.data.adapted) (ψ p)) cell
              (Ioo (-δcomp j) (δcomp j) ×ˢ ball ((0 : Euclidean (n - 1)), z) (rcomp j)) ∧
            cell ⊆ (U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
              (parameter ⁻¹' parameterInterior (2 * P.radius)) ∧
            cell ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
              (parameter ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
            MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) (ρdet j))
              (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
            closedBall ((0 : Euclidean n), z) (ρdet j) ⊆
              ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius) ∧
            MapsTo ψ cell (closedBall ((0 : Euclidean n), z) (ρdet j))) ∧
          (∀ z ∈ parameterCube P.radius, ∃ j : centers,
            ((0 : Euclidean n), (z 0, spectatorCenter z)) ∈
              ball (0 : Euclidean n) (εcarrier j) ×ˢ
                ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier j)) ∧
        ∃ V : Set (Euclidean 3 × Euclidean (n - 1)),
          IsOpen V ∧ (∀ z ∈ parameterCube P.radius, (z, T.reference.spatialPatch z) ∈ V) ∧
          (ball (0 : Euclidean n) ε ×ˢ V ⊆
            ⋃ j : centers, closedBall ((0 : Euclidean n),
              (j.1.1, T.reference.spatialPatch j.1.1)) (σ j)) ∧
      ∀ M Mᵣ κmet κnormal m : ℝ, 0 ≤ M → 0 ≤ Mᵣ →
        0 < κmet → 0 < κnormal → 0 < m →
      ∃ c : ℝ, ∃ E : ℕ → ℝ, ∃ A H B : centers → ℕ → ℝ,
        0 < c ∧ (∀ j, 0 < E j) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 14 F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ j : centers,
        let z₀ := j.1.1
        let Ωc := Ωc j
        let ρc := ρc j
        let Bc := Bc j
        let gc := gc j
        let row := row j
        let col := col j
        let ρ := ρ j
        let R := R j
        let τ := τ j
        let Rc := Rc j
        let τc := τc j
        let Mc := Mc j
        let rcomp := rcomp j
        let δcomp := δcomp j
        let σ := σ j
        let A := A j
        let H := H j
        let B := B j
        let g := c
        let b := c
        let cν := c
        let a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
          (0, (z₀, T.reference.spatialPatch z₀))
        let Ω := ball a (2 * ρ)
        closedBall a (2 * ρ) ⊆ domain T ∧
        MapsTo Prod.fst (closedBall a (2 * ρ))
          (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
            (ball (0 : Euclidean n) T.physicalRadius ∩ interior K)) ∧
        let e := adaptedCoordinates T.data.adapted
        let Cc := coordinates (Z := Euclidean 3) e
        let pc := ((0 : Euclidean (n - 1)), z₀)
        ∃ Dc : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        ∃ φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
          (ContDiffOn ℝ ∞ (carrierNullvector T Q col) Ωc ∧
            ContDiffOn ℝ ∞ (carrierConullvector T Q row) Ωc ∧
            ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ωc ∧
            ContDiffOn ℝ ∞ (carrierTransportPotential T Q F row col) Ωc ∧
            cNorm (closedBall ((0 : Euclidean n), z₀) ρc) 1
              (carrierTransportDirection T Q row col) ≤ Bc ∧
            (∀ w ∈ Ωc, ∀ i, (Q.1 w.1 i).IsSymm) ∧
            (∀ w ∈ Ωc,
              carrierNullvector T Q col w ≠ 0 ∧ carrierConullvector T Q row w ≠ 0 ∧
              reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
                (fun j ↦ carrierNullvector T Q col w j) = 0 ∧
              carrierConullvector T Q row w ᵥ*
                reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
              gc ≤ |carrierAdaptedDenominator T Q row col w| ∧
              carrierAdaptedDenominator T Q row col w ≠ 0 ∧
              |(carrierAdaptedDenominator T Q row col w)⁻¹| ≤ gc⁻¹) ∧
            Dc = (fun q ↦ (q.1, φ q)) ''
              (Ioo (-τc) τc ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8)) ∧
            Dc ⊆ Cc.symm ⁻¹' Ωc ∧ Cc ⁻¹' Dc ⊆ Ωc ∧
            Cc ⁻¹' Dc ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
              parameterInterior (3 * P.radius / 2) ∧
            ContDiffOn ℝ ∞ φ
              (Ioo (-τc) τc ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8)) ∧
            ContDiffOn ℝ ∞ y Dc ∧
            (∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8),
              ∀ t ∈ Ioo (-τc) τc, (φ (t, p)).2 = p.2) ∧
            (∀ q ∈ Dc, (y q).2 = q.2.2) ∧
            ContDiffOn ℝ ∞ y (Ioo (-(2 * τc)) (2 * τc) ×ˢ
              ball ((0 : Euclidean (n - 1)), z₀) (Rc / 4))) ∧
          IsOpen Dc ∧ Ioo (-τc) τc ×ˢ ball pc (Rc / 32) ⊆ Dc ∧
          Dc ⊆ Ioo (-τc) τc ×ˢ ball pc (Rc / 4) ∧
          MapsTo (fun q ↦ (q.1, φ q)) (Ioo (-τc) τc ×ˢ ball pc (Rc / 8)) Dc ∧
          MapsTo (fun q ↦ (q.1, y q)) Dc (Ioo (-τc) τc ×ˢ ball pc (Rc / 8)) ∧
          (∀ p ∈ ball pc (Rc / 8), φ (0, p) = p) ∧
          (∀ p ∈ ball pc (Rc / 8), ∀ t ∈ Ioo (-τc) τc, y (t, φ (t, p)) = p) ∧
          (∀ q ∈ Dc, φ (q.1, y q) = q.2) ∧
          (∀ p ∈ ball pc (Rc / 8), ∀ t ∈ Ioo (-τc) τc, HasDerivAt (fun s ↦ φ (s, p))
            ((e (carrierTransportDirection T Q row col (Cc.symm (t, φ (t, p))))).2, 0) t) ∧
          ContDiffOn ℝ ∞ φ (Ioo (-(2 * τc)) (2 * τc) ×ˢ ball pc (Rc / 4)) ∧
          cNorm (Icc (-τc) τc ×ˢ closedBall pc (Rc / 8)) 1 φ ≤ Mc ∧
      let p₀ := ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀))
      let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1))
        (adaptedCoordinates T.data.adapted)
      let Bρ := closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) ρ
      let I := Ioo (-τ) τ
      let L := ball p₀ (R / 8)
      let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
      let W := C.symm '' (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64))
      ∃ D : Set (ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))),
      ∃ Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
        Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)),
        IsOpen D ∧ I ×ˢ ball p₀ (R / 32) ⊆ D ∧ D ⊆ I ×ˢ ball p₀ (R / 4) ∧
        C ⁻¹' D ⊆ Ω ∧
        closedBall a (2 * σ) ⊆ C ⁻¹' D ∧
        (∀ (y : Euclidean (n - 1)) (z : Euclidean 3) (ζ : Euclidean (n - 1)),
          (T.data.adapted.embedding y, (z, ζ)) ∈ closedBall a (2 * σ) →
          phase T Q (T.data.adapted.embedding y) ζ = inner ℝ y ζ) ∧
        ContDiffOn ℝ ∞ Φ (I ×ˢ L) ∧ ContDiffOn ℝ ∞ Y D ∧
        MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ L) D ∧
        MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ L) ∧
        (∀ p ∈ L, Φ (0, p) = p) ∧
        (∀ p ∈ L, ∀ t ∈ I, Y (t, Φ (t, p)) = p) ∧
        (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
        (∀ p ∈ L, ∀ t ∈ I, (Φ (t, p)).2.1 = p.2.1 ∧ (Φ (t, p)).2.2 = p.2.2) ∧
        (∀ q ∈ D, (Y q).2.1 = q.2.2.1 ∧ (Y q).2.2 = q.2.2.2) ∧
        (∀ p ∈ L, ∀ t ∈ I, HasDerivAt (fun s ↦ Φ (s, p))
          ((adaptedCoordinates T.data.adapted
            (transportDirection T Q row col (C.symm (t, Φ (t, p))))).2, 0) t) ∧
        ContDiffOn ℝ ∞ Φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
        ContDiffOn ℝ ∞ Y (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
        (∀ j, cNorm J j Φ + cNorm J j Y ≤ H j * (1 + cNorm K (j + 5) F)) ∧
        (∀ w ∈ C ⁻¹' D,
          b ≤ ‖nullvector T Q col w‖ ∧ b ≤ ‖phaseGradient T Q w.1 w.2.2‖ ∧
          reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
            (fun i ↦ nullvector T Q col w i) = 0 ∧
          conullvector T Q row w ᵥ*
            reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) = 0) ∧
        (∀ j, cNorm Bρ j (nullvector T Q col) +
          cNorm Bρ j (conullvector T Q row) +
          cNorm Bρ j (adaptedDenominator T Q row col) +
          cNorm Bρ j (fun w ↦ (adaptedDenominator T Q row col w)⁻¹) +
          cNorm Bρ j (transportDirection T Q row col) +
          cNorm Bρ j (transportPotential T Q F row col) ≤ A j * (1 + cNorm K (j + 5) F)) ∧
        (∀ q ∈ Ioo (-δcomp) δcomp ×ˢ ball pc rcomp,
          q ∈ Dc ∧ (q.1, carrierLabel T q.2) ∈ D ∧
          (∀ t ∈ Ioo (-δcomp) δcomp,
            Φ (t, carrierLabel T (y q)) = carrierLabel T (φ (t, y q))) ∧
          Y (q.1, carrierLabel T q.2) = carrierLabel T (y q) ∧
          ∀ initial : Euclidean (n - 1) × Euclidean 3 → ℝ,
            let w := Cc.symm q
            scalarAmplitude T Q F row col Φ Y initial
                (w.1, (w.2, T.reference.spatialPatch w.2)) =
              carrierScalarAmplitude T Q F row col φ y initial w ∧
            scalarAmplitude T Q F row col Φ Y initial
                (w.1, (w.2, T.reference.spatialPatch w.2)) •
                nullvector T Q col (w.1, (w.2, T.reference.spatialPatch w.2)) =
              carrierScalarAmplitude T Q F row col φ y initial w • carrierNullvector T Q col w) ∧
        ∀ r : Euclidean (n - 1) × Euclidean 3 → ℝ,
          ContDiffOn ℝ ∞ r (ball ((0 : Euclidean (n - 1)), z₀) (R / 4)) →
          cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) 14 r ≤ Mᵣ →
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8), m ≤ r p) →
          let α := scalarAmplitude T Q F row col Φ Y r
          ContDiffOn ℝ ∞ α (C ⁻¹' D) ∧
          ContDiffOn ℝ ∞ (fun w ↦ α w • nullvector T Q col w) (C ⁻¹' D) ∧
          (∀ p ∈ L, α (T.data.adapted.embedding p.1, p.2) = r (p.1, p.2.1)) ∧
          (∀ w ∈ C ⁻¹' D, g ≤ α w ∧ 0 < α w ∧
            nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0 ∧
            α w • nullvector T Q col w ≠ 0) ∧
          (∀ w ∈ C ⁻¹' D,
            fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (transportDirection T Q row col w) +
              transportPotential T Q F row col w * α w = 0) ∧
          (∀ w ∈ C ⁻¹' D,
            reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
              (fun j ↦ (α w • nullvector T Q col w) j) = 0) ∧
          (∀ w ∈ C ⁻¹' D, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
            (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1 = 0) ∧
          (∀ j, cNorm W j α + cNorm W j (fun w ↦ α w • nullvector T Q col w) ≤
            B j * (1 + cNorm K (j + 13) F +
              cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 13) r)) ∧
              (∀ w ∈ C ⁻¹' D,
                cν ≤ ‖principalNormal (canonicalNormalCompletion F w.1)
                  (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)‖ ∧
                determinant (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) = 0 ∧
                (1 / 2 : ℝ) • linearizedMetric F
                    (reconstruction F (canonicalNormalCompletion F) (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2))) w.1 =
                  stressProjection F w.1 (symmCovariantDeriv F (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1) ∧
                (∀ τ' : ℝ, τ' ≠ 0 →
                  completedVariationComplex F
                    (fun x ↦ (τ' : ℂ) ^ 2 •
                      Complex.exp (Complex.I * (phase T Q x w.2.2 : ℂ) / (τ' : ℂ)) •
                        euclideanComplexInclusion (α (x, w.2) • nullvector T Q col (x, w.2))) 0 w.1 =
                    Complex.exp (Complex.I * (phase T Q w.1 w.2.2 : ℂ) / (τ' : ℂ)) •
                      ((Complex.I * (τ' : ℂ)) • euclideanComplexInclusion
                        (principalNormal (canonicalNormalCompletion F w.1)
                          (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)) +
                      (τ' : ℂ) ^ 2 • euclideanComplexInclusion
                        (reconstruction F (canonicalNormalCompletion F) (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1))) ∧
                hermitianTensor ((principalMatrix
                    (principalNormal (canonicalNormalCompletion F w.1)
                      (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w))
                    (phaseGradient T Q w.1 w.2.2)).map Complex.ofReal) =
                  fun i j ↦ ‖principalNormal (canonicalNormalCompletion F w.1)
                    (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)‖ ^ 2 *
                      phaseGradient T Q w.1 w.2.2 i * phaseGradient T Q w.1 w.2.2 j) ∧
          let J₀ := closedBall a σ
          let b₀ := fun w ↦ α w • nullvector T Q col w
          let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
            phaseGradient T Q w.1 w.2.2
          let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
          let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
          ∀ j, cNorm J₀ j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J₀ j b₀ +
            cNorm J₀ j ν + cNorm J₀ j V + cNorm J₀ j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
              E j * (1 + cNorm K (j + 14) F +
                cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r) := by
  obtain ⟨η, ε, hη, hε, centers, row, col, ρ, R, τ, Rc, τc, Mc, rcomp, δcomp, σ,
    hpositive, Ωc, ρc, Bc, gc, hgeometryc, _hworking, hrest⟩ :=
    exists_finite_retained_leading_family_before_geometry_with_carrier_data_and_working_balls
      hn hP T hK hKU hball
  exact ⟨η, ε, hη, hε, centers, row, col, ρ, R, τ, Rc, τc, Mc, rcomp, δcomp, σ,
    hpositive, Ωc, ρc, Bc, gc, hgeometryc, hrest⟩

/-- Original endpoint, projected from the joint carrier-data constructor for
`app:ch_waves:thm:leading`. All witnesses and conclusions are unchanged. -/
theorem exists_finite_retained_leading_family_before_geometry {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
 :
    ∃ η ε : ℝ, 0 < η ∧ 0 < ε ∧
      ∃ centers : Finset (parameterCube P.radius),
      ∃ row col : centers → Fin n,
      ∃ ρ R τ Rc τc Mc rcomp δcomp σ : centers → ℝ,
        (∀ j, 0 < ρ j ∧ 0 < R j ∧ 0 < τ j ∧ 0 < Rc j ∧ 0 < τc j ∧
          0 < Mc j ∧ 0 < rcomp j ∧ 0 < δcomp j ∧ 0 < σ j) ∧
        ∃ εcarrier ρdet : centers → ℝ,
          (∀ j, 0 < εcarrier j ∧ 0 < ρdet j ∧
            let z := j.1.1
            let cell := ball (0 : Euclidean n) (εcarrier j) ×ˢ
              ball (z 0, spectatorCenter z) (εcarrier j)
            let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)
            MapsTo (carrierGraph T) cell
              (ball ((0 : Euclidean n), (z, T.reference.spatialPatch z)) (σ j)) ∧
            MapsTo (fun p ↦ coordinates (adaptedCoordinates T.data.adapted) (ψ p)) cell
              (Ioo (-δcomp j) (δcomp j) ×ˢ ball ((0 : Euclidean (n - 1)), z) (rcomp j)) ∧
            cell ⊆ (U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
              (parameter ⁻¹' parameterInterior (2 * P.radius)) ∧
            cell ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
              (parameter ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
            MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) (ρdet j))
              (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
            closedBall ((0 : Euclidean n), z) (ρdet j) ⊆
              ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius) ∧
            MapsTo ψ cell (closedBall ((0 : Euclidean n), z) (ρdet j))) ∧
          (∀ z ∈ parameterCube P.radius, ∃ j : centers,
            ((0 : Euclidean n), (z 0, spectatorCenter z)) ∈
              ball (0 : Euclidean n) (εcarrier j) ×ˢ
                ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier j)) ∧
        ∃ V : Set (Euclidean 3 × Euclidean (n - 1)),
          IsOpen V ∧ (∀ z ∈ parameterCube P.radius, (z, T.reference.spatialPatch z) ∈ V) ∧
          (ball (0 : Euclidean n) ε ×ˢ V ⊆
            ⋃ j : centers, closedBall ((0 : Euclidean n),
              (j.1.1, T.reference.spatialPatch j.1.1)) (σ j)) ∧
      ∀ M Mᵣ κmet κnormal m : ℝ, 0 ≤ M → 0 ≤ Mᵣ →
        0 < κmet → 0 < κnormal → 0 < m →
      ∃ c : ℝ, ∃ E : ℕ → ℝ, ∃ A H B : centers → ℕ → ℝ,
        0 < c ∧ (∀ j, 0 < E j) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 14 F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ j : centers,
        let z₀ := j.1.1
        let row := row j
        let col := col j
        let ρ := ρ j
        let R := R j
        let τ := τ j
        let Rc := Rc j
        let τc := τc j
        let Mc := Mc j
        let rcomp := rcomp j
        let δcomp := δcomp j
        let σ := σ j
        let A := A j
        let H := H j
        let B := B j
        let g := c
        let b := c
        let cν := c
        let a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
          (0, (z₀, T.reference.spatialPatch z₀))
        let Ω := ball a (2 * ρ)
        closedBall a (2 * ρ) ⊆ domain T ∧
        MapsTo Prod.fst (closedBall a (2 * ρ))
          (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
            (ball (0 : Euclidean n) T.physicalRadius ∩ interior K)) ∧
        let e := adaptedCoordinates T.data.adapted
        let Cc := coordinates (Z := Euclidean 3) e
        let pc := ((0 : Euclidean (n - 1)), z₀)
        ∃ Dc : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        ∃ φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
          IsOpen Dc ∧ Ioo (-τc) τc ×ˢ ball pc (Rc / 32) ⊆ Dc ∧
          Dc ⊆ Ioo (-τc) τc ×ˢ ball pc (Rc / 4) ∧
          MapsTo (fun q ↦ (q.1, φ q)) (Ioo (-τc) τc ×ˢ ball pc (Rc / 8)) Dc ∧
          MapsTo (fun q ↦ (q.1, y q)) Dc (Ioo (-τc) τc ×ˢ ball pc (Rc / 8)) ∧
          (∀ p ∈ ball pc (Rc / 8), φ (0, p) = p) ∧
          (∀ p ∈ ball pc (Rc / 8), ∀ t ∈ Ioo (-τc) τc, y (t, φ (t, p)) = p) ∧
          (∀ q ∈ Dc, φ (q.1, y q) = q.2) ∧
          (∀ p ∈ ball pc (Rc / 8), ∀ t ∈ Ioo (-τc) τc, HasDerivAt (fun s ↦ φ (s, p))
            ((e (carrierTransportDirection T Q row col (Cc.symm (t, φ (t, p))))).2, 0) t) ∧
          ContDiffOn ℝ ∞ φ (Ioo (-(2 * τc)) (2 * τc) ×ˢ ball pc (Rc / 4)) ∧
          cNorm (Icc (-τc) τc ×ˢ closedBall pc (Rc / 8)) 1 φ ≤ Mc ∧
      let p₀ := ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀))
      let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1))
        (adaptedCoordinates T.data.adapted)
      let Bρ := closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) ρ
      let I := Ioo (-τ) τ
      let L := ball p₀ (R / 8)
      let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
      let W := C.symm '' (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64))
      ∃ D : Set (ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))),
      ∃ Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
        Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)),
        IsOpen D ∧ I ×ˢ ball p₀ (R / 32) ⊆ D ∧ D ⊆ I ×ˢ ball p₀ (R / 4) ∧
        C ⁻¹' D ⊆ Ω ∧
        closedBall a (2 * σ) ⊆ C ⁻¹' D ∧
        (∀ (y : Euclidean (n - 1)) (z : Euclidean 3) (ζ : Euclidean (n - 1)),
          (T.data.adapted.embedding y, (z, ζ)) ∈ closedBall a (2 * σ) →
          phase T Q (T.data.adapted.embedding y) ζ = inner ℝ y ζ) ∧
        ContDiffOn ℝ ∞ Φ (I ×ˢ L) ∧ ContDiffOn ℝ ∞ Y D ∧
        MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ L) D ∧
        MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ L) ∧
        (∀ p ∈ L, Φ (0, p) = p) ∧
        (∀ p ∈ L, ∀ t ∈ I, Y (t, Φ (t, p)) = p) ∧
        (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
        (∀ p ∈ L, ∀ t ∈ I, (Φ (t, p)).2.1 = p.2.1 ∧ (Φ (t, p)).2.2 = p.2.2) ∧
        (∀ q ∈ D, (Y q).2.1 = q.2.2.1 ∧ (Y q).2.2 = q.2.2.2) ∧
        (∀ p ∈ L, ∀ t ∈ I, HasDerivAt (fun s ↦ Φ (s, p))
          ((adaptedCoordinates T.data.adapted
            (transportDirection T Q row col (C.symm (t, Φ (t, p))))).2, 0) t) ∧
        ContDiffOn ℝ ∞ Φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
        ContDiffOn ℝ ∞ Y (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
        (∀ j, cNorm J j Φ + cNorm J j Y ≤ H j * (1 + cNorm K (j + 5) F)) ∧
        (∀ w ∈ C ⁻¹' D,
          b ≤ ‖nullvector T Q col w‖ ∧ b ≤ ‖phaseGradient T Q w.1 w.2.2‖ ∧
          reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
            (fun i ↦ nullvector T Q col w i) = 0 ∧
          conullvector T Q row w ᵥ*
            reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) = 0) ∧
        (∀ j, cNorm Bρ j (nullvector T Q col) +
          cNorm Bρ j (conullvector T Q row) +
          cNorm Bρ j (adaptedDenominator T Q row col) +
          cNorm Bρ j (fun w ↦ (adaptedDenominator T Q row col w)⁻¹) +
          cNorm Bρ j (transportDirection T Q row col) +
          cNorm Bρ j (transportPotential T Q F row col) ≤ A j * (1 + cNorm K (j + 5) F)) ∧
        (∀ q ∈ Ioo (-δcomp) δcomp ×ˢ ball pc rcomp,
          q ∈ Dc ∧ (q.1, carrierLabel T q.2) ∈ D ∧
          (∀ t ∈ Ioo (-δcomp) δcomp,
            Φ (t, carrierLabel T (y q)) = carrierLabel T (φ (t, y q))) ∧
          Y (q.1, carrierLabel T q.2) = carrierLabel T (y q) ∧
          ∀ initial : Euclidean (n - 1) × Euclidean 3 → ℝ,
            let w := Cc.symm q
            scalarAmplitude T Q F row col Φ Y initial
                (w.1, (w.2, T.reference.spatialPatch w.2)) =
              carrierScalarAmplitude T Q F row col φ y initial w ∧
            scalarAmplitude T Q F row col Φ Y initial
                (w.1, (w.2, T.reference.spatialPatch w.2)) •
                nullvector T Q col (w.1, (w.2, T.reference.spatialPatch w.2)) =
              carrierScalarAmplitude T Q F row col φ y initial w • carrierNullvector T Q col w) ∧
        ∀ r : Euclidean (n - 1) × Euclidean 3 → ℝ,
          ContDiffOn ℝ ∞ r (ball ((0 : Euclidean (n - 1)), z₀) (R / 4)) →
          cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) 14 r ≤ Mᵣ →
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8), m ≤ r p) →
          let α := scalarAmplitude T Q F row col Φ Y r
          ContDiffOn ℝ ∞ α (C ⁻¹' D) ∧
          ContDiffOn ℝ ∞ (fun w ↦ α w • nullvector T Q col w) (C ⁻¹' D) ∧
          (∀ p ∈ L, α (T.data.adapted.embedding p.1, p.2) = r (p.1, p.2.1)) ∧
          (∀ w ∈ C ⁻¹' D, g ≤ α w ∧ 0 < α w ∧
            nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0 ∧
            α w • nullvector T Q col w ≠ 0) ∧
          (∀ w ∈ C ⁻¹' D,
            fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (transportDirection T Q row col w) +
              transportPotential T Q F row col w * α w = 0) ∧
          (∀ w ∈ C ⁻¹' D,
            reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
              (fun j ↦ (α w • nullvector T Q col w) j) = 0) ∧
          (∀ w ∈ C ⁻¹' D, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
            (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1 = 0) ∧
          (∀ j, cNorm W j α + cNorm W j (fun w ↦ α w • nullvector T Q col w) ≤
            B j * (1 + cNorm K (j + 13) F +
              cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 13) r)) ∧
              (∀ w ∈ C ⁻¹' D,
                cν ≤ ‖principalNormal (canonicalNormalCompletion F w.1)
                  (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)‖ ∧
                determinant (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) = 0 ∧
                (1 / 2 : ℝ) • linearizedMetric F
                    (reconstruction F (canonicalNormalCompletion F) (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2))) w.1 =
                  stressProjection F w.1 (symmCovariantDeriv F (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1) ∧
                (∀ τ' : ℝ, τ' ≠ 0 →
                  completedVariationComplex F
                    (fun x ↦ (τ' : ℂ) ^ 2 •
                      Complex.exp (Complex.I * (phase T Q x w.2.2 : ℂ) / (τ' : ℂ)) •
                        euclideanComplexInclusion (α (x, w.2) • nullvector T Q col (x, w.2))) 0 w.1 =
                    Complex.exp (Complex.I * (phase T Q w.1 w.2.2 : ℂ) / (τ' : ℂ)) •
                      ((Complex.I * (τ' : ℂ)) • euclideanComplexInclusion
                        (principalNormal (canonicalNormalCompletion F w.1)
                          (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)) +
                      (τ' : ℂ) ^ 2 • euclideanComplexInclusion
                        (reconstruction F (canonicalNormalCompletion F) (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1))) ∧
                hermitianTensor ((principalMatrix
                    (principalNormal (canonicalNormalCompletion F w.1)
                      (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w))
                    (phaseGradient T Q w.1 w.2.2)).map Complex.ofReal) =
                  fun i j ↦ ‖principalNormal (canonicalNormalCompletion F w.1)
                    (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)‖ ^ 2 *
                      phaseGradient T Q w.1 w.2.2 i * phaseGradient T Q w.1 w.2.2 j) ∧
          let J₀ := closedBall a σ
          let b₀ := fun w ↦ α w • nullvector T Q col w
          let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
            phaseGradient T Q w.1 w.2.2
          let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
          let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
          ∀ j, cNorm J₀ j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J₀ j b₀ +
            cNorm J₀ j ν + cNorm J₀ j V + cNorm J₀ j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
              E j * (1 + cNorm K (j + 14) F +
                cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r) := by
  obtain ⟨η, ε, hη, hε, centers, row, col, ρ, R, τ, Rc, τc, Mc, rcomp, δcomp, σ,
    hpositive, Ωc, ρc, Bc, gc, _hgeometry, εcarrier, ρdet, hcell, hcarrierCover,
    V, hV, hgraph, hcover, hproduce⟩ :=
    exists_finite_retained_leading_family_before_geometry_with_carrier_data hn hP T hK hKU hball
  refine ⟨η, ε, hη, hε, centers, row, col, ρ, R, τ, Rc, τc, Mc, rcomp, δcomp, σ,
    hpositive, εcarrier, ρdet, hcell, hcarrierCover, V, hV, hgraph, hcover, ?_⟩
  intro M Mᵣ κmet κnormal m hM hMᵣ hκmet hκnormal hm
  obtain ⟨c, E, A, H, B, hc, hE, hactual⟩ :=
    hproduce M Mᵣ κmet κnormal m hM hMᵣ hκmet hκnormal hm
  refine ⟨c, E, A, H, B, hc, hE, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  obtain ⟨hlow, hspec⟩ := hactual F hF hi hrank hFM hmet hnormal hclose
  refine ⟨hlow, ?_⟩
  dsimp only
  intro j
  obtain ⟨hdom, hx, Dc, φ, y, _hdata, hrest⟩ := hspec j
  exact ⟨hdom, hx, Dc, φ, y, hrest⟩

end JanetCartan.CurrentCoefficientProfiles
