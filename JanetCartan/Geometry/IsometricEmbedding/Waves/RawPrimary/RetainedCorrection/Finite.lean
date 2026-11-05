module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.RetainedCorrection.CellBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.RetainedCover.Finite

/-!
# Finite retained correction before the geometric budgets

Enrich the original retained leading constructor on its own witnesses. All
centers, covering and estimate balls, selected indices, carrier/full domains,
flows, compatibility and leading estimates are preserved. The cell deduction
also applies directly to an already initialized family, so it does not require
identifying this existential selection with a second initializer.

Consumer: the actual raw primary fields, `app:ch_waves:thm:individual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.RawPrimary.RetainedCorrection
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase FlowAmplitude
open ProjectedStressFrame AmbientResponse ResponseTransfer
open LeadingWave LeadingWave.FullModulation LeadingWave.FullModulation.CarrierCompatibility
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.LeadingPrimitive ContinuumRow.LeadingCarrier
open FullPhaseCharts.ActualComparison

/-- The original retained finite leading family, chosen before all geometric
and scalar budgets, carries its literal orthogonal correction. The reserve is
fourteen, with constants before the immersion, scalar and frequency. The
correction estimate holds on the doubled working balls; the original radius-`σ`
cover and every carrier/full-flow conclusion are retained unchanged
(`app:ch_waves:eq:primary-algebraic-correction`, `app:ch_waves:eq:WKB-grading`,
`app:ch_waves:thm:individual`). -/
theorem exists_finite_retained_corrected_family_before_geometry {n : ℕ} (hn : 5 ≤ n)
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
      ∃ c : ℝ, ∃ E Γ : ℕ → ℝ, ∃ A H B : centers → ℕ → ℝ,
        0 < c ∧ (∀ j, 0 < E j) ∧ (∀ j, 0 < Γ j) ∧
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
          (∀ j, cNorm J₀ j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J₀ j b₀ +
            cNorm J₀ j ν + cNorm J₀ j V + cNorm J₀ j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
              E j * (1 + cNorm K (j + 14) F +
                cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r)) ∧
          ContDiffOn ℝ ∞ (fullCorrectionCovector T Q F row col Φ Y r) (C ⁻¹' D) ∧
          (∀ w ∈ C ⁻¹' D,
            Complex.I • ((reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).map
              Complex.ofReal *ᵥ (fun i ↦ fullCorrectionCovector T Q F row col Φ Y r w i)) +
              (fun i ↦ (reducedOperator F Q.1
                (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1 i : ℂ)) = 0) ∧
          ∀ k, cNorm (closedBall a (2 * σ)) k (fullCorrectionCovector T Q F row col Φ Y r) ≤
            Γ k * (1 + cNorm K (k + 14) F +
              cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (k + 14) r) := by
  classical
  choose η ε hη hε centers row col ρ R τ Rc τc Mc rcomp δcomp σ
    hpos Ωc ρc Bc gc hcarrier hworking εcarrier ρdet hcells hcarrierCover
    V hV hgraph hcover hlocal using
    CurrentCoefficientProfiles.exists_finite_retained_leading_family_before_geometry_with_carrier_data_and_working_balls
      hn hP T hK hKU hball
  refine ⟨η, ε, hη, hε, centers, row, col, ρ, R, τ, Rc, τc, Mc, rcomp, δcomp, σ,
    hpos, Ωc, ρc, Bc, gc, hcarrier, hworking, εcarrier, ρdet, hcells, hcarrierCover,
    V, hV, hgraph, hcover, ?_⟩
  intro M Mᵣ κmet κnormal m hM hMᵣ hκmet hκnormal hm
  choose c E A H B hc hE hactual using hlocal M Mᵣ κmet κnormal m hM hMᵣ hκmet hκnormal hm
  have hbud (j : centers) := by
    rcases hpos j with ⟨hρ, hR, hτ, _hRc, _hτc, _hMc, _hrcomp, _hδcomp, hσ⟩
    exact exists_retained_cell_correction_bounds (N := embeddingDimension n)
      T hK hKU hball j.1.1 (row j) (col j) hρ hR hτ hσ M Mᵣ (B j)
        hκmet hκnormal hc (hworking j).1 (hworking j).2.1
  choose G hG hbudget using hbud
  let Γ := fun k ↦ 1 + ∑ j : centers, G j k
  have hΓ (k) : 0 < Γ k := by
    have hh : 0 ≤ ∑ j : centers, G j k := Finset.sum_nonneg (fun j _ ↦ (hG j k).le)
    change 0 < 1 + ∑ j : centers, G j k
    linarith
  have hGΓ (j : centers) (k) : G j k ≤ Γ k := by
    have hh := Finset.single_le_sum (f := fun i : centers ↦ G i k)
      (fun i _ ↦ (hG i k).le) (Finset.mem_univ j)
    change G j k ≤ 1 + ∑ i : centers, G i k
    linarith
  refine ⟨c, E, Γ, A, H, B, hc, hE, hΓ, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  choose hlow hfamily using hactual F hF hi hrank hFM hmet hnormal hclose
  refine ⟨hlow, ?_⟩
  dsimp only
  intro j
  choose hdom hx Dc φ y hcarrierData hDc hcoverc hbigc hφDc hyL hφ₀ hyφ hφy
    hvelocityc hφbuffer hflowcLow D Φ Y hD hcoverD hbig hphys hballD hphaseInitial
    hΦ hY hΦD hYL hΦ₀ hYΦ hΦY hΦz hYz hvelocity
    hΦbuffer hYbuffer hflow hgaps hcoeff hcompat hsolution using hfamily j
  refine ⟨hdom, hx, Dc, φ, y, hcarrierData, hDc, hcoverc, hbigc, hφDc, hyL, hφ₀, hyφ, hφy,
    hvelocityc, hφbuffer, hflowcLow, D, Φ, Y, hD, hcoverD, hbig, hphys, hballD, hphaseInitial,
    hΦ, hY, hΦD, hYL, hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity,
    hΦbuffer, hYbuffer, hflow, hgaps, hcoeff, hcompat, ?_⟩
  intro r hr hrM hrmin
  rcases hsolution r hr hrM hrmin with
    ⟨hα, hb₀, hinit, hpositive, hpde, hsymbol, hreduce, habound, hidentity, hjoint⟩
  obtain ⟨hsmooth, hcancel, hbound⟩ := hbudget j F hF hi hrank hFM hmet hnormal hlow
    hdom hx D Φ Y hD hcoverD hphys (fun w hw ↦ (hgaps w hw).1) r hrM hα
    (fun w hw ↦ ⟨(hpositive w hw).2.2.1, (hpositive w hw).2.2.2.1⟩) hreduce habound
  refine ⟨hα, hb₀, hinit, hpositive, hpde, hsymbol, hreduce, habound, hidentity,
    hjoint, hsmooth, hcancel, ?_⟩
  intro k
  exact (hbound k).trans (mul_le_mul_of_nonneg_right (hGΓ j k)
    (by linarith [cNorm_nonneg K (k + 14) F,
      cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), j.1.1) (R j / 8)) (k + 14) r]))

end JanetCartan.RawPrimary.RetainedCorrection
