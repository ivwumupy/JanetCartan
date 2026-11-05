module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.FullModulationBounds
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.FullModulationConstruction.CarrierFlow
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.FullModulationConstruction.Transport
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Reconstruction
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.ActualCompatibility

/-!
# Actual local full modulation with geometry chosen first

The frame threshold, actual minor and both transport and compatibility domains
precede source-dependent geometric and scalar budgets. Only positive amplitude
and normal gaps and high constants depend on those later budgets. The literal
carrier/full flows agree by the existing ODE uniqueness theorem, and the scalar
retains its original datum (`main:prop:current-scale`, `app:ch_waves:thm:leading`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.CurrentCoefficientProfiles
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase FlowAmplitude
open ProjectedStressFrame AmbientResponse ResponseTransfer
open LeadingWave LeadingWave.FullModulation LeadingWave.FullModulation.CarrierCompatibility

/-- Actual local full-modulation amplitudes with all geometric domains and the
frame threshold chosen before the primitive budgets. The same carrier maps retain
their coefficient, inverse-buffer and parameter-preservation evidence for
`PositiveReference.FlowConstruction.Chart`; the independent full and carrier
radii and original initial scalar are preserved (`app:ch_waves:thm:leading`,
`app:ch_background:prop:bg-frame`).
The comparison bound `8 * rcomp ≤ Rc / 32` is retained from
`CarrierCompatibility.exists_comparison_radii` before budgets and finite selection.
It supplies `RetainedRowGeometry.exists_original_outputCylinder_region` on these
same witnesses (`app:ch_background:eq:bg-Psi`, `app:ch_background:prop:bg-frame`,
paper-v2.tex `app:ch_osc:prop:osc-normal`, Step 4'). -/
theorem exists_full_local_amplitude_before_geometry_with_source_geometry {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z₀ : Euclidean 3) (hz₀ : z₀ ∈ parameterCube P.radius) :
    ∃ row col : Fin n, ∃ ρ R η τ b Rc τc Mc rcomp δcomp : ℝ,
    ∃ Ωc : Set (Euclidean n × Euclidean 3), ∃ ρc Bc gc μc Bfull : ℝ,
      (0 < μc ∧
        (∀ σ ∈ Ioc (0 : ℝ) 1,
          MapsTo (fun w : Euclidean n × Euclidean 3 ↦ (σ • w.1, w.2)) Ωc Ωc) ∧
        closedBall ((0 : Euclidean n), z₀) (2 * ρc) ⊆ Ωc ∧
        closedBall ((0 : Euclidean n), z₀) (2 * ρc) ⊆
          (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
            parameterInterior (3 * P.radius / 2) ∧
        MapsTo Prod.fst (closedBall ((0 : Euclidean n), z₀) (2 * ρc))
          (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
        ∀ w ∈ closedBall ((0 : Euclidean n), z₀) (2 * ρc),
          2 * μc ≤ |(cubePencil (P.toFun w.2)).adjugate row col|) ∧
      0 < Bfull ∧
      τ = existenceTime R (LeadingWave.FullModulation.liftedLowBound T Bfull) / 4 ∧
      8 * rcomp ≤ Rc / 32 ∧
      0 < ρ ∧ 0 < R ∧ 0 < η ∧ 0 < τ ∧ 0 < b ∧
      0 < Rc ∧ 0 < τc ∧ 0 < Mc ∧ 0 < rcomp ∧ 0 < δcomp ∧ τ ≤ R / 16 ∧
      let a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
        (0, (z₀, T.reference.spatialPatch z₀))
      let Ω := ball a (2 * ρ)
      closedBall a (2 * ρ) ⊆ domain T ∧
      MapsTo Prod.fst (closedBall a (2 * ρ))
        (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
          (ball (0 : Euclidean n) T.physicalRadius ∩ interior K)) ∧
      MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
        (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)),
          (z₀, T.reference.spatialPatch z₀))) R) (closedBall a ρ) ∧
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
        τc ≤ Rc / 16) ∧
      ∀ M₁₂ Mᵣ κmet κnormal m : ℝ, 0 ≤ M₁₂ → 0 ≤ Mᵣ →
        0 < κmet → 0 < κnormal → 0 < m →
      ∃ g cν : ℝ, ∃ A H B : ℕ → ℝ,
        0 < g ∧ 0 < cν ∧ (∀ j, 0 < A j) ∧ (∀ j, 0 < H j) ∧ (∀ j, 0 < B j) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 12 F ≤ M₁₂ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        let e := adaptedCoordinates T.data.adapted
        let Cc := coordinates (Z := Euclidean 3) e
        let pc := ((0 : Euclidean (n - 1)), z₀)
        cNorm (closedBall a ρ) 1 (transportDirection T Q row col) ≤ Bfull ∧
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
          cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) 5 r ≤ Mᵣ →
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
                      phaseGradient T Q w.1 w.2.2 i * phaseGradient T Q w.1 w.2.2 j) := by
  obtain ⟨row, col, ρc, Rc, ηc, τc, gc, Mc, Ωc, Bc, μc, hsource, _hρc, hRc, hηc, hτc, hgc, hMc,
    _hbufferC, _hτRc, hgeometryc, hcarrier⟩ :=
    exists_carrier_flow_before_geometry_with_source_geometry (N := embeddingDimension n)
      (by omega : 2 ≤ n) hP T hK hKU hball z₀ hz₀
  obtain ⟨ηf, ρ, b, Bd, hηf, _hηfT, hρ, hb, hBd,
    hΩ, hsmallΩ, hdom, hx, hcoeff⟩ :=
    exists_full_modulation_coefficient_bounds_before_geometry (N := embeddingDimension n)
      (by omega : 2 ≤ n) hP T hK hKU hball row col z₀ hz₀ hgc
  obtain ⟨R, τ, Mf, hτeq, hR, hτ, hMf, hτR, hbuffer, hfull⟩ :=
    exists_full_transport_before_geometry_with_exact_time (N := embeddingDimension n) T K z₀ hρ hΩ hsmallΩ hBd.le
  obtain ⟨δ, hδ, hnormal⟩ := exists_full_modulation_normal_threshold_before_budgets hn hU hK hKU
  let Mv := Mc + Mf
  have hMv : 0 ≤ Mv := add_nonneg hMc.le hMf.le
  obtain ⟨Rg, Lg, hRg, hLg, hgraph⟩ := exists_local_carrierLabel_lipschitz
    T hP ((0 : Euclidean (n - 1)), z₀) hz₀
  obtain ⟨rcomp, δcomp, hrcomp, hδcomp, hδc, hδf, hrc, hrf, hMδ, hrg⟩ :=
    exists_comparison_radii hRc hR hRg hτc hτ hMv hLg
  refine ⟨row, col, ρ, R, min ηc (min ηf δ), τ, b, Rc, τc,
    Mc, rcomp, δcomp, Ωc, ρc, Bc, gc, μc, Bd, hsource, hBd, hτeq, hrc, hρ, hR, lt_min hηc (lt_min hηf hδ),
    hτ, hb, hRc, hτc, hMc, hrcomp, hδcomp, hτR, hdom, hx, hbuffer, hgeometryc, ?_⟩
  intro M₁₂ Mᵣ κmet κnormal m hM₁₂ hMᵣ hκmet hκnormal hm
  obtain ⟨A, hA, hcoeff⟩ := hcoeff M₁₂ κmet κnormal hκmet hκnormal
  obtain ⟨g, H, B, hg, hH, hB, hfull⟩ := hfull A hA M₁₂ Mᵣ m hM₁₂ hMᵣ hm
  obtain ⟨cν, hcν, hnormalGap⟩ := hnormal M₁₂ b (g * b) hb (mul_pos hg hb)
  refine ⟨g, cν, A, H, B, hg, hcν, hA, hH, hB, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  have hF4 : cNorm K 4 F ≤ M₁₂ := (cNorm_mono_order (by omega)).trans hFM
  obtain ⟨hlow, Dc, φ, y, hcarrierData, hDc, hcoverc, hbigc, _hphysc, _hφ, _hy, hφDc, hyL,
    hφ₀, hyφ, hφy, _hcz, _hyz, hvelocityc, hφbuffer, hflowcLow, hgapc⟩ :=
    hcarrier M₁₂ κmet κnormal hκmet hκnormal F hF hi hrank hF4 hmet hnormal
      (hclose.trans_le (min_le_left _ _))
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
      {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  let Cc := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  have hcenter : Cc ((0 : Euclidean n), z₀) ∈ Dc := by
    apply hcoverc
    have he : Cc ((0 : Euclidean n), z₀) = (0, 0, z₀) := by simp [Cc]
    rw [he]
    exact ⟨⟨by linarith, hτc⟩, mem_ball_self (by positivity)⟩
  have hcenterGap : gc ≤ |carrierAdaptedDenominator T Q row col (0, z₀)| :=
    hgapc _ hcenter
  obtain ⟨hlowf, hcoefff⟩ := hcoeff F hF hi hrank hF4 hmet hnormal
    (hclose.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨hk, _hl, _hd, _hinv, hdir, hpot, hgap, hdirLow, hhigh⟩ := hcoefff hcenterGap
  let Ω := ball ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) (2 * ρ)
  have hΩU : ∀ w ∈ Ω, w.1 ∈ U :=
    fun w hw ↦ hKU (interior_subset (hx (ball_subset_closedBall hw)).2.2)
  have hsym : ∀ w ∈ Ω, ∀ i, (Q.1 w.1 i).IsSymm := fun w hw i ↦
    (projectedStress_mem_stressSpace
      ((hF.contDiffAt (hU.mem_nhds (hΩU w hw))).of_le (by simp)) (hrank w.1 (hΩU w hw)) i).1
  obtain ⟨D, Φ, Y, hD, hcover, hbig, hphys, hΦ, hY, hΦD, hYL,
    hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity, hΦbuffer, hYbuffer, hflowfLow, hflow, hsolution⟩ :=
    hfull Q F row col hk hdir hpot
      (fun w hw ↦ (hgap w (ball_subset_closedBall hw)).2.1) hsym
      (fun w hw ↦ hdom (ball_subset_closedBall hw)) hhigh hdirLow hFM
  have hspeedc p hp t ht : ‖carrierVelocity T Q row col t (φ (t, p))‖ ≤ Mv :=
    (flow_speed_le_cNorm hRc hτc hφbuffer hflowcLow hp ht (hvelocityc p hp t ht)).trans
      (le_add_of_nonneg_right hMf.le)
  have hspeedf p hp t ht : ‖fullVelocity T Q row col t (Φ (t, p))‖ ≤ Mv :=
    (flow_speed_le_cNorm hR hτ hΦbuffer hflowfLow hp ht (hvelocity p hp t ht)).trans
      (le_add_of_nonneg_left hMc.le)
  have hlip t (ht : t ∈ Ioo (-δcomp) δcomp) :
      LipschitzOnWith ⟨LeadingWave.FullModulation.liftedLowBound T Bd,
        LeadingWave.FullModulation.liftedLowBound_nonneg T hBd.le⟩
        (fullVelocity T Q row col t)
        (closedBall ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀)) (R / 2)) :=
    fullVelocity_lipschitz_of_direction_bound T Q row col hΩ
      (isCompact_closedBall _ _) hsmallΩ hdir hBd.le hR hτR hdirLow hbuffer
      (show t ∈ Ioo (-τ) τ from ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hcompat := compatibility_on_common_buffer T Q F row col
    hRc hR hrcomp hδcomp hMv hLg hδc hδf hrc hrf hMδ hrg hgraph
    hcoverc hcover (fun q hq ↦ (hyL hq).2) hφy hYΦ hφ₀ hΦ₀
    hvelocityc hvelocity hspeedc hspeedf hlip
  refine ⟨hlow, hdirLow, Dc, φ, y, hcarrierData, hDc, hcoverc, hbigc, hφDc, hyL, hφ₀, hyφ, hφy,
    hvelocityc, hφbuffer, hflowcLow, D, Φ, Y, hD, hcover, hbig, hphys,
    hΦ, hY, hΦD, hYL, hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity,
    hΦbuffer, hYbuffer, hflow, ?_, hhigh, hcompat, ?_⟩
  · intro w hw
    have hh := hgap w (ball_subset_closedBall (hphys hw))
    exact ⟨hh.2.2.2.1, hh.2.2.2.2.2.1,
      nullvector_relations T Q row col (hdom (ball_subset_closedBall (hphys hw)))⟩
  · intro r hr hrLow hrmin
    obtain ⟨hα, hαk, hinitial, hpos, hpde, hsymbol, hreduce, htame⟩ :=
      hsolution r hr hrLow hrmin
    refine ⟨hα, hαk, hinitial, hpos, hpde, hsymbol, hreduce, htame, ?_⟩
    let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1))
      (adaptedCoordinates T.data.adapted)
    have hident := reconstruction_identities T hF hi hrank hlow
      (hD.preimage C.continuous) (fun w hw ↦ ⟨hΩU w (hphys hw), mem_univ _⟩)
      (fun w hw ↦ hdom (ball_subset_closedBall (hphys hw))) hαk
    intro w hw
    have hwK : w.1 ∈ K := interior_subset (hx (ball_subset_closedBall (hphys hw))).2.2
    have hgaps := hgap w (ball_subset_closedBall (hphys hw))
    have hαpos := (hpos w hw).2.1
    have hamp : g * b ≤ ‖scalarAmplitude T Q F row col Φ Y r w • nullvector T Q col w‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hαpos]
      exact mul_le_mul (hpos w hw).1 hgaps.2.2.2.1 hb.le hαpos.le
    refine ⟨hnormalGap F hF hi hrank hF4
      (hclose.trans_le ((min_le_right _ _).trans (min_le_right _ _))) w.1 hwK
      _ _ (hsymbol w hw) hgaps.2.2.2.2.2.1 hamp,
      (hident w hw).1, (hident w hw).2.1, (hident w hw).2.2,
      principalNormal_hermitianTensor F w.1 _ _⟩

/-- Original comparison-radius endpoint projected from the construction
retaining source geometry and the separate full-modulation direction bound and
exact time (`app:ch_waves:thm:leading`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_full_local_amplitude_before_geometry_with_carrier_data_and_comparison_radius {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z₀ : Euclidean 3) (hz₀ : z₀ ∈ parameterCube P.radius) :
    ∃ row col : Fin n, ∃ ρ R η τ b Rc τc Mc rcomp δcomp : ℝ,
    ∃ Ωc : Set (Euclidean n × Euclidean 3), ∃ ρc Bc gc : ℝ,
      8 * rcomp ≤ Rc / 32 ∧
      0 < ρ ∧ 0 < R ∧ 0 < η ∧ 0 < τ ∧ 0 < b ∧
      0 < Rc ∧ 0 < τc ∧ 0 < Mc ∧ 0 < rcomp ∧ 0 < δcomp ∧ τ ≤ R / 16 ∧
      let a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
        (0, (z₀, T.reference.spatialPatch z₀))
      let Ω := ball a (2 * ρ)
      closedBall a (2 * ρ) ⊆ domain T ∧
      MapsTo Prod.fst (closedBall a (2 * ρ))
        (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
          (ball (0 : Euclidean n) T.physicalRadius ∩ interior K)) ∧
      MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
        (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)),
          (z₀, T.reference.spatialPatch z₀))) R) (closedBall a ρ) ∧
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
        τc ≤ Rc / 16) ∧
      ∀ M₁₂ Mᵣ κmet κnormal m : ℝ, 0 ≤ M₁₂ → 0 ≤ Mᵣ →
        0 < κmet → 0 < κnormal → 0 < m →
      ∃ g cν : ℝ, ∃ A H B : ℕ → ℝ,
        0 < g ∧ 0 < cν ∧ (∀ j, 0 < A j) ∧ (∀ j, 0 < H j) ∧ (∀ j, 0 < B j) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 12 F ≤ M₁₂ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
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
          cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) 5 r ≤ Mᵣ →
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
                      phaseGradient T Q w.1 w.2.2 i * phaseGradient T Q w.1 w.2.2 j) := by
  obtain ⟨row, col, ρ, R, η, τ, b, Rc, τc, Mc, rcomp, δcomp,
    Ωc, ρc, Bc, gc, _μc, _Bfull, _hsource, _hBfull, _hτeq,
    hcomp, hρ, hR, hη, hτ, hb, hRc, hτc, hMc, hrcomp, hδcomp,
    hτR, hdom, hx, hbuffer, hgeometryc, hactual⟩ :=
    exists_full_local_amplitude_before_geometry_with_source_geometry hn hP T hK hKU hball z₀ hz₀
  refine ⟨row, col, ρ, R, η, τ, b, Rc, τc, Mc, rcomp, δcomp,
    Ωc, ρc, Bc, gc, hcomp, hρ, hR, hη, hτ, hb, hRc, hτc, hMc, hrcomp, hδcomp,
    hτR, hdom, hx, hbuffer, hgeometryc, ?_⟩
  intro M₁₂ Mᵣ κmet κnormal m hM₁₂ hMᵣ hκmet hκnormal hm
  obtain ⟨g, cν, A, H, B, hg, hcν, hA, hH, hB, hactual⟩ :=
    hactual M₁₂ Mᵣ κmet κnormal m hM₁₂ hMᵣ hκmet hκnormal hm
  refine ⟨g, cν, A, H, B, hg, hcν, hA, hH, hB, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  obtain ⟨hlow, _hdirLow, hrest⟩ := hactual F hF hi hrank hFM hmet hnormal hclose
  exact ⟨hlow, hrest⟩

/-- Original entry point, retaining every witness and conclusion of the strengthened
comparison-radius constructor and forgetting only its additional bound
(`app:ch_background:eq:bg-Psi`, `app:ch_background:prop:bg-frame`). -/
theorem exists_full_local_amplitude_before_geometry_with_carrier_data {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z₀ : Euclidean 3) (hz₀ : z₀ ∈ parameterCube P.radius) :
    ∃ row col : Fin n, ∃ ρ R η τ b Rc τc Mc rcomp δcomp : ℝ,
    ∃ Ωc : Set (Euclidean n × Euclidean 3), ∃ ρc Bc gc : ℝ,
      0 < ρ ∧ 0 < R ∧ 0 < η ∧ 0 < τ ∧ 0 < b ∧
      0 < Rc ∧ 0 < τc ∧ 0 < Mc ∧ 0 < rcomp ∧ 0 < δcomp ∧ τ ≤ R / 16 ∧
      let a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
        (0, (z₀, T.reference.spatialPatch z₀))
      let Ω := ball a (2 * ρ)
      closedBall a (2 * ρ) ⊆ domain T ∧
      MapsTo Prod.fst (closedBall a (2 * ρ))
        (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
          (ball (0 : Euclidean n) T.physicalRadius ∩ interior K)) ∧
      MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
        (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)),
          (z₀, T.reference.spatialPatch z₀))) R) (closedBall a ρ) ∧
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
        τc ≤ Rc / 16) ∧
      ∀ M₁₂ Mᵣ κmet κnormal m : ℝ, 0 ≤ M₁₂ → 0 ≤ Mᵣ →
        0 < κmet → 0 < κnormal → 0 < m →
      ∃ g cν : ℝ, ∃ A H B : ℕ → ℝ,
        0 < g ∧ 0 < cν ∧ (∀ j, 0 < A j) ∧ (∀ j, 0 < H j) ∧ (∀ j, 0 < B j) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 12 F ≤ M₁₂ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
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
          cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) 5 r ≤ Mᵣ →
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
                      phaseGradient T Q w.1 w.2.2 i * phaseGradient T Q w.1 w.2.2 j) := by
  obtain ⟨row, col, ρ, R, η, τ, b, Rc, τc, Mc, rcomp, δcomp,
    Ωc, ρc, Bc, gc, _hrc, hrest⟩ :=
    exists_full_local_amplitude_before_geometry_with_carrier_data_and_comparison_radius hn hP T hK hKU hball z₀ hz₀
  exact ⟨row, col, ρ, R, η, τ, b, Rc, τc, Mc, rcomp, δcomp,
    Ωc, ρc, Bc, gc, hrest⟩

/-- Original endpoint, projected from the joint carrier-data constructor for
`app:ch_waves:thm:leading`. All witnesses and conclusions are unchanged. -/
theorem exists_full_local_amplitude_before_geometry {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z₀ : Euclidean 3) (hz₀ : z₀ ∈ parameterCube P.radius) :
    ∃ row col : Fin n, ∃ ρ R η τ b Rc τc Mc rcomp δcomp : ℝ,
      0 < ρ ∧ 0 < R ∧ 0 < η ∧ 0 < τ ∧ 0 < b ∧
      0 < Rc ∧ 0 < τc ∧ 0 < Mc ∧ 0 < rcomp ∧ 0 < δcomp ∧ τ ≤ R / 16 ∧
      let a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
        (0, (z₀, T.reference.spatialPatch z₀))
      let Ω := ball a (2 * ρ)
      closedBall a (2 * ρ) ⊆ domain T ∧
      MapsTo Prod.fst (closedBall a (2 * ρ))
        (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
          (ball (0 : Euclidean n) T.physicalRadius ∩ interior K)) ∧
      MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
        (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)),
          (z₀, T.reference.spatialPatch z₀))) R) (closedBall a ρ) ∧
      ∀ M₁₂ Mᵣ κmet κnormal m : ℝ, 0 ≤ M₁₂ → 0 ≤ Mᵣ →
        0 < κmet → 0 < κnormal → 0 < m →
      ∃ g cν : ℝ, ∃ A H B : ℕ → ℝ,
        0 < g ∧ 0 < cν ∧ (∀ j, 0 < A j) ∧ (∀ j, 0 < H j) ∧ (∀ j, 0 < B j) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 12 F ≤ M₁₂ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
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
          cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) 5 r ≤ Mᵣ →
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
                      phaseGradient T Q w.1 w.2.2 i * phaseGradient T Q w.1 w.2.2 j) := by
  obtain ⟨row, col, ρ, R, η, τ, b, Rc, τc, Mc, rcomp, δcomp,
    Ωc, ρc, Bc, gc, hρ, hR, hη, hτ, hb, hRc, hτc, hMc, hrcomp, hδcomp,
    hτR, hdom, hx, hbuffer, _hgeometry, hactual⟩ :=
    exists_full_local_amplitude_before_geometry_with_carrier_data hn hP T hK hKU hball z₀ hz₀
  refine ⟨row, col, ρ, R, η, τ, b, Rc, τc, Mc, rcomp, δcomp,
    hρ, hR, hη, hτ, hb, hRc, hτc, hMc, hrcomp, hδcomp, hτR, hdom, hx, hbuffer, ?_⟩
  intro M Mᵣ κmet κnormal m hM hMᵣ hκmet hκnormal hm
  obtain ⟨g, cν, A, H, B, hg, hcν, hA, hH, hB, hactual⟩ :=
    hactual M Mᵣ κmet κnormal m hM hMᵣ hκmet hκnormal hm
  refine ⟨g, cν, A, H, B, hg, hcν, hA, hH, hB, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  obtain ⟨hlow, Dc, φ, y, _hdata, hrest⟩ := hactual F hF hi hrank hFM hmet hnormal hclose
  exact ⟨hlow, Dc, φ, y, hrest⟩

end JanetCartan.CurrentCoefficientProfiles
