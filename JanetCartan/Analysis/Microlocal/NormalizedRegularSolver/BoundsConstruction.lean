module

public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.Operators
public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.HalfBounds
public import JanetCartan.Analysis.Microlocal.EllipticComplement.DirectBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.ProtectedConstruction.SuppliedFamily.Operators

/-!
# Actual normalized complete construction on the supplied family

Apply both actual branch constructors to the same `f`, retaining the original
characteristic protection, phase, chart, masks and final collar. The extra
output cutoff is applied to the elliptic term before addition. All constants
are chosen before `Q` and the full zeroth-order field `B`. The source and the
gain-one residual are normalized separately. Sources: `sector-theorem-solution`,
`sector-theorem-residual`, `energy-complete-residual`, `measured-adjoint`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 16000000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.NormalizedSolver
open FiniteAssembly EllipticComplement
open Characteristic Characteristic.ResidualCoordinates Characteristic.UniformEvolution
open Characteristic.ConicAmplitude Characteristic.AmplitudeBounds Characteristic.RootFamily
open Characteristic.ConicPhase Characteristic.UniformAmplitudes Characteristic.EvolutionIntegral.SymbolBudgets
open Characteristic.EvolutionIntegral FiniteMasks FiniteMasks.ActualFamily
open FinitePdo FiniteEvolution FourierIntegral FourierIntegral.LowBounds Pseudodifferential
open JanetCartan.CharacteristicTransport.CompleteResidual
open Characteristic.RetardedLocalization LocalSobolev
open FiniteResidual.FiniteIdentity
open ActualCarriers Characteristic.AlgebraicChart Characteristic.AlgebraicSymbols
open Characteristic.PdoRealization FiniteAlgebraic AmplitudeBound
open ArbitraryAccuracy.ResidualLocalization ResponseTransfer.Complement
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "TPoint" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)

local notation "Coeff" => Fin (d+1) → Mat
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ

/-- The corrected complete solver on the ACTUAL supplied characteristic
family, with its actual elliptic complement. The collar premise is exactly
the original selected-family producer's input; no PDE or operator bound is
assumed. This constructs both signed fixed-shift estimates for the actual
half-sum and both literal-adjoint
local real residual bounds needed by the small-support inverse. The original
characteristic tested equation is retained on the SAME operators for the
normalized PDE continuation; it is constructed, not assumed. All retained
characteristic geometry belongs to the same `Φ`, `C`, `Op` and `f`.
Sources: `sector-theorem-identity`, `sector-theorem-residual`,
`energy-complete-residual`, `measured-adjoint`. -/
theorem exists_normalized_complete_operator_bounds_of_selected_collar
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (A₀ : Coeff) {K : Set E} (hK : IsCompact K) {M : ℝ} (hM : 0 ≤ M)
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hf : ∀ p : f.centers,
      let c := f.chart p
      let ξ := p.val.val
      c.bufferRadius ≤ c.targetRadius ∧ c.maskRadius ≤ c.bufferRadius / 4 ∧
      RootBuffer c.index c.row c.col A₀ ξ c.root c.coefficientRadius c.rootRadius
        c.minorGap c.transportGap ∧
      MapsTo (rootPhysicalPosition (coordinateSplit c.index)) (tsupport c.sourceMask)
        (closedBall x RQ) ∧
    ∃ evolutionTime speedGap rootSize rootCost,
      LocalProtectionCertificate c evolutionTime speedGap rootSize rootCost ∧
    ∃ a > (0 : ℝ), ∃ b > (0 : ℝ),
      a < c.coefficientRadius ∧ b < min c.coefficientRadius c.rootRadius ∧
      let KA := closedBall A₀ a
      let Kη := closedBall (coordinateSplit c.index ξ).2 b
      let x' := (physicalCoordinates c.index).symm x
      IsCompact KA ∧ IsCompact Kη ∧
      KA ⊆ ball A₀ c.coefficientRadius ∧
      Kη ⊆ ball (coordinateSplit c.index ξ).2 (min c.coefficientRadius c.rootRadius) ∧
      (∀ p ∈ ball A₀ c.coefficientRadius ×ˢ
        ball (coordinateSplit c.index ξ).2 (min c.coefficientRadius c.rootRadius),
        ContDiffAt ℝ ∞ c.root p) ∧
      (∀ p ∈ KA ×ˢ Kη, ContDiffAt ℝ ∞ c.root p) ∧
    ∃ bound > (0 : ℝ),
      (∀ p ∈ KA ×ˢ Kη,
        ‖coefficientRootPencil (coordinateSplit c.index) c.root p‖ ≤ bound ∧
        ‖pencil p.1 ((coordinateSplit c.index).symm (1, 0))‖ ≤ bound ∧
        (coefficientRootPencil (coordinateSplit c.index) c.root p).det = 0 ∧
        c.minorGap ≤ |(coefficientRootPencil (coordinateSplit c.index) c.root p).adjugate c.row c.col| ∧
        c.transportGap ≤ |minorTransportCoefficient
          (coefficientRootPencil (coordinateSplit c.index) c.root p)
          (pencil p.1 ((coordinateSplit c.index).symm (1, 0))) c.row c.col|) ∧
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      (∀ p ∈ minorCoefficientClass c.row c.col bound c.minorGap c.transportGap,
        ∀ e : ℝ, |e| ≤ ε →
        δ ≤ |(pencilCompletion p.1 p.2 (minorRightNullvector p.1 c.row c.col)
          (minorLeftNullvector p.1 p.2 c.row c.col) e).det| ∧
        δ ≤ |(borderedPencil p.1 p.2 (minorRightNullvector p.1 c.row c.col)
          (minorLeftNullvector p.1 p.2 c.row c.col) e).det|) ∧
      (minorCoefficientClass c.row c.col bound c.minorGap c.transportGap ×ˢ
        closedBall (0 : ℝ) ε ⊆ minorComplementDomain c.row c.col) ∧
    ∃ a' > (0 : ℝ), a' ≤ a ∧ a' ≤ c.coefficientRadius ∧
      f.coefficientRadius ≤ a' ∧
    ∃ V : Set E, IsOpen V ∧ ξ ∈ V ∧ V ⊆ c.angularNeighborhood ∧
      tsupport (f.angularMask p) ⊆ V ∧
      (∀ ζ ∈ V, ∀ t : ℝ, 0 < t → t • ζ ∈ V) ∧
    ∃ Λ > (0 : ℝ),
      (∀ ζ ∈ V,
        let ζ' := (physicalCoordinates c.index).symm ζ
        0 < c.radialSection (spatialPart ζ') ∧
        spatialPart (normalizeCovector c.radialSection ζ') ∈ Kη ∧
        ‖normalizeCovector c.radialSection ζ'‖ ≤ Λ ∧
        ∀ A ∈ closedBall A₀ a',
          |normalizeCovector c.radialSection ζ' 0 -
            c.root (A, spatialPart (normalizeCovector c.radialSection ζ'))| ≤ ε) ∧
      ∀ Q : E → Coeff, MapsTo Q Ω (closedBall A₀ a') →
        (∀ β : E → ℂ, tsupport β ⊆ V →
          NormalizedSpectralSupport c.radialSection (fieldRoot (coordinateSplit c.index) Q c.root)
            (physicalCoordinates c.index ⁻¹' Ω) ε (β ∘ physicalCoordinates c.index) ∧
          NormalizedSpectralSupport c.radialSection (fieldRoot (coordinateSplit c.index) Q c.root)
            (physicalCoordinates c.index ⁻¹'
              (rootPhysicalPosition (coordinateSplit c.index) '' tsupport c.sourceMask))
            ε (β ∘ physicalCoordinates c.index) ∧
          (physicalCoordinates c.index ⁻¹' Ω) ×ˢ
            (normalizeCovector c.radialSection '' tsupport (β ∘ physicalCoordinates c.index)) ⊆
            complementDomain c.index Q (fieldRoot (coordinateSplit c.index) Q c.root)
              c.row c.col (fieldDomain (coordinateSplit c.index) Ω c.radialSection
                (coordinateSplit c.index ξ).2 c.coefficientRadius)) ∧
        (ContDiffOn ℝ ∞ Q Ω → ∀ ζ ∈ V,
          let ζ' := normalizeCovector c.radialSection ((physicalCoordinates c.index).symm ζ)
          (∀ y ∈ closedBall x' RQ, ContDiffAt ℝ ∞
            (fun y ↦ bminus c.index Q (fieldRoot (coordinateSplit c.index) Q c.root)
              c.row c.col y ζ') y) ∧
          ∀ m, cNorm (closedBall x' RQ) m
            (fun y ↦ bminus c.index Q (fieldRoot (coordinateSplit c.index) Q c.root)
              c.row c.col y ζ') ≤ C m * (1 + cNorm (closedBall x RQ) m Q))) :
    ∃ (evolutionTime speedGap rootSize : f.centers → ℝ) (rootCost : f.centers → ℕ → ℝ),
      (∀ p, LocalProtectionCertificate (f.chart p) (evolutionTime p) (speedGap p)
        (rootSize p) (rootCost p)) ∧
      (∀ p, 0 < 6 * f.physicalRadius ∧
        6 * f.physicalRadius < (f.chart p).sourceRadius ∧
        6 * f.physicalRadius < evolutionTime p) ∧
      (∀ p : f.centers, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
        (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4) ∧
      (∀ p : f.centers, SelectedChartPhysicalEvolution (f.chart p) (f.angularMask p)
        ((physicalCoordinates (f.chart p).index).symm '' tsupport f.inputMask)
        ((physicalCoordinates (f.chart p).index) ⁻¹' Ω)) ∧
      (∀ p : f.centers,
        let c := f.chart p
        RootBuffer c.index c.row c.col A₀ p.val.val c.root c.coefficientRadius c.rootRadius
          c.minorGap c.transportGap ∧
        MapsTo (rootPhysicalPosition (coordinateSplit c.index)) (tsupport c.sourceMask)
          (closedBall x RQ) ∧
        ∃ ε > (0 : ℝ), ∃ Rbox > (0 : ℝ), ∃ Mbound > (0 : ℝ),
        ∃ C D G : ℕ → ℝ, (∀ m, 0 < C m) ∧ (∀ m, 1 ≤ D m) ∧ (∀ n, 0 ≤ G n) ∧
        ∀ L ≥ f.radialThreshold, ∀ (Q : E → Coeff) (B : E → Mat),
          ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
          MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
          cNorm (closedBall x RQ) (sectorLowOrder d) Q ≤ M →
          cNorm (closedBall x RQ) (sectorLowOrder d) B ≤ M →
          let h := fieldRoot (coordinateSplit c.index) Q c.root
          let β := fun ζ ↦ (dilatedConicMask (f.angularMask p) L (physicalCoordinates c.index ζ) : ℂ)
          let U := physicalCoordinates c.index ⁻¹' Ω
          let b := directAlgebraicSymbol
            (conicBminus c.radialSection c.index Q h c.row c.col)
            (conicSourceSymbol c.radialSection (conicMask (f.spatialMask p)) c.sourceMask) β
          let pb := physicalSymbolApply
            (fun y a ↦ (coefficient c.index Q y a).map Complex.ofReal)
            (fun y ↦ (zeroth c.index B y).map Complex.ofReal) b
          NormalizedSpectralSupport c.radialSection h U ε β ∧
          ContDiffOn ℝ ∞ h (normalizedRootDomain c) ∧
          (∀ w ∈ normalizedRootDomain c, (rootPencil (coordinateSplit c.index) Q h w).det = 0) ∧
          (U ×ˢ (normalizeCovector c.radialSection '' tsupport β) ⊆
            complementDomain c.index Q h c.row c.col (normalizedRootDomain c)) ∧
          (∀ ζ ∈ tsupport β, ∀ y ∈ U,
            (∑ a, (ζ a : ℂ) • (coefficient c.index Q y a).map Complex.ofReal) *
              conicBminus c.radialSection c.index Q h c.row c.col y ζ =
                1 - projector c.index Q h c.row c.col y
                  ((c.radialSection (spatialPart ζ))⁻¹ • spatialPart ζ)) ∧
          ∀ s ∈ ({b, pb} : Set (E → E → CMat)),
            ContDiff ℝ ∞ (Function.uncurry s) ∧
            GraphNormalAmplitudeBounds
              (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p) s)
              Rbox Mbound ∧
            (∀ m ξ is, is.length ≤ m → ∀ z,
              (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
                (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p) s ξ) z‖ ≤
                C m * (1 + cNorm (closedBall x RQ) (m+1) Q +
                  cNorm (closedBall x RQ) (m+1) B)) ∧
            ∀ n : ℕ,
              let T := physicalOperator c.index
                (maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p) s)
              let high := D (2 * (d+2) + (n+1)) *
                (1 + cNorm (closedBall x RQ) (n + (2 * (d+2) + 2)) Q +
                  cNorm (closedBall x RQ) (n + (2 * (d+2) + 2)) B)
              (∀ u : H, MemVectorFourierSobolev (n : ℝ) u →
              (MemVectorFourierSobolev ((n : ℝ)+1) (T u) ∧
                vectorFourierSobolevNorm ((n : ℝ)+1) (T u) ≤
                  ((d+1 : ℝ) * (d+1) * G n) *
                    (vectorFourierSobolevNorm (n : ℝ) u + high * ‖u‖)) ∧
              (MemVectorFourierSobolev ((n : ℝ)+1) (T.adjoint u) ∧
                vectorFourierSobolevNorm ((n : ℝ)+1) (T.adjoint u) ≤
                  ((d+1 : ℝ) * (d+1) * G n) *
                    (vectorFourierSobolevNorm (n : ℝ) u + high * ‖u‖))) ∧
              ∀ u : H,
                (MemVectorFourierSobolev (-(n : ℝ)) (T u) ∧
                  vectorFourierSobolevNorm (-(n : ℝ)) (T u) ≤
                    ((d+1 : ℝ) * (d+1) * ((d+1 : ℝ) * (d+1) * G n)) *
                      (1 + high) * vectorFourierSobolevNorm (-((n : ℝ)+1)) u) ∧
                (MemVectorFourierSobolev (-(n : ℝ)) (T.adjoint u) ∧
                  vectorFourierSobolevNorm (-(n : ℝ)) (T.adjoint u) ≤
                    ((d+1 : ℝ) * (d+1) * ((d+1 : ℝ) * (d+1) * G n)) *
                      (1 + high) * vectorFourierSobolevNorm (-((n : ℝ)+1)) u)) ∧
    ∃ L : ℝ, ∃ hL : f.radialThreshold ≤ L,
    ∃ (angular : f.centers → Euclidean d → ℝ) (χout χsource : f.centers → E → ℂ),
    ∃ hs : ∀ p, ContDiff ℝ ∞ (χsource p),
    ∃ (output : E → ℝ) (r : ℝ), 0 < r ∧
      ContDiff ℝ ∞ output ∧ (∀ y, output y ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport output ∧ tsupport output ⊆ ball x f.physicalRadius ∧
      closedBall x r ⊆ interior {y | output y = 1} ∧
      (∀ p y, χsource p ((physicalCoordinates (f.chart p).index).symm y) *
        (f.inputMask y : ℂ) = (f.inputMask y : ℂ)) ∧
      (∀ p y, (output y : ℂ) * χout p ((physicalCoordinates (f.chart p).index).symm y) =
        (output y : ℂ)) ∧
      (∀ p, SelectedChartEndpointAtWithProtection f p
        (evolutionTime p) (speedGap p) (rootSize p) (rootCost p) L (angular p) (χout p) (χsource p) (hs p) output) ∧
      (∀ p, selectedSourceSymbol (withEnlargedThreshold f L hL) p
        (withEnlargedThreshold f L hL).radialThreshold = selectedSourceSymbol f p (2*L)) ∧
    ∃ (base : Fin 2 → f.centers → ℝ) (cost : Fin 2 → f.centers → ℕ → ℝ)
      (maskCost : ℕ → ℝ) (Rbox : f.centers → ℝ)
      (Dpdo Dgain Gain : f.centers → ℕ → ℝ)
      (ra rb : f.centers → ℝ) (amplitudeCost : f.centers → ℕ → ℝ),
      (∀ o p, 0 < base o p) ∧ (∀ o p s, 0 < cost o p s) ∧
      (∀ s, 1 ≤ maskCost s) ∧ (∀ p, 0 < Rbox p) ∧
      (∀ p s, 1 ≤ Dpdo p s) ∧ (∀ p s, 1 ≤ Dgain p s) ∧ (∀ p s, 0 ≤ Gain p s) ∧
      (∀ p, 0 < ra p) ∧ (∀ p, ra p < rb p) ∧ (∀ p m, 0 < amplitudeCost p m) ∧
      (∀ p, ContDiff ℝ ∞ (angular p) ∧
        ∀ η ∈ tsupport (angular p), 0 < (f.chart p).radialSection η) ∧
      (∀ p, FinitePdo.RetainedConstruction.DiagonalFrequencyCoverage
        (f.chart p).radialSection (coordinateSplit (f.chart p).index p.val.val).2
        ((f.chart p).bufferRadius/2) (ra p) (rb p) (selectedEndpointMultiplier f p L)) ∧
    ∃ completeCost : Fin 2 → ℕ → ℝ, (∀ o s, 0 ≤ completeCost o s) ∧
    ∃ completeLocalCost : ℝ, 0 ≤ completeLocalCost ∧
    ∀ Q : E → Fin (d+1) → Mat, ContDiffOn ℝ ∞ Q Ω →
      MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
      cNorm (closedBall x RQ) (sectorLowOrder d) Q ≤ M →
    ∀ B : E → Mat, ContDiffOn ℝ ∞ B Ω →
      cNorm (closedBall x RQ) (sectorLowOrder d) B ≤ M →
    ∃ (Φ : f.centers → Z × ℝ → Z) (C : f.centers → OpenPartialHomeomorph TPoint TPoint)
      (G : f.centers → TPoint → ℝ) (Op : Fin 2 → f.centers → H →L[ℂ] H),
      (∀ p, SelectedProtectionData (f.chart p) (evolutionTime p) (speedGap p)
        (rootSize p) (rootCost p) Q (Φ p) (C p)) ∧
      (∀ p,
        let c := f.chart p
        let e := coordinateSplit c.index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        let h := fieldRoot e Q c.root
        let U := fieldDomain e Ω c.radialSection z.2.2 c.coefficientRadius
        let V := (C p).target ∩ (C p).symm ⁻¹' (ball z.1 (c.maskRadius/2) ×ˢ
          (ball z.1 (c.maskRadius/2) ×ˢ ball z.2 (c.maskRadius/2)))
        let Fs := selectedBufferedAmplitude f p Q B (Φ p) (C p)
        let W := selectedConicAmplitude f p Q B (Φ p) (C p) (angular p)
        ContDiffOn ℝ ∞ h U ∧
        (∀ w ∈ U, ∀ t : ℝ, 0 < t → h (w.1, (w.2.1, t • w.2.2)) = t*h w) ∧
        closedBall z c.rootRadius ⊆ U ∧
        (∀ w ∈ closedBall z c.rootRadius, (rootPencil e Q h w).det = 0 ∧
          c.minorGap ≤ |(rootPencil e Q h w).adjugate c.row c.col| ∧
          c.transportGap ≤ |minorTransportCoefficient (rootPencil e Q h w)
            (rootTimeCoefficient e Q w) c.row c.col|) ∧
        ((C p) : TPoint → TPoint) = twoTimeProjection (Φ p) ∧
        (C p).source = ball (z.1, z) c.sourceRadius ∧
        ContDiffOn ℝ ∞ (C p).symm (C p).target ∧
        closedBall (z.1, z) c.targetRadius ⊆ (C p).target ∧
        ContDiffOn ℝ ∞ (twoTimePhase (C p)) (C p).target ∧
        (∀ q ∈ (C p).target, HasFDerivAt (twoTimePhase (C p))
          (twoTimePhaseDifferential h (Φ p) (C p) q) q) ∧
        (∀ q ∈ (C p).target,
          ((C p).symm q).1 = q.1 ∧ ((C p).symm q).2.1 = q.2.1 ∧
          ((C p).symm q).2.2.2 = q.2.2.2 ∧
          (twoTimeState (Φ p) ((C p).symm q)).2.1 = q.2.2.1) ∧
        (∀ q ∈ (C p).target, twoTimeState (Φ p) ((C p).symm q) ∈ U ∧
          (twoTimeState (Φ p) ((C p).symm q)).1 = q.1) ∧
        (∀ w ∈ ball z c.sourceRadius, (w.1, w) ∈ (C p).target ∧
          (C p).symm (w.1, w) = (w.1, w) ∧
          twoTimePhase (C p) (w.1, w) = inner ℝ w.2.1 w.2.2) ∧
        (∀ q ∈ closedBall (z.1, z) c.targetRadius, ‖twoTimePhaseMixed (C p) q - 1‖ ≤ 1/2) ∧
        (∀ m, cNorm (closedBall (z.1, z) c.targetRadius) m (twoTimePhase (C p)) ≤
          c.phaseCost m * (1+cNorm (closedBall x RQ) (m+1) Q)) ∧
        ball (z.1, z) c.outerRadius ⊆ (C p).target ∧
        MapsTo (C p) (closedBall (z.1, z) c.maskRadius)
          (closedBall (z.1, z) (c.bufferRadius/2)) ∧
        ContDiff ℝ ∞ (G p) ∧
        (∀ t y η, G p (t, (t, (y, η))) = inner ℝ y η) ∧
        (∀ q ∈ tsupport (collared c.radialSection 0 (angular p) (Fs 0)) ∪
          tsupport (collared c.radialSection 1 (angular p) (Fs 1)),
          G p =ᶠ[𝓝 q] ConicPhase.phase c.radialSection (C p)) ∧
        (∀ q : TPoint, c.timeMask =ᶠ[𝓝 q.1] (fun _ ↦ 1) →
          collared c.radialSection 1 (angular p) (Fs 2) q ≠ 0 →
          G p =ᶠ[𝓝 q] ConicPhase.phase c.radialSection (C p)) ∧
        (∀ y : E, c.timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1) → ∀ s η j,
          WKB.firstOrderApply
            (fun x idx ↦ ((coefficient c.index Q x idx).map Complex.ofReal).mulVecLin)
            (fun x ↦ ((zeroth c.index B x).map Complex.ofReal).mulVecLin)
            (fun x ↦ Complex.exp (Complex.I * (G p (x 0, (s, (spatialPart x, η))) : ℂ)) •
              (fun k ↦ (W 0 + W 1) (x 0) s (spatialPart x) η k j)) y =
            Complex.exp (Complex.I * (G p (y 0, (s, (spatialPart y, η))) : ℂ)) •
              (fun k ↦ twoTimePhysicalApply
                (fun x idx ↦ (coefficient c.index Q x idx).map Complex.ofReal)
                (fun x ↦ (zeroth c.index B x).map Complex.ofReal) (W 1)
                  (y 0) s (spatialPart y) η k j)) ∧
        (∀ y : E, c.timeMask (y 0) = 1 → ∀ η,
          (coefficient c.index Q y 0).map Complex.ofReal * W 0 (y 0) (y 0) (spatialPart y) η =
            conicSourceSymbol c.radialSection (conicMask (angular p)) c.sourceMask y η •
              projector c.index Q h c.row c.col y ((c.radialSection η)⁻¹ • η)) ∧
        let Ψ := fun t s y η ↦ G p (t, (s, (y, η)))
        let a := (coordinateSplit c.index x).1-c.maskRadius/2
        RetainedSignedRetardedBounds (closedBall x RQ) Q B (3*c.maskRadius/4) a Ψ
          (W 0 + W 1) (χout p) (χsource p) (selectedEndpointMultiplier f p L)
          (hs p) 0 (base 0 p) (cost 0 p) (Op 0 p) ∧
        RetainedSignedRetardedBounds (closedBall x RQ) Q B (3*c.maskRadius/4) a Ψ
          (W 2) (χout p) (χsource p) (selectedEndpointMultiplier f p L)
          (hs p) 1 (base 1 p) (cost 1 p) (Op 1 p) ∧
        RetainedSignedRetardedBounds (closedBall x RQ) Q B (3*c.maskRadius/4) a Ψ
          (twoTimePhysicalApply (fun y idx ↦ (coefficient c.index Q y idx).map Complex.ofReal)
            (fun y ↦ (zeroth c.index B y).map Complex.ofReal) (W 1))
          (χout p) (χsource p) (selectedEndpointMultiplier f p L)
          (hs p) 1 (base 1 p) (cost 1 p) (Op 1 p) ∧
        EndpointPdoEstimates c.index (closedBall x RQ) Q B
          (endpointOutputMask f p output) (FiniteAlgebraic.chartInputMask f p)
          (selectedEndpointSymbol f p L Q (W 1)) (Rbox p) M (Dpdo p) (Dgain p) (Gain p) ∧
        (∀ q : TPoint, c.timeMask =ᶠ[𝓝 q.1] (fun _ ↦ 1) → ∀ j : Fin (d+1),
          (fun k ↦ collared c.radialSection 1 (angular p) (Fs 2) q k j) =
            WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
              (fun y k ↦ collared c.radialSection 1 (angular p) (Fs 1)
                (physicalSlice e q.2.1 q.2.2.2 y) k j) (e.symm (q.1, q.2.2.1))) ∧
        ∀ j : Fin 3,
          ContDiff ℝ ∞ (Fs j) ∧ HasCompactSupport (Fs j) ∧ tsupport (Fs j) ⊆ V ∧
          tsupport (Fs j) ⊆ closedBall (z.1, z) (c.bufferRadius/2) ∧
          ContDiff ℝ ∞ (collared c.radialSection (if j=0 then 0 else 1) (angular p) (Fs j)) ∧
          tsupport (collared c.radialSection (if j=0 then 0 else 1) (angular p) (Fs j)) ⊆
            ConicPhase.domain c.radialSection V ∧
          (∀ q : TPoint, q.2.1 ≤ z.1-c.maskRadius →
            collared c.radialSection (if j=0 then 0 else 1) (angular p) (Fs j) q = 0) ∧
          (∀ q ∈ V, c.timeMask =ᶠ[𝓝 q.1] (fun _ ↦ 1) → Fs j =ᶠ[𝓝 q]
            pencilAmplitudeFamily c.index Q B h (Φ p) (C p) c.row c.col c.sourceMask j) ∧
          ∀ m, BoundedTwoTimeOrderSeminorm (if j=0 then 0 else 1)
              (bufferedJetSet c.radialSection z (c.bufferRadius/2) (ra p) (rb p)) m (W j) ∧
            twoTimeOrderSeminorm (if j=0 then 0 else 1)
              (bufferedJetSet c.radialSection z (c.bufferRadius/2) (ra p) (rb p)) m (W j) ≤
              amplitudeCost p m * (1+cNorm (closedBall x RQ) (m+10) Q+
                cNorm (closedBall x RQ) (m+9) B)) ∧
      ∃ (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
        (hib : ∀ y, ‖f.inputMask y‖ ≤ 1),
      let retarded := fun o : Fin 2 ↦ (sourceCutMultiplier output ho hob).comp
        ((finitePhysicalOperator (fun p ↦ (f.chart p).index) (Op o)).comp
          (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
      let W₁ := fun p ↦ selectedConicAmplitude f p Q B (Φ p) (C p) (angular p) 1
      let T := fun o : Fin 2 ↦ if o = 0 then
        selectedFiniteDirectSolver f L Q B output ho hob (retarded 0) else
        selectedFiniteDirectResidual f L Q B W₁ output ho hob (retarded 1)
      let Tplus := fun o : Fin 2 ↦ (1/2 : ℂ) • (T o +
        (sourceCutMultiplier output ho hob).comp
          (if o = 0 then ellipticSolver f hK L Q else ellipticResidual f hK L Q B))
      (∀ (u : H) (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ ball x r → ∀ j,
        physicalTestAction
          (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
          (fun y ↦ (T 0 u y).ofLp) φ j = ∫ y, φ y •
            ((1 + selectedFiniteCompleteError f L Q B W₁ output ho hob (retarded 1)) u) y j) ∧
      (∀ (o : Fin 2) (s : ℕ) (V : H →L[ℂ] H),
        (V = Tplus o ∨ V = (Tplus o).adjoint) → ∀ u,
        MemVectorFourierSobolev ((s-o.val : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (V u) ∧
        vectorFourierSobolevNorm (s : ℝ) (V u) ≤ completeCost o s *
          (vectorFourierSobolevNorm ((s-o.val : ℕ) : ℝ) u +
            (1+cNorm (closedBall x RQ) (s-o.val+sectorLowOrder d) Q+
              cNorm (closedBall x RQ) (s-o.val+sectorLowOrder d) B)*‖u‖)) ∧
      (∀ (o : Fin 2) (k : ℕ) (V : H →L[ℂ] H),
        (V = Tplus o ∨ V = (Tplus o).adjoint) → ∀ u,
        MemVectorFourierSobolev (-(k : ℝ)) (V u) ∧
        vectorFourierSobolevNorm (-(k : ℝ)) (V u) ≤
          ((d+1 : ℝ)*(d+1)*completeCost o (k+o.val)) *
            (2+cNorm (closedBall x RQ) (k+sectorLowOrder d) Q+
              cNorm (closedBall x RQ) (k+sectorLowOrder d) B) *
            vectorFourierSobolevNorm (-((k+o.val : ℕ) : ℝ)) u) ∧
      ∀ (U V : Set E) (hU : MeasurableSet U), MeasurableSet V →
        (∀ u : LocalL2 U (EuclideanSpace ℂ (Fin (d+1))),
          MemRestrictionSobolev V 1 (localRetardedOperator hU V (Tplus 1) u) ∧
          restrictionSobolevNorm V 1 (localRetardedOperator hU V (Tplus 1) u) ≤
            completeLocalCost*‖u‖) ∧
        (∀ v : LocalL2 V (EuclideanSpace ℂ (Fin (d+1))),
          MemRestrictionSobolev U 1 ((localRetardedOperator hU V (Tplus 1)).adjoint v) ∧
          restrictionSobolevNorm U 1 ((localRetardedOperator hU V (Tplus 1)).adjoint v) ≤
            completeLocalCost*‖v‖) ∧
        let R := localRealCompression hU V
          (pairedResidual f hK L Q B output ho hob W₁ (retarded 1))
        (∀ u : LocalL2 U (EuclideanSpace ℝ (Fin (d+1))),
          MemRestrictionSobolev V 1 (R u) ∧ restrictionSobolevNorm V 1 (R u) ≤
            (4*completeLocalCost)*‖u‖) ∧
        (∀ v : LocalL2 V (EuclideanSpace ℝ (Fin (d+1))),
          MemRestrictionSobolev U 1 (R.adjoint v) ∧ restrictionSobolevNorm U 1 (R.adjoint v) ≤
            (4*completeLocalCost)*‖v‖) := by
  classical
  have hfixed := exists_finite_protected_direct_operator_bounds_and_equations_of_selected_collar
    (d := d) (Ω := Ω) (RQ := RQ) (K := K) (M := M) hΩ x hRQ hKΩ A₀ hM f hf
  obtain ⟨evolutionTime, hfixed⟩ := hfixed
  refine ⟨evolutionTime, ?_⟩
  obtain ⟨speedGap, hfixed⟩ := hfixed
  refine ⟨speedGap, ?_⟩
  obtain ⟨rootSize, hfixed⟩ := hfixed
  refine ⟨rootSize, ?_⟩
  obtain ⟨rootCost, hfixed⟩ := hfixed
  refine ⟨rootCost, ?_⟩
  obtain ⟨hprotection, hfixed⟩ := hfixed
  refine ⟨hprotection, ?_⟩
  obtain ⟨hcommon, hfixed⟩ := hfixed
  refine ⟨hcommon, ?_⟩
  obtain ⟨hradii, hfixed⟩ := hfixed
  refine ⟨hradii, ?_⟩
  obtain ⟨hevolution, hfixed⟩ := hfixed
  refine ⟨hevolution, ?_⟩
  obtain ⟨hlocal, hfixed⟩ := hfixed
  refine ⟨hlocal, ?_⟩
  obtain ⟨L, hfixed⟩ := hfixed
  refine ⟨L, ?_⟩
  obtain ⟨hL, hfixed⟩ := hfixed
  refine ⟨hL, ?_⟩
  obtain ⟨angular, hfixed⟩ := hfixed
  refine ⟨angular, ?_⟩
  obtain ⟨χout, hfixed⟩ := hfixed
  refine ⟨χout, ?_⟩
  obtain ⟨χsource, hfixed⟩ := hfixed
  refine ⟨χsource, ?_⟩
  obtain ⟨hs, hfixed⟩ := hfixed
  refine ⟨hs, ?_⟩
  obtain ⟨output, hfixed⟩ := hfixed
  refine ⟨output, ?_⟩
  obtain ⟨r, hfixed⟩ := hfixed
  refine ⟨r, ?_⟩
  obtain ⟨hr, hfixed⟩ := hfixed
  refine ⟨hr, ?_⟩
  obtain ⟨ho, hfixed⟩ := hfixed
  refine ⟨ho, ?_⟩
  obtain ⟨horange, hfixed⟩ := hfixed
  refine ⟨horange, ?_⟩
  obtain ⟨hoc, hfixed⟩ := hfixed
  refine ⟨hoc, ?_⟩
  obtain ⟨hos, hfixed⟩ := hfixed
  refine ⟨hos, ?_⟩
  obtain ⟨hop, hfixed⟩ := hfixed
  refine ⟨hop, ?_⟩
  obtain ⟨hsourceMask, hfixed⟩ := hfixed
  refine ⟨hsourceMask, ?_⟩
  obtain ⟨houtMask, hfixed⟩ := hfixed
  refine ⟨houtMask, ?_⟩
  obtain ⟨hselected, hfixed⟩ := hfixed
  refine ⟨hselected, ?_⟩
  obtain ⟨hthreshold, hfixed⟩ := hfixed
  refine ⟨hthreshold, ?_⟩
  obtain ⟨base, hfixed⟩ := hfixed
  refine ⟨base, ?_⟩
  obtain ⟨cost, hfixed⟩ := hfixed
  refine ⟨cost, ?_⟩
  obtain ⟨maskCost, hfixed⟩ := hfixed
  refine ⟨maskCost, ?_⟩
  obtain ⟨Rbox, hfixed⟩ := hfixed
  refine ⟨Rbox, ?_⟩
  obtain ⟨Dpdo, hfixed⟩ := hfixed
  refine ⟨Dpdo, ?_⟩
  obtain ⟨Dgain, hfixed⟩ := hfixed
  refine ⟨Dgain, ?_⟩
  obtain ⟨Gain, hfixed⟩ := hfixed
  refine ⟨Gain, ?_⟩
  obtain ⟨ra, hfixed⟩ := hfixed
  refine ⟨ra, ?_⟩
  obtain ⟨rb, hfixed⟩ := hfixed
  refine ⟨rb, ?_⟩
  obtain ⟨amplitudeCost, hfixed⟩ := hfixed
  refine ⟨amplitudeCost, ?_⟩
  obtain ⟨hbase, hfixed⟩ := hfixed
  refine ⟨hbase, ?_⟩
  obtain ⟨hcost, hfixed⟩ := hfixed
  refine ⟨hcost, ?_⟩
  obtain ⟨hmaskCost, hfixed⟩ := hfixed
  refine ⟨hmaskCost, ?_⟩
  obtain ⟨hRbox, hfixed⟩ := hfixed
  refine ⟨hRbox, ?_⟩
  obtain ⟨hDpdo, hfixed⟩ := hfixed
  refine ⟨hDpdo, ?_⟩
  obtain ⟨hDgain, hfixed⟩ := hfixed
  refine ⟨hDgain, ?_⟩
  obtain ⟨hGain, hfixed⟩ := hfixed
  refine ⟨hGain, ?_⟩
  obtain ⟨hra, hfixed⟩ := hfixed
  refine ⟨hra, ?_⟩
  obtain ⟨hrab, hfixed⟩ := hfixed
  refine ⟨hrab, ?_⟩
  obtain ⟨hamp, hfixed⟩ := hfixed
  refine ⟨hamp, ?_⟩
  obtain ⟨hangular, hfixed⟩ := hfixed
  refine ⟨hangular, ?_⟩
  obtain ⟨hcoverage, hfixed⟩ := hfixed
  refine ⟨hcoverage, ?_⟩
  obtain ⟨directCost, hfixed⟩ := hfixed
  obtain ⟨hdirectCost, hfixed⟩ := hfixed
  obtain ⟨defectCost, hfixed⟩ := hfixed
  obtain ⟨hdefectCost, hfixed⟩ := hfixed
  obtain ⟨localCost, hfixed⟩ := hfixed
  obtain ⟨hlocalCost, hfixed⟩ := hfixed
  have hconstruct := hfixed
  have hob y : ‖output y‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (horange y).1]
    exact (horange y).2
  obtain ⟨ellCost, ellLow, hellCost, _, helliptic⟩ :=
    exists_commonOutput_elliptic_direct_constants f hK hΩ hKΩ output ho hoc hob
  obtain ⟨Dlocal, hDlocal, hrestriction⟩ := exists_localRetarded_restrictionH1_constant d (d+1)
  let completeCost (o : Fin 2) (s : ℕ) := (directCost o s + ellCost o s)/2
  have hcompleteCost o s : 0 ≤ completeCost o s :=
    div_nonneg (add_nonneg (hdirectCost o s) (hellCost o s)) (by norm_num)
  let completeLocalCost := (Dlocal * completeCost 1 1) * (2+2*M)
  have hcompleteLocalCost : 0 ≤ completeLocalCost :=
    mul_nonneg (mul_nonneg hDlocal.le (hcompleteCost 1 1)) (by positivity)
  refine ⟨completeCost, ?_⟩
  refine ⟨hcompleteCost, ?_⟩
  refine ⟨completeLocalCost, ?_⟩
  refine ⟨hcompleteLocalCost, ?_⟩
  intro Q hQ hQrange hQlow B hB hBlow
  have hvary := hconstruct Q hQ hQrange hQlow B hB hBlow
  obtain ⟨Φ, hvary⟩ := hvary
  refine ⟨Φ, ?_⟩
  obtain ⟨C, hvary⟩ := hvary
  refine ⟨C, ?_⟩
  obtain ⟨G, hvary⟩ := hvary
  refine ⟨G, ?_⟩
  obtain ⟨Op, hvary⟩ := hvary
  refine ⟨Op, ?_⟩
  obtain ⟨hprotectionData, hvary⟩ := hvary
  refine ⟨hprotectionData, ?_⟩
  obtain ⟨hgeometry, hvary⟩ := hvary
  refine ⟨hgeometry, ?_⟩
  obtain ⟨ho', hvary⟩ := hvary
  refine ⟨ho', ?_⟩
  obtain ⟨hob', hvary⟩ := hvary
  refine ⟨hob', ?_⟩
  obtain ⟨hib, hvary⟩ := hvary
  refine ⟨hib, ?_⟩
  have hresults := hvary
  intro retarded W₁ T Tplus
  let high n := 1+cNorm (closedBall x RQ) (n+sectorLowOrder d) Q+
    cNorm (closedBall x RQ) (n+sectorLowOrder d) B
  have hhigh n : 0 ≤ high n :=
    add_nonneg (add_nonneg zero_le_one (cNorm_nonneg _ _ _)) (cNorm_nonneg _ _ _)
  have hpositive (o : Fin 2) (s : ℕ) (V : H →L[ℂ] H)
      (hV : V = Tplus o ∨ V = (Tplus o).adjoint) (u : H)
      (hu : MemVectorFourierSobolev ((s-o.val : ℕ) : ℝ) u) :
      MemVectorFourierSobolev (s : ℝ) (V u) ∧ vectorFourierSobolevNorm (s : ℝ) (V u) ≤
        completeCost o s * (vectorFourierSobolevNorm ((s-o.val : ℕ) : ℝ) u + high (s-o.val)*‖u‖) := by
    let Eop := if o = 0 then ellipticSolver f hK L Q else ellipticResidual f hK L Q B
    have hEmem : Eop ∈ ({ellipticSolver f hK L Q, ellipticResidual f hK L Q B} : Set (H →L[ℂ] H)) := by
      dsimp only [Eop]
      split_ifs <;> simp
    have he := (helliptic L hL Q B hQ hB hQrange hQlow hBlow Eop hEmem).1 o s
    exact direct_sobolev_half
      (T o + (sourceCutMultiplier output ho' hob').comp Eop)
      ((s-o.val : ℕ) : ℝ) (s : ℝ) (directCost o s+ellCost o s) (high (s-o.val))
      (direct_sobolev_add (T o) ((sourceCutMultiplier output ho' hob').comp Eop)
        ((s-o.val : ℕ) : ℝ) (s : ℝ) (directCost o s) (ellCost o s) (high (s-o.val))
        (hresults.2.2.2.2.1 o s) he) V hV u hu
  have hnegative (o : Fin 2) (k : ℕ) (V : H →L[ℂ] H)
      (hV : V = Tplus o ∨ V = (Tplus o).adjoint) (u : H) :
      MemVectorFourierSobolev (-(k : ℝ)) (V u) ∧
      vectorFourierSobolevNorm (-(k : ℝ)) (V u) ≤
        ((d+1 : ℝ)*(d+1)*completeCost o (k+o.val)) *
          (2+cNorm (closedBall x RQ) (k+sectorLowOrder d) Q+
            cNorm (closedBall x RQ) (k+sectorLowOrder d) B) *
          vectorFourierSobolevNorm (-((k+o.val : ℕ) : ℝ)) u := by
    have ha : V.adjoint = Tplus o ∨ V.adjoint = (Tplus o).adjoint := by
      rcases hV with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (ContinuousLinearMap.adjoint_adjoint _)
    have ht (v : H) (hv : MemVectorFourierSobolev (k : ℝ) v) :
        MemVectorFourierSobolev ((k+o.val : ℕ) : ℝ) (V.adjoint v) ∧
        vectorFourierSobolevNorm ((k+o.val : ℕ) : ℝ) (V.adjoint v) ≤
          completeCost o (k+o.val) * (vectorFourierSobolevNorm (k : ℝ) v + high k*‖v‖) := by
      simpa only [Nat.add_sub_cancel] using
        hpositive o (k+o.val) V.adjoint ha v (by simpa only [Nat.add_sub_cancel] using hv)
    have hn := negativeVectorFourierSobolev_tame_bound_of_adjoint (Nat.cast_nonneg k)
      (Nat.cast_nonneg (k+o.val)) (hcompleteCost o (k+o.val)) (hhigh k) V ht u
    simpa only [Nat.cast_add, Nat.cast_one, high, show (1:ℝ)+(1+cNorm (closedBall x RQ) (k+sectorLowOrder d) Q+
      cNorm (closedBall x RQ) (k+sectorLowOrder d) B) =
      2+cNorm (closedBall x RQ) (k+sectorLowOrder d) Q+
      cNorm (closedBall x RQ) (k+sectorLowOrder d) B by ring] using hn
  refine ⟨hresults.1, hpositive, hnegative, ?_⟩
  intro U V hU hV
  obtain ⟨hforward, hadjoint⟩ := hrestriction (Tplus 1) 0 1 (completeCost 1) (fun s ↦ high (s-1))
    (by simpa only [one_mul, Nat.add_zero, show (1 : Fin 2).val = 1 from rfl] using hpositive 1)
    U V hU hV
  have hlow : 1 + high 0 ≤ 2+2*M := by
    simp only [high, Nat.zero_add]
    linarith only [hQlow, hBlow]
  have hle : Dlocal*completeCost 1 1*(1+high 0) ≤ completeLocalCost :=
    mul_le_mul_of_nonneg_left hlow (mul_nonneg hDlocal.le (hcompleteCost 1 1))
  simp only [one_mul, Nat.add_zero, Nat.sub_self] at hforward hadjoint
  have hf' (u : LocalL2 U (EuclideanSpace ℂ (Fin (d+1)))) :
      MemRestrictionSobolev V 1 (localRetardedOperator hU V (Tplus 1) u) ∧
      restrictionSobolevNorm V 1 (localRetardedOperator hU V (Tplus 1) u) ≤ completeLocalCost*‖u‖ :=
    ⟨(hforward u).1, (hforward u).2.trans (mul_le_mul_of_nonneg_right hle (norm_nonneg u))⟩
  have ha' (v : LocalL2 V (EuclideanSpace ℂ (Fin (d+1)))) :
      MemRestrictionSobolev U 1 ((localRetardedOperator hU V (Tplus 1)).adjoint v) ∧
      restrictionSobolevNorm U 1 ((localRetardedOperator hU V (Tplus 1)).adjoint v) ≤ completeLocalCost*‖v‖ :=
    ⟨(hadjoint v).1, (hadjoint v).2.trans (mul_le_mul_of_nonneg_right hle (norm_nonneg v))⟩
  refine ⟨hf', ha', ?_⟩
  simpa only [Tplus, T, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
      pairedResidual, normalizedPair] using
    localRealCompression_physicalPair_restriction_bounds hU hV (Tplus 1) 1 completeLocalCost
      hcompleteLocalCost hf' ha'

end JanetCartan.RegularSector.NormalizedSolver
