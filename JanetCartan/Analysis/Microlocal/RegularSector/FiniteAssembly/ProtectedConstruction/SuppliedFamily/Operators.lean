module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.ProtectionCertificates.SuppliedFamily.AlgebraicSums
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.ProtectionCertificates.Geometry
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.ProtectedConstruction.RetardedSums
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.EndpointSums
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.PdoIdentification
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.OperatorBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RealPairing
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SourceBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.OriginalEndpoint
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart

/-!
# One protected finite family with the complete PDE and signed estimates

Retain the supplied protected algebraic family. Its endpoint construction retains
angular smoothness and diagonal frequency coverage, so the relative
common-chart PDE proof applies to its literal operators. The root-speed,
transversality, whole-flow and inverse certificates accompany the same solver,
all three analytic residual terms, source at `2*L`, and complete identity defect.

Consumers: `SelectedSectorProtection`'s same-family masks and leakage,
`FixedDomainInverse`'s analytic-residual inverse, and `CompatibleResponse`'s
common source/solution family. Sources: `sector-theorem-solution`,
`sector-theorem-residual`, `measured-adjoint`, `characteristic-kernel`,
`energy-complete-residual`. Existing constructors are unchanged.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAssembly
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

/-- Construct the protected direct solver and its complete residual on a supplied
finite family. The collar hypothesis is the literal conclusion of
`exists_actualMaskFamily_with_algebraic_collar_with_protection_certificates`;
no family is selected here. Both protection certificates, all tested/weak PDE
clauses, full lower-order coefficient and paired angular discrepancy stay on
this family. Constants precede the varying coefficients.
Consumer: `exists_finite_protected_smooth_operators_of_selected_collar`, then
`FixedDomainInverse.exists_finite_direct_smooth_fixed_inverse`.
Sources: `sector-theorem-solution`, `sector-theorem-residual`,
`characteristic-kernel` and `energy-complete-residual`. -/
theorem exists_finite_protected_direct_operator_bounds_and_equations_of_selected_collar_on_enlarged_bands
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (A₀ : Coeff) {K : Set E} {M : ℝ} (hM : 0 ≤ M)
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
              c.row c.col y ζ') ≤ C m * (1 + cNorm (closedBall x RQ) m Q)))
    (bandFloor bandCeiling : f.centers → ℝ) (hbandFloor : ∀ p, 0 < bandFloor p) :
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
      (∀ p, 0 < ra p) ∧ (∀ p, ra p < rb p) ∧
      (∀ p, ra p ≤ bandFloor p) ∧ (∀ p, bandCeiling p ≤ rb p) ∧
      (∀ p m, 0 < amplitudeCost p m) ∧
      (∀ p, ContDiff ℝ ∞ (angular p) ∧
        ∀ η ∈ tsupport (angular p), 0 < (f.chart p).radialSection η) ∧
      (∀ p, FinitePdo.RetainedConstruction.DiagonalFrequencyCoverage
        (f.chart p).radialSection (coordinateSplit (f.chart p).index p.val.val).2
        ((f.chart p).bufferRadius/2) (ra p) (rb p) (selectedEndpointMultiplier f p L)) ∧
    ∃ directCost : Fin 2 → ℕ → ℝ, (∀ o s, 0 ≤ directCost o s) ∧
    ∃ defectCost : ℕ → ℝ, (∀ s, 0 ≤ defectCost s) ∧
    ∃ localCost : ℝ, 0 < localCost ∧
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
      (∀ u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball x r → ∀ j,
        physicalTestAction
          (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
          (fun y ↦ (T 0 u y).ofLp) φ j = ∫ y, φ y •
            ((1 + selectedFiniteCompleteError f L Q B W₁ output ho hob (retarded 1)) u) y j) ∧
      (∀ u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball x r → ∀ j,
        physicalTestAction
          (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
          (fun y ↦ (physicalPairedSectorSum {()} (fun _ : Unit ↦ T 0) u y).ofLp) φ j =
          ∫ y, φ y • (physicalPairedSectorSum {()} (fun _ : Unit ↦
            1 + selectedFiniteCompleteError f L Q B W₁ output ho hob (retarded 1)) u) y j) ∧
      (∀ (u : Lp (EuclideanSpace ℝ (Fin (d+1))) 2 (volume : Measure E)) φ,
        ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball x r → ∀ j,
        physicalTestAction
          (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
          (fun y ↦ (l2ComplexInclusion volume
            (Realization.realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦ T 0)) u) y).ofLp)
          φ j = ∫ y, φ y • l2ComplexInclusion volume
            (Realization.realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦
              1 + selectedFiniteCompleteError f L Q B W₁ output ho hob (retarded 1))) u) y j) ∧
      (∀ u : graphTestSpace (d+1) (d+1), ∃ du : E → E →L[ℝ] (Fin (d+1) → ℂ),
        Mollification.HasWeakFDerivOn volume (fun y ↦ (T 0 (graphTestToLp u) y).ofLp) du univ ∧
        MemLp du 2 volume ∧
        physicalWeakApply
          (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
          (fun y ↦ (T 0 (graphTestToLp u) y).ofLp) du =ᵐ[volume.restrict (ball x r)]
          fun y ↦ ((1 + selectedFiniteCompleteError f L Q B W₁ output ho hob
            (retarded 1)) (graphTestToLp u) y).ofLp) ∧
      (∀ o : Fin 2, ∀ s : ℕ, ∀ V : H →L[ℂ] H, (V = T o ∨ V = (T o).adjoint) → ∀ u,
        MemVectorFourierSobolev ((s-o.val : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (V u) ∧
        vectorFourierSobolevNorm (s : ℝ) (V u) ≤ directCost o s *
          (vectorFourierSobolevNorm ((s-o.val : ℕ) : ℝ) u +
            (1+cNorm (closedBall x RQ) (s-o.val+sectorLowOrder d) Q+
              cNorm (closedBall x RQ) (s-o.val+sectorLowOrder d) B)*‖u‖)) ∧
      (∀ o : Fin 2, ∀ k : ℕ, ∀ V : H →L[ℂ] H, (V = T o ∨ V = (T o).adjoint) → ∀ u,
        MemVectorFourierSobolev (-(k : ℝ)) (V u) ∧
        vectorFourierSobolevNorm (-(k : ℝ)) (V u) ≤
          ((d+1 : ℝ)*(d+1)*directCost o (k+o.val)) *
            (2+cNorm (closedBall x RQ) (k+sectorLowOrder d) Q+
              cNorm (closedBall x RQ) (k+sectorLowOrder d) B) *
            vectorFourierSobolevNorm (-((k+o.val : ℕ) : ℝ)) u) ∧
      (∀ o : Fin 2,
        (sourceCutMultiplier output ho hob).comp (selectedFiniteAlgebraicPDO f (2*L) Q B o) =
          finitePhysicalOperator (fun p ↦ (f.chart p).index)
            (fun p ↦ maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
              (selectedAlgebraicSymbol f p (2*L) Q B o)) ∧
        (selectedFiniteAlgebraicPDO f (2*L) Q B o).adjoint.comp (sourceCutMultiplier output ho hob) =
          finitePhysicalOperator (fun p ↦ (f.chart p).index)
            (fun p ↦ (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
              (selectedAlgebraicSymbol f p (2*L) Q B o)).adjoint)) ∧
      (finitePhysicalOperator (fun p ↦ (f.chart p).index)
        (fun p ↦ maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
          (selectedSourceSymbol f p (2*L))) =
        (sourceCutMultiplier output ho hob).comp (selectedFiniteSourcePDO f L)) ∧
      (∀ s : ℕ, ∀ V : H →L[ℂ] H,
        (V = selectedFiniteCompleteError f L Q B W₁ output ho hob (retarded 1) ∨
          V = (selectedFiniteCompleteError f L Q B W₁ output ho hob (retarded 1)).adjoint) → ∀ u,
        MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (V u) ∧
        vectorFourierSobolevNorm (s : ℝ) (V u) ≤ (defectCost s+directCost 1 s)*
          (vectorFourierSobolevNorm (s : ℝ) u+
            (1+cNorm (closedBall x RQ) (s+sectorLowOrder d) Q+
              cNorm (closedBall x RQ) (s+sectorLowOrder d) B)*‖u‖)) ∧
      ∀ (U V : Set E) (hU : MeasurableSet U), MeasurableSet V →
        (∀ u : LocalL2 U (EuclideanSpace ℂ (Fin (d+1))),
          MemRestrictionSobolev V 1 (localRetardedOperator hU V (T 1) u) ∧
          restrictionSobolevNorm V 1 (localRetardedOperator hU V (T 1) u) ≤
            (localCost * directCost 1 1 * (2+2*M))*‖u‖) ∧
        (∀ v : LocalL2 V (EuclideanSpace ℂ (Fin (d+1))),
          MemRestrictionSobolev U 1 ((localRetardedOperator hU V (T 1)).adjoint v) ∧
          restrictionSobolevNorm U 1 ((localRetardedOperator hU V (T 1)).adjoint v) ≤
            (localCost * directCost 1 1 * (2+2*M))*‖v‖) ∧
        let R := localRealCompression hU V (physicalPairedSectorSum {()} (fun _ : Unit ↦ T 1))
        (∀ u : LocalL2 U (EuclideanSpace ℝ (Fin (d+1))),
          MemRestrictionSobolev V 1 (R u) ∧ restrictionSobolevNorm V 1 (R u) ≤
            (4*(localCost*directCost 1 1*(2+2*M)))*‖u‖) ∧
        (∀ v : LocalL2 V (EuclideanSpace ℝ (Fin (d+1))),
          MemRestrictionSobolev U 1 (R.adjoint v) ∧ restrictionSobolevNorm U 1 (R.adjoint v) ≤
            (4*(localCost*directCost 1 1*(2+2*M)))*‖v‖) := by
  classical
  have hbandConstruction1 := exists_finite_algebraic_pdo_sums_of_selected_collar hΩ x hRQ hKΩ A₀ hM f hf
  obtain ⟨evolutionTime, hbandConstruction1⟩ := hbandConstruction1
  obtain ⟨speedGap, hbandConstruction1⟩ := hbandConstruction1
  obtain ⟨rootSize, hbandConstruction1⟩ := hbandConstruction1
  obtain ⟨rootCost, hbandConstruction1⟩ := hbandConstruction1
  obtain ⟨hprotection, hbandConstruction1⟩ := hbandConstruction1
  obtain ⟨hradii, hbandConstruction1⟩ := hbandConstruction1
  obtain ⟨hevolution, hbandConstruction1⟩ := hbandConstruction1
  obtain ⟨hlocal, hbandConstruction1⟩ := hbandConstruction1
  obtain ⟨algCost, hbandConstruction1⟩ := hbandConstruction1
  obtain ⟨halgCost, hbandConstruction1⟩ := hbandConstruction1
  have halg := hbandConstruction1
  have hlocalKeep := hlocal
  choose hroot hsource ε hε Ralg hRalg Malg hMalg Calg Dalg Galg
    hCalg hDalg hGalg halgLocal using hlocal
  have hbandConstruction2 := exists_finite_common_retarded_sums_with_protection_and_coverage_on_enlarged_bands hΩ hKΩ f hprotection hradii hM
      bandFloor bandCeiling hbandFloor
  obtain ⟨L, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hL, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨angular, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨χout, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨χsource, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hs, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨output, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨r, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hr, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨ho, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨horange, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hoc, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hos, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hop, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hsourceMask, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨houtMask, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hselected, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hthreshold, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨base, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨cost, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨maskCost, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨Rbox, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨Dpdo, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨Dgain, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨Gain, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨ra, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨rb, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨amplitudeCost, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hbase, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hcost, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hmaskCost, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hRbox, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hDpdo, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hDgain, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hGain, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hra, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hrab, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hfloor, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hceiling, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hamp, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hangular, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨hcoverage, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨_, hbandConstruction2⟩ := hbandConstruction2
  obtain ⟨_, hbandConstruction2⟩ := hbandConstruction2
  have hretarded := hbandConstruction2
  have hob y : ‖output y‖ ≤ 1 := by rw [Real.norm_of_nonneg (horange y).1]; exact (horange y).2
  obtain ⟨Dout, hDout, hmask⟩ := exists_outputMask_sobolev_constants (q := d+1) output ho hoc hob
  let retCost (o : Fin 2) s := maskCost s*(∑ p, cost o p s)*maskCost (s-o.val)
  let endCost n := ∑ p, ((d+1 : ℝ)*(d+1)*Gain p n)*Dgain p (2*(d+2)+(n+1))
  let maskedAlgCost (o : Fin 2) s := Dout s*algCost (s-o.val)*Dout (s-o.val)
  let directCost (o : Fin 2) s :=
    (if o = 0 then retCost o s else endCost (s-1)+retCost o s)+maskedAlgCost o s
  have hretCost o s : 0 ≤ retCost o s := mul_nonneg
    (mul_nonneg (zero_le_one.trans (hmaskCost s))
      (Finset.sum_nonneg fun p _ ↦ (hcost o p s).le)) (zero_le_one.trans (hmaskCost _))
  have hendCost n : 0 ≤ endCost n := Finset.sum_nonneg fun p _ ↦
    mul_nonneg (mul_nonneg (by positivity) (hGain p n)) (zero_le_one.trans (hDgain p _))
  have hmaskedAlgCost o s : 0 ≤ maskedAlgCost o s := mul_nonneg
    (mul_nonneg (zero_le_one.trans (hDout s)) (halgCost _)) (zero_le_one.trans (hDout _))
  have hdirectCost o s : 0 ≤ directCost o s := by
    dsimp only [directCost]
    split_ifs
    · exact add_nonneg (hretCost o s) (hmaskedAlgCost o s)
    · exact add_nonneg (add_nonneg (hendCost (s-1)) (hretCost o s)) (hmaskedAlgCost o s)
  obtain ⟨defectCost, hdefectCost, hdefect⟩ :=
    exists_selectedFiniteSourcePDO_identity_defect_bounds f L hL output ho hoc hob
  obtain ⟨localCost, hlocalCost, hlocalBound⟩ := exists_localRetarded_restrictionH1_constant d (d+1)
  refine ⟨evolutionTime, ?_⟩
  refine ⟨speedGap, ?_⟩
  refine ⟨rootSize, ?_⟩
  refine ⟨rootCost, ?_⟩
  refine ⟨hprotection, ?_⟩
  refine ⟨fun p ↦ selected_common_elapsed_lt_evolutionTime f p (hprotection p), ?_⟩
  refine ⟨hradii, ?_⟩
  refine ⟨hevolution, ?_⟩
  refine ⟨hlocalKeep, ?_⟩
  refine ⟨L, ?_⟩
  refine ⟨hL, ?_⟩
  refine ⟨angular, ?_⟩
  refine ⟨χout, ?_⟩
  refine ⟨χsource, ?_⟩
  refine ⟨hs, ?_⟩
  refine ⟨output, ?_⟩
  refine ⟨r, ?_⟩
  refine ⟨hr, ?_⟩
  refine ⟨ho, ?_⟩
  refine ⟨horange, ?_⟩
  refine ⟨hoc, ?_⟩
  refine ⟨hos, ?_⟩
  refine ⟨hop, ?_⟩
  refine ⟨hsourceMask, ?_⟩
  refine ⟨houtMask, ?_⟩
  refine ⟨hselected, ?_⟩
  refine ⟨hthreshold, ?_⟩
  refine ⟨base, ?_⟩
  refine ⟨cost, ?_⟩
  refine ⟨maskCost, ?_⟩
  refine ⟨Rbox, ?_⟩
  refine ⟨Dpdo, ?_⟩
  refine ⟨Dgain, ?_⟩
  refine ⟨Gain, ?_⟩
  refine ⟨ra, ?_⟩
  refine ⟨rb, ?_⟩
  refine ⟨amplitudeCost, ?_⟩
  refine ⟨hbase, ?_⟩
  refine ⟨hcost, ?_⟩
  refine ⟨hmaskCost, ?_⟩
  refine ⟨hRbox, ?_⟩
  refine ⟨hDpdo, ?_⟩
  refine ⟨hDgain, ?_⟩
  refine ⟨hGain, ?_⟩
  refine ⟨hra, ?_⟩
  refine ⟨hrab, ?_⟩
  refine ⟨hfloor, ?_⟩
  refine ⟨hceiling, ?_⟩
  refine ⟨hamp, ?_⟩
  refine ⟨hangular, ?_⟩
  refine ⟨hcoverage, ?_⟩
  refine ⟨directCost, ?_⟩
  refine ⟨hdirectCost, ?_⟩
  refine ⟨defectCost, ?_⟩
  refine ⟨hdefectCost, ?_⟩
  refine ⟨localCost, ?_⟩
  refine ⟨hlocalCost, ?_⟩
  intro Q hQ hQrange hQlow B hB hBlow
  have hbandConstruction3 := hretarded Q hQ hQrange hQlow B hB hBlow
  obtain ⟨Φ, hbandConstruction3⟩ := hbandConstruction3
  obtain ⟨C, hbandConstruction3⟩ := hbandConstruction3
  obtain ⟨G, hbandConstruction3⟩ := hbandConstruction3
  obtain ⟨Op, hbandConstruction3⟩ := hbandConstruction3
  obtain ⟨hprotectionData, hbandConstruction3⟩ := hbandConstruction3
  obtain ⟨hgeometry, hbandConstruction3⟩ := hbandConstruction3
  obtain ⟨ho', hbandConstruction3⟩ := hbandConstruction3
  obtain ⟨hob', hbandConstruction3⟩ := hbandConstruction3
  obtain ⟨hib, hbandConstruction3⟩ := hbandConstruction3
  obtain ⟨hpositive, hbandConstruction3⟩ := hbandConstruction3
  obtain ⟨_, hbandConstruction3⟩ := hbandConstruction3
  refine ⟨Φ, ?_⟩
  refine ⟨C, ?_⟩
  refine ⟨G, ?_⟩
  refine ⟨Op, ?_⟩
  refine ⟨hprotectionData, ?_⟩
  refine ⟨hgeometry, ?_⟩
  refine ⟨ho', ?_⟩
  refine ⟨hob', ?_⟩
  refine ⟨hib, ?_⟩
  intro retarded W₁ T
  let high n := 1+cNorm (closedBall x RQ) (n+sectorLowOrder d) Q+
    cNorm (closedBall x RQ) (n+sectorLowOrder d) B
  have hhigh n : 0 ≤ high n := by
    exact add_nonneg (add_nonneg zero_le_one (cNorm_nonneg _ _ _)) (cNorm_nonneg _ _ _)
  have hLtwo : f.radialThreshold ≤ 2*L := by
    linarith only [f.radialThreshold_ge_one, hL]
  have hnormal (o : Fin 2) p : GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L) Q B o)) (Ralg p) (Malg p) := by
    have ha := halgLocal p (2*L) hLtwo Q B hQ hB hQrange hQlow hBlow
    exact (ha.2.2.2.2.2 (selectedAlgebraicSymbol f p (2*L) Q B o)
      (by fin_cases o <;> simp [selectedAlgebraicSymbol])).2.1
  have htest p : ∀ u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ physicalCoordinates (f.chart p).index ⁻¹' ball x r → ∀ j,
      physicalTestAction (coefficient (f.chart p).index Q) (zeroth (f.chart p).index B)
        (fun y ↦ (selectedCommonChartSolver f p L Q B output ho' hob' hib (Op 0 p) u y).ofLp)
        φ j = ∫ y, φ y •
          ((maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
            (selectedSourceSymbol f p (2*L)) +
            selectedCommonChartResidual f p L Q B (W₁ p) output ho' hob' hib (Op 1 p)) u) y j := by
    let c := f.chart p
    let e := coordinateSplit c.index
    let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
    let h := fieldRoot e Q c.root
    let V := (C p).target ∩ (C p).symm ⁻¹' (ball z.1 (c.maskRadius/2) ×ˢ
      (ball z.1 (c.maskRadius/2) ×ˢ ball z.2 (c.maskRadius/2)))
    let Fs := selectedBufferedAmplitude f p Q B (Φ p) (C p)
    let W := selectedConicAmplitude f p Q B (Φ p) (C p) (angular p)
    obtain ⟨_, _, _, _, _, _, _, hbuffer, hphase, hdiff, hinv, _, _, hnear,
      hphaseBudget, _, _, hGs, hGdiag, hG, hGres, hcancel, hlead,
      hsolver, _, hPW, _, hphysical, hFs⟩ := hgeometry p
    have ha := halgLocal p (2*L) hLtwo Q B hQ hB hQrange hQlow hBlow
    have halg0 := ha.2.2.2.2.2 (selectedAlgebraicSymbol f p (2*L) Q B 0) (by
      simp [selectedAlgebraicSymbol])
    obtain ⟨Rsource, _, Dsource, _, hsourceBudget, _⟩ :=
      exists_selected_source_pdo_budgets f p (2*L)
    obtain ⟨Rend, _, Dend, _, hend⟩ := exists_original_chart_endpoint_normal_bounds
      hΩ hKΩ f p hM (hradii p).1 (hradii p).2
      (lt_of_lt_of_le zero_lt_one (f.radialThreshold_ge_one.trans hL))
      (hcoverage p) (amplitudeCost p) (hamp p)
    have hendBudget := hend Q hQ hQlow B hBlow h (Φ p) (C p) V (angular p)
      (hFs 1).2.2.2.2.1 (hFs 1).2.2.2.2.2.2.2.2
    let Rall : Fin 4 → ℝ := ![Ralg p, Rsource, Rend, Ralg p]
    let Mall : Fin 4 → ℝ := ![Malg p, Dsource (2*(d+2)), Dend (2*(d+2)+1)*(1+M+M), Malg p]
    let A : E → Fin (d+1) → CMat := fun y i ↦ (coefficient c.index Q y i).map Complex.ofReal
    let Bc : E → CMat := fun y ↦ (zeroth c.index B y).map Complex.ofReal
    let bm := conicBminus c.radialSection c.index Q h c.row c.col
    let σf := conicSourceSymbol c.radialSection (conicMask (f.spatialMask p)) c.sourceMask
    let β := selectedEndpointMultiplier f p L
    have hbudget k : GraphNormalAmplitudeBounds
        (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
          (directPDOSymbols A Bc (W 1) bm σf β k)) (Rall k) (Mall k) := by
      fin_cases k
      · exact hnormal 0 p
      · exact hsourceBudget
      · exact hendBudget
      · exact hnormal 1 p
    have hret (k : Bool) : RetainedSignedRetardedBounds (closedBall x RQ) Q B
        (3*c.maskRadius/4) (z.1-c.maskRadius/2) (fun t s y η ↦ G p (t, (s, (y, η))))
        (directRetardedAmplitudes A Bc (W 0) (W 1) k) (χout p) (χsource p) β (hs p)
        (if k then 1 else 0) (base (if k then 1 else 0) p) (cost (if k then 1 else 0) p)
        (Op (if k then 1 else 0) p) := by
      cases k
      · exact hsolver
      · exact hPW
    have hgain := halg0.2.2.2 0
    have hc := FiniteResidual.SelectedChart.completeResidual_of_common_selected_chart
      f p (hradii p).1 (hradii p).2 hΩ hKΩ L (f.radialThreshold_ge_one.trans hL) hL
      (angular p) (hangular p).1 (hangular p).2 (hselected p L le_rfl).1
      Q B hQ hB h (Φ p) (C p) hbuffer hphase hdiff hnear hphaseBudget
      (fun v hv ↦ (hinv v hv).2.1) Fs (fun j ↦ (hFs j).1)
      (fun j ↦ (hFs j).2.2.2.2.1) (fun j ↦ (hFs j).2.2.2.2.2.1) hphysical
      (G p) hG hGres hGs hGdiag hcancel hlead halg0.1 ha.2.2.2.2.1
      Rall Mall hbudget (χout p) (χsource p) (hs p)
      (fun k ↦ Op (if k then 1 else 0) p) (fun k ↦ base (if k then 1 else 0) p)
      (fun k ↦ cost (if k then 1 else 0) p) hret
      ((d+1 : ℝ)*(d+1)*Galg p 0)
      (Dalg p (2*(d+2)+(0+1)) *
        (1+cNorm (closedBall x RQ) (0+(2*(d+2)+2)) Q+
          cNorm (closedBall x RQ) (0+(2*(d+2)+2)) B))
      (fun v hv ↦ by
        simpa only [Nat.cast_zero, zero_add, selectedAlgebraicSymbol, directPDOSymbols,
          Matrix.cons_val_zero, ite_true, h, e, c] using
          (hgain.1 v (by simpa only [Nat.cast_zero] using hv)).1)
      output r ho hoc hob hos hop (houtMask p) (hsourceMask p)
    exact hc.1
  have hendpoint p : EndpointPdoEstimates (f.chart p).index (closedBall x RQ) Q B
      (endpointOutputMask f p output) (chartInputMask f p)
      (selectedEndpointSymbol f p L Q (W₁ p)) (Rbox p) M (Dpdo p) (Dgain p) (Gain p) := by
    have hg := hgeometry p
    exact hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have halgebraic (o : Fin 2) (s : ℕ) :=
    direct_gain_output_order (selectedFiniteAlgebraicPDO f (2*L) Q B o) s o
      (algCost (s-o.val)) (high (s-o.val))
      (halg (2*L) hLtwo Q B hQ hB hQrange hQlow hBlow o (s-o.val)).1
  have hmasked (o : Fin 2) (s : ℕ) := hmask
    (selectedFiniteAlgebraicPDO f (2*L) Q B o) (s-o.val) s (algCost (s-o.val))
    (high (s-o.val)) (halgCost _) (hhigh _) (halgebraic o s)
  have hret (o : Fin 2) (s : ℕ) (V : H →L[ℂ] H)
      (hV : V = retarded o ∨ V = (retarded o).adjoint) (u : H)
      (hu : MemVectorFourierSobolev ((s-o.val : ℕ) : ℝ) u) :
      MemVectorFourierSobolev (s : ℝ) (V u) ∧
      vectorFourierSobolevNorm (s : ℝ) (V u) ≤ retCost o s *
        (vectorFourierSobolevNorm ((s-o.val : ℕ) : ℝ) u+high (s-o.val)*‖u‖) := by
    obtain ⟨hm, hn⟩ := hpositive o s V hV u hu
    refine ⟨hm, hn.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ (norm_nonneg u))) (hretCost o s))⟩
    have hb := (sectorLowOrder_bounds d).2.1
    have hoBound := o.isLt
    exact add_le_add (add_le_add le_rfl (cNorm_mono_order (by omega)))
      (cNorm_mono_order (by omega))
  have hend (s : ℕ) := direct_gain_output_order
    (selectedFiniteEndpointPDO f L Q W₁ output) s 1 (endCost (s-1)) (high (s-1))
    (selectedFiniteEndpointPDO_signed_gain f L Q B W₁ output Rbox Dpdo Dgain Gain
      hDgain hGain hendpoint (s-1)).1
  have hp (o : Fin 2) (s : ℕ) (V : H →L[ℂ] H)
      (hV : V = T o ∨ V = (T o).adjoint) (u : H)
      (hu : MemVectorFourierSobolev ((s-o.val : ℕ) : ℝ) u) :
      MemVectorFourierSobolev (s : ℝ) (V u) ∧
      vectorFourierSobolevNorm (s : ℝ) (V u) ≤ directCost o s *
        (vectorFourierSobolevNorm ((s-o.val : ℕ) : ℝ) u+high (s-o.val)*‖u‖) := by
    have ha := direct_sobolev_unit_smul
      ((sourceCutMultiplier output ho' hob').comp (selectedFiniteAlgebraicPDO f (2*L) Q B o))
      (-Complex.I) (by simp) ((s-o.val : ℕ) : ℝ) (s : ℝ)
      (maskedAlgCost o s) (high (s-o.val)) (hmasked o s)
    fin_cases o
    · exact direct_sobolev_add _ _ _ _ _ _ _ (hret 0 s) ha V hV u hu
    · exact direct_sobolev_add _ _ _ _ _ _ _
        (direct_sobolev_add _ _ _ _ _ _ _ (hend s) (hret 1 s)) ha V hV u hu
  have hballΩ : ball x r ⊆ Ω := by
    intro y hy
    have hyp := interior_subset (hop (ball_subset_closedBall hy))
    have hyout : y ∈ tsupport output := subset_tsupport output (by
      change output y ≠ 0
      rw [show output y = 1 from hyp]
      exact one_ne_zero)
    exact hKΩ (f.physicalBall_coefficientDomain
      ((ball_subset_closedBall.trans (closedBall_subset_closedBall
        (by linarith [f.physicalRadius_pos] : f.physicalRadius ≤ 4*f.physicalRadius))) (hos hyout)))
  have hfiniteTest := selectedFiniteDirectSolver_test_of_commonCharts f L hL hΩ hballΩ
    Q B hQ hB W₁ output ho' hob' hib hos (fun _ ↦ Ralg) (fun _ ↦ Malg)
    hnormal Op htest
  have hfinitePair := selectedFiniteDirectSolver_physicalPair_test_of_commonCharts
    f L hL hΩ hballΩ Q B hQ hB W₁ output ho' hob' hib hos
    (fun _ ↦ Ralg) (fun _ ↦ Malg) hnormal Op htest
  have hSeq := selectedFiniteDirectSolver_eq_commonChartSum f L Q B output ho' hob' hib hos
    Ralg Malg (hnormal 0) (Op 0)
  have hTeq := selectedFiniteCompleteError_eq_commonChartSum f L hL Q B W₁ output ho' hob' hib hos
    Ralg Malg (hnormal 1) (Op 1)
  have hballSupport : ball x r ⊆ tsupport output := by
    intro y hy
    apply subset_tsupport output
    change output y ≠ 0
    have hy' := interior_subset (hop (ball_subset_closedBall hy))
    rw [show output y = 1 from hy']
    exact one_ne_zero
  have hclosedΩ : closure (ball x r) ⊆ Ω :=
    (closure_minimal hballSupport (isClosed_tsupport output)).trans
      (hos.trans ((ball_subset_closedBall.trans (closedBall_subset_closedBall
        (by linarith [f.physicalRadius_pos] : f.physicalRadius ≤ 4*f.physicalRadius))).trans
          (f.physicalBall_coefficientDomain.trans hKΩ)))
  have hfiniteAE (u : graphTestSpace (d+1) (d+1)) :=
    finitePhysicalOperator_ae_of_fourier_one hΩ isOpen_ball hclosedΩ Q B hQ hB
      (fun p ↦ (f.chart p).index)
      (fun p ↦ selectedCommonChartSolver f p L Q B output ho' hob' hib (Op 0 p))
      (fun p ↦ maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
        (selectedSourceSymbol f p (2*L)) +
        selectedCommonChartResidual f p L Q B (W₁ p) output ho' hob' hib (Op 1 p))
      htest u (by
        rw [← hSeq]
        simpa only [Nat.cast_one, T, retarded, ite_true] using
          (hp 0 1 (T 0) (Or.inl rfl) (graphTestToLp u)
            (graphTest_memVectorFourierSobolev _ u)).1)
  refine ⟨hfiniteTest, hfinitePair, ?_, ?_, hp, ?_, ?_, selectedFiniteSourcePDO_commonOutput f L hL output ho' hob' hos, ?_, ?_⟩
  · intro u φ hφ hc hs j
    rw [inclusion_realCompression_physicalPairedSectorSum,
      inclusion_realCompression_physicalPairedSectorSum]
    exact hfinitePair _ φ hφ hc hs j
  · intro u
    obtain ⟨du, hdu, hduLp, heq⟩ := hfiniteAE u
    refine ⟨du, ?_, hduLp, ?_⟩
    · simpa only [← hSeq, T, retarded, ite_true] using hdu
    · simpa only [← hSeq, ← hTeq, T, retarded, ite_true] using heq
  · intro o k V hV u
    have hb (W : H →L[ℂ] H) (hW : W = T o ∨ W = (T o).adjoint) :
        ∀ v, MemVectorFourierSobolev (k : ℝ) v →
          MemVectorFourierSobolev ((k+o.val : ℕ) : ℝ) (W v) ∧
          vectorFourierSobolevNorm ((k+o.val : ℕ) : ℝ) (W v) ≤
            directCost o (k+o.val)*(vectorFourierSobolevNorm (k : ℝ) v+high k*‖v‖) := by
      simpa only [Nat.add_sub_cancel] using hp o (k+o.val) W hW
    have hdual (W : H →L[ℂ] H) (hwa : W.adjoint = T o ∨ W.adjoint = (T o).adjoint) :=
      negativeVectorFourierSobolev_tame_bound_of_adjoint (Nat.cast_nonneg k)
        (Nat.cast_nonneg (k+o.val)) (hdirectCost o (k+o.val)) (hhigh k) W
        (hb W.adjoint hwa) u
    rcases hV with rfl | rfl
    · simpa only [high, ← add_assoc, Nat.cast_add, Nat.cast_one, show (1 : ℝ)+1=2 by norm_num] using
        hdual (T o) (Or.inr rfl)
    · simpa only [high, ← add_assoc, Nat.cast_add, Nat.cast_one, show (1 : ℝ)+1=2 by norm_num] using
        hdual (T o).adjoint (Or.inl (ContinuousLinearMap.adjoint_adjoint _))
  · intro o
    exact ⟨selectedFiniteAlgebraicPDO_commonOutput f L Q B o output ho' hob' hos Ralg Malg
      (hnormal o), selectedFiniteAlgebraicPDO_commonOutput_adjoint f L Q B o output ho' hob' hos
      Ralg Malg (hnormal o)⟩
  · intro s V hV u hu
    have hs (W : H →L[ℂ] H)
        (hW : W = (sourceCutMultiplier output ho' hob').comp (selectedFiniteSourcePDO f L)-1 ∨
          W = ((sourceCutMultiplier output ho' hob').comp (selectedFiniteSourcePDO f L)-1).adjoint)
        (v : H) (hv : MemVectorFourierSobolev (s : ℝ) v) :
        MemVectorFourierSobolev (s : ℝ) (W v) ∧
        vectorFourierSobolevNorm (s : ℝ) (W v) ≤
          defectCost s*(vectorFourierSobolevNorm (s : ℝ) v+high s*‖v‖) := by
      obtain ⟨hm, hn⟩ := hdefect s W hW v hv
      exact ⟨hm, hn.trans (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (mul_nonneg (hhigh s) (norm_nonneg v))) (hdefectCost s))⟩
    have hr (W : H →L[ℂ] H) (hW : W = T 1 ∨ W = (T 1).adjoint)
        (v : H) (hv : MemVectorFourierSobolev (s : ℝ) v) :
        MemVectorFourierSobolev (s : ℝ) (W v) ∧
        vectorFourierSobolevNorm (s : ℝ) (W v) ≤
          directCost 1 s*(vectorFourierSobolevNorm (s : ℝ) v+high s*‖v‖) := by
      have hs : ((s-(1 : Fin 2).val : ℕ) : ℝ) ≤ (s : ℝ) := by
        exact_mod_cast Nat.sub_le s (1 : Fin 2).val
      obtain ⟨hm, hn⟩ := hp 1 s W hW v (fun j ↦ (hv j).mono hs)
      have hh : high (s-(1 : Fin 2).val) ≤ high s :=
        add_le_add (add_le_add le_rfl (cNorm_mono_order (Nat.add_le_add_right (Nat.sub_le _ _) _)))
          (cNorm_mono_order (Nat.add_le_add_right (Nat.sub_le _ _) _))
      exact ⟨hm, hn.trans (mul_le_mul_of_nonneg_left
        (add_le_add (vectorFourierSobolevNorm_mono hv hs)
          (mul_le_mul_of_nonneg_right hh (norm_nonneg v))) (hdirectCost 1 s))⟩
    exact direct_sobolev_add _ _ s s (defectCost s) (directCost 1 s) (high s) hs hr V hV u hu
  · intro U V hU hV
    obtain ⟨hf, ha⟩ := hlocalBound (T 1) 0 1 (directCost 1)
      (fun s ↦ high (s-1))
      (by simpa only [one_mul, Nat.add_zero, show (1 : Fin 2).val = 1 from rfl] using hp 1) U V hU hV
    have hlow : 1+high (1-1) ≤ 2+2*M := by
      simp only [high, Nat.sub_self, Nat.zero_add]
      linarith only [hQlow, hBlow]
    have hc : 0 ≤ localCost*directCost 1 1 := mul_nonneg hlocalCost.le (hdirectCost 1 1)
    have hn := mul_le_mul_of_nonneg_left hlow hc
    have hf' := fun u ↦ And.intro (hf u).1 ((hf u).2.trans (by
      simpa only [one_mul, Nat.add_zero] using mul_le_mul_of_nonneg_right hn (norm_nonneg u)))
    have ha' := fun v ↦ And.intro (ha v).1 ((ha v).2.trans (by
      simpa only [one_mul, Nat.add_zero] using mul_le_mul_of_nonneg_right hn (norm_nonneg v)))
    exact ⟨hf', ha', localRealCompression_physicalPair_restriction_bounds hU hV (T 1) 1
      (localCost*directCost 1 1*(2+2*M))
      (mul_nonneg hc (by linarith only [hM])) hf' ha'⟩

/-- Project the original supplied-family conclusion from the construction with
prescribed amplitude-band bounds on the same witnesses
(`app:ch_regular_base:eq:energy-complete-residual`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_finite_protected_direct_operator_bounds_and_equations_of_selected_collar
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (A₀ : Coeff) {K : Set E} {M : ℝ} (hM : 0 ≤ M)
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
    ∃ directCost : Fin 2 → ℕ → ℝ, (∀ o s, 0 ≤ directCost o s) ∧
    ∃ defectCost : ℕ → ℝ, (∀ s, 0 ≤ defectCost s) ∧
    ∃ localCost : ℝ, 0 < localCost ∧
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
      (∀ u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball x r → ∀ j,
        physicalTestAction
          (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
          (fun y ↦ (T 0 u y).ofLp) φ j = ∫ y, φ y •
            ((1 + selectedFiniteCompleteError f L Q B W₁ output ho hob (retarded 1)) u) y j) ∧
      (∀ u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball x r → ∀ j,
        physicalTestAction
          (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
          (fun y ↦ (physicalPairedSectorSum {()} (fun _ : Unit ↦ T 0) u y).ofLp) φ j =
          ∫ y, φ y • (physicalPairedSectorSum {()} (fun _ : Unit ↦
            1 + selectedFiniteCompleteError f L Q B W₁ output ho hob (retarded 1)) u) y j) ∧
      (∀ (u : Lp (EuclideanSpace ℝ (Fin (d+1))) 2 (volume : Measure E)) φ,
        ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball x r → ∀ j,
        physicalTestAction
          (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
          (fun y ↦ (l2ComplexInclusion volume
            (Realization.realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦ T 0)) u) y).ofLp)
          φ j = ∫ y, φ y • l2ComplexInclusion volume
            (Realization.realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦
              1 + selectedFiniteCompleteError f L Q B W₁ output ho hob (retarded 1))) u) y j) ∧
      (∀ u : graphTestSpace (d+1) (d+1), ∃ du : E → E →L[ℝ] (Fin (d+1) → ℂ),
        Mollification.HasWeakFDerivOn volume (fun y ↦ (T 0 (graphTestToLp u) y).ofLp) du univ ∧
        MemLp du 2 volume ∧
        physicalWeakApply
          (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
          (fun y ↦ (T 0 (graphTestToLp u) y).ofLp) du =ᵐ[volume.restrict (ball x r)]
          fun y ↦ ((1 + selectedFiniteCompleteError f L Q B W₁ output ho hob
            (retarded 1)) (graphTestToLp u) y).ofLp) ∧
      (∀ o : Fin 2, ∀ s : ℕ, ∀ V : H →L[ℂ] H, (V = T o ∨ V = (T o).adjoint) → ∀ u,
        MemVectorFourierSobolev ((s-o.val : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (V u) ∧
        vectorFourierSobolevNorm (s : ℝ) (V u) ≤ directCost o s *
          (vectorFourierSobolevNorm ((s-o.val : ℕ) : ℝ) u +
            (1+cNorm (closedBall x RQ) (s-o.val+sectorLowOrder d) Q+
              cNorm (closedBall x RQ) (s-o.val+sectorLowOrder d) B)*‖u‖)) ∧
      (∀ o : Fin 2, ∀ k : ℕ, ∀ V : H →L[ℂ] H, (V = T o ∨ V = (T o).adjoint) → ∀ u,
        MemVectorFourierSobolev (-(k : ℝ)) (V u) ∧
        vectorFourierSobolevNorm (-(k : ℝ)) (V u) ≤
          ((d+1 : ℝ)*(d+1)*directCost o (k+o.val)) *
            (2+cNorm (closedBall x RQ) (k+sectorLowOrder d) Q+
              cNorm (closedBall x RQ) (k+sectorLowOrder d) B) *
            vectorFourierSobolevNorm (-((k+o.val : ℕ) : ℝ)) u) ∧
      (∀ o : Fin 2,
        (sourceCutMultiplier output ho hob).comp (selectedFiniteAlgebraicPDO f (2*L) Q B o) =
          finitePhysicalOperator (fun p ↦ (f.chart p).index)
            (fun p ↦ maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
              (selectedAlgebraicSymbol f p (2*L) Q B o)) ∧
        (selectedFiniteAlgebraicPDO f (2*L) Q B o).adjoint.comp (sourceCutMultiplier output ho hob) =
          finitePhysicalOperator (fun p ↦ (f.chart p).index)
            (fun p ↦ (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
              (selectedAlgebraicSymbol f p (2*L) Q B o)).adjoint)) ∧
      (finitePhysicalOperator (fun p ↦ (f.chart p).index)
        (fun p ↦ maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
          (selectedSourceSymbol f p (2*L))) =
        (sourceCutMultiplier output ho hob).comp (selectedFiniteSourcePDO f L)) ∧
      (∀ s : ℕ, ∀ V : H →L[ℂ] H,
        (V = selectedFiniteCompleteError f L Q B W₁ output ho hob (retarded 1) ∨
          V = (selectedFiniteCompleteError f L Q B W₁ output ho hob (retarded 1)).adjoint) → ∀ u,
        MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (V u) ∧
        vectorFourierSobolevNorm (s : ℝ) (V u) ≤ (defectCost s+directCost 1 s)*
          (vectorFourierSobolevNorm (s : ℝ) u+
            (1+cNorm (closedBall x RQ) (s+sectorLowOrder d) Q+
              cNorm (closedBall x RQ) (s+sectorLowOrder d) B)*‖u‖)) ∧
      ∀ (U V : Set E) (hU : MeasurableSet U), MeasurableSet V →
        (∀ u : LocalL2 U (EuclideanSpace ℂ (Fin (d+1))),
          MemRestrictionSobolev V 1 (localRetardedOperator hU V (T 1) u) ∧
          restrictionSobolevNorm V 1 (localRetardedOperator hU V (T 1) u) ≤
            (localCost * directCost 1 1 * (2+2*M))*‖u‖) ∧
        (∀ v : LocalL2 V (EuclideanSpace ℂ (Fin (d+1))),
          MemRestrictionSobolev U 1 ((localRetardedOperator hU V (T 1)).adjoint v) ∧
          restrictionSobolevNorm U 1 ((localRetardedOperator hU V (T 1)).adjoint v) ≤
            (localCost * directCost 1 1 * (2+2*M))*‖v‖) ∧
        let R := localRealCompression hU V (physicalPairedSectorSum {()} (fun _ : Unit ↦ T 1))
        (∀ u : LocalL2 U (EuclideanSpace ℝ (Fin (d+1))),
          MemRestrictionSobolev V 1 (R u) ∧ restrictionSobolevNorm V 1 (R u) ≤
            (4*(localCost*directCost 1 1*(2+2*M)))*‖u‖) ∧
        (∀ v : LocalL2 V (EuclideanSpace ℝ (Fin (d+1))),
          MemRestrictionSobolev U 1 (R.adjoint v) ∧ restrictionSobolevNorm U 1 (R.adjoint v) ≤
            (4*(localCost*directCost 1 1*(2+2*M)))*‖v‖) := by
  have hbandConstruction4 := exists_finite_protected_direct_operator_bounds_and_equations_of_selected_collar_on_enlarged_bands
      hΩ x hRQ hKΩ A₀ hM f hf (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ zero_lt_one)
  obtain ⟨evolutionTime, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨speedGap, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨rootSize, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨rootCost, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hprotection, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hcommon, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hradii, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hevolution, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hlocal, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨L, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hL, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨angular, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨χout, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨χsource, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hs, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨output, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨r, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hr, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨ho, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨horange, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hoc, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hos, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hop, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hsourceMask, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨houtMask, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hselected, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hthreshold, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨base, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨cost, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨maskCost, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨Rbox, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨Dpdo, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨Dgain, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨Gain, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨ra, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨rb, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨amplitudeCost, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hbase, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hcost, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hmaskCost, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hRbox, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hDpdo, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hDgain, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hGain, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hra, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨hrab, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨_, hbandConstruction4⟩ := hbandConstruction4
  obtain ⟨_, hbandConstruction4⟩ := hbandConstruction4
  have hrest := hbandConstruction4
  refine ⟨evolutionTime, ?_⟩
  refine ⟨speedGap, ?_⟩
  refine ⟨rootSize, ?_⟩
  refine ⟨rootCost, ?_⟩
  refine ⟨hprotection, ?_⟩
  refine ⟨hcommon, ?_⟩
  refine ⟨hradii, ?_⟩
  refine ⟨hevolution, ?_⟩
  refine ⟨hlocal, ?_⟩
  refine ⟨L, ?_⟩
  refine ⟨hL, ?_⟩
  refine ⟨angular, ?_⟩
  refine ⟨χout, ?_⟩
  refine ⟨χsource, ?_⟩
  refine ⟨hs, ?_⟩
  refine ⟨output, ?_⟩
  refine ⟨r, ?_⟩
  refine ⟨hr, ?_⟩
  refine ⟨ho, ?_⟩
  refine ⟨horange, ?_⟩
  refine ⟨hoc, ?_⟩
  refine ⟨hos, ?_⟩
  refine ⟨hop, ?_⟩
  refine ⟨hsourceMask, ?_⟩
  refine ⟨houtMask, ?_⟩
  refine ⟨hselected, ?_⟩
  refine ⟨hthreshold, ?_⟩
  refine ⟨base, ?_⟩
  refine ⟨cost, ?_⟩
  refine ⟨maskCost, ?_⟩
  refine ⟨Rbox, ?_⟩
  refine ⟨Dpdo, ?_⟩
  refine ⟨Dgain, ?_⟩
  refine ⟨Gain, ?_⟩
  refine ⟨ra, ?_⟩
  refine ⟨rb, ?_⟩
  refine ⟨amplitudeCost, ?_⟩
  refine ⟨hbase, ?_⟩
  refine ⟨hcost, ?_⟩
  refine ⟨hmaskCost, ?_⟩
  refine ⟨hRbox, ?_⟩
  refine ⟨hDpdo, ?_⟩
  refine ⟨hDgain, ?_⟩
  refine ⟨hGain, ?_⟩
  refine ⟨hra, ?_⟩
  refine ⟨hrab, ?_⟩
  exact hrest

end JanetCartan.RegularSector.FiniteAssembly
