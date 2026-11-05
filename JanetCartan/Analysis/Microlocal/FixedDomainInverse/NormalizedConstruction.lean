module

public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.WeakConstruction
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.DirectConstruction.Localization
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.CoefficientNorms
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.Smooth

/-!
# Fixed inversion of the normalized complete residual on the supplied family

Apply the actual normalized characteristic-plus-elliptic constructor to the
existing fixed-cutoff inverse. All three normalized operators retain the same
external half, family, physical masks, full zeroth-order coefficient and doubled
radial collar. The complete source discrepancy remains outside the inverted
residual. The original tested, smooth and weak equations are retained on the
same witnesses, together with both fixed-shift measured gains and one smooth
supported correction. Constants and cutoffs precede the varying coefficients.

Consumers: the corrected smooth physical solver and `Response.Compatible`.
Sources: `app:ch_regular:thm:exact-correction`, `app:ch_regular:eq:inverse-tame`,
`app:ch_regular:eq:exact-physical`, `real-sector-normalization`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 24000000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius NNReal ENNReal
namespace JanetCartan.FixedDomainInverse
open RegularSector RegularSector.FiniteAssembly RegularSector.Realization
open RegularSector.NormalizedSolver RegularSector.EllipticComplement
open Characteristic Characteristic.ResidualCoordinates Characteristic.UniformEvolution
open Characteristic.ConicAmplitude Characteristic.AmplitudeBounds Characteristic.RootFamily
open Characteristic.ConicPhase Characteristic.UniformAmplitudes Characteristic.EvolutionIntegral.SymbolBudgets
open Characteristic.EvolutionIntegral FiniteMasks FiniteMasks.ActualFamily
open FinitePdo FiniteEvolution FourierIntegral FourierIntegral.LowBounds Pseudodifferential
open JanetCartan.CharacteristicTransport.CompleteResidual
open Characteristic.RetardedLocalization LocalSobolev SmallSupport
open FiniteResidual.FiniteIdentity CoefficientNorms
open ActualCarriers Characteristic.AlgebraicChart Characteristic.AlgebraicSymbols
open Characteristic.PdoRealization FiniteAlgebraic AmplitudeBound
open ArbitraryAccuracy.ResidualLocalization ResponseTransfer.Complement
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "TPoint" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)
local notation "Coeff" => Fin (d+1) → Mat
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

local notation "CF" => EuclideanSpace ℂ (Fin (d+1))
local notation "RF" => EuclideanSpace ℝ (Fin (d+1))

/-- The actual normalized complete residual on the supplied protected family
has one fixed-cutoff inverse with both inverse identities, the original
forward/literal-adjoint one-gain shift and all-order tame bounds. Its smooth
supported correction and every tested/smooth/weak equation use the same
normalized solver, source and residual. The full source discrepancy remains
explicit; no angular accuracy is asserted here
(`app:ch_regular:thm:exact-correction`, `app:ch_regular:eq:inverse-tame`,
`app:ch_regular:eq:exact-physical`, `real-sector-normalization`). -/
theorem exists_normalized_complete_fixed_inverse_of_selected_collar
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
              c.row c.col y ζ') ≤ C m * (1 + cNorm (closedBall x RQ) m Q))) 
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
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
    ∃ (normRadius : ℝ) (hQR : RQ < normRadius)
      (hNormBall : closedBall x normRadius ⊆ Ω),
    ∃ coefficientCost : ℕ → ℝ, (∀ m, 1 ≤ coefficientCost m) ∧
      (∀ (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
          (B : Euclidean (d + 1) → MetricTensor (d + 1))
          (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω),
        let uQ := smoothCoefficientL2 hΩ (hRQ.trans hQR) hNormBall Q hQ
        let uB := smoothCoefficientL2 hΩ (hRQ.trans hQR) hNormBall B hB
        (∀ k, MemRestrictionSobolev (ball x normRadius) k uQ ∧
          MemRestrictionSobolev (ball x normRadius) k uB) ∧
        ∀ m,
          cNorm (closedBall x RQ) m Q ≤
            coefficientCost m * restrictionSobolevNorm (ball x normRadius) (m + (d + 2)) uQ ∧
          cNorm (closedBall x RQ) m B ≤
            coefficientCost m * restrictionSobolevNorm (ball x normRadius) (m + (d + 2)) uB ∧
          1 + cNorm (closedBall x RQ) m Q + cNorm (closedBall x RQ) m B ≤
            coefficientCost m * (1 + restrictionSobolevNorm (ball x normRadius) (m + (d + 2)) uQ +
              restrictionSobolevNorm (ball x normRadius) (m + (d + 2)) uB)) ∧
    ∃ hbudget : 0 ≤ 4*completeLocalCost,
    ∃ hrU : 0 < min r f.physicalRadius,
    ∃ hUW : ball x (min r f.physicalRadius) ⊆ ball x normRadius,
    ∃ χ₂ χ₃ : ContDiffBump x,
      tsupport (χ₂ : E → ℝ) ⊆ ball x (min r f.physicalRadius) ∧
      tsupport (χ₃ : E → ℝ) ⊆ ball x (min r f.physicalRadius) ∧
      (∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1) ∧
      (ball x χ₂.rIn).Nonempty ∧ IsOpen (ball x χ₂.rIn) ∧
      ball x χ₂.rIn ⊆ ball x (min r f.physicalRadius) ∧
      (∀ y ∈ ball x χ₂.rIn, χ₂ y = 1) ∧
      (∀ y ∈ ball x (min r f.physicalRadius), output y = 1 ∧ f.inputMask y = 1) ∧
    ∃ gainCost : ℕ → ℝ, (∀ s, 0 ≤ gainCost s) ∧
    ∀ (Q : E → Fin (d+1) → Mat) (hQ : ContDiffOn ℝ ∞ Q Ω),
      MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
      cNorm (closedBall x RQ) (sectorLowOrder d) Q ≤ M →
    ∀ (B : E → Mat) (hB : ContDiffOn ℝ ∞ B Ω),
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
      ((((∀ (u : H) (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ ball x r → ∀ j,
        physicalTestAction
          (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
          (fun y ↦ (T 0 u y).ofLp) φ j = ∫ y, φ y •
            ((1 + selectedFiniteCompleteError f L Q B W₁ output ho hob (retarded 1)) u) y j) ∧
      (∀ (u : H) (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ ball x r → ∀ j,
        physicalTestAction
          (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
          (fun y ↦ (pairedSolver f hK L Q B output ho hob (retarded 0) u y).ofLp) φ j =
          ∫ y, φ y • (pairedSource f hK L output ho hob +
            pairedResidual f hK L Q B output ho hob W₁ (retarded 1)) u y j) ∧
      (∀ (u : Lp (EuclideanSpace ℝ (Fin (d+1))) 2 (volume : Measure E)) (φ : E → ℝ),
        ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball x r → ∀ j,
        physicalTestAction
          (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
          (fun y ↦ (l2ComplexInclusion volume
            (realSolver f hK L Q B output ho hob (retarded 0) u) y).ofLp) φ j =
          ∫ y, φ y • l2ComplexInclusion volume
            ((realSource f hK L output ho hob +
              realResidual f hK L Q B output ho hob W₁ (retarded 1)) u) y j) ∧
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
            (4*completeLocalCost)*‖v‖)) ∧
      ∃ S : Fin 2 → graphTestSpace (d+1) (d+1) →ₗ[ℂ] (E → CF),
      ∃ A : graphTestSpace (d+1) (d+1) →ₗ[ℂ] (E → CF),
      ∃ SR : Fin 2 → realSectorTestSpace d (d+1) →ₗ[ℝ] (E → RF),
      ∃ AR : realSectorTestSpace d (d+1) →ₗ[ℝ] (E → RF),
      (∀ o u, ContDiff ℝ ∞ (S o u) ∧ S o u =ᵐ[volume]
        (if o = 0 then pairedSolver f hK L Q B output ho hob (retarded 0)
          else pairedResidual f hK L Q B output ho hob W₁ (retarded 1)) (graphTestToLp u)) ∧
      (∀ u, ContDiff ℝ ∞ (A u) ∧ A u =ᵐ[volume]
        pairedSource f hK L output ho hob (graphTestToLp u)) ∧
      (∀ o u, ContDiff ℝ ∞ (SR o u) ∧ SR o u =ᵐ[volume]
        (if o = 0 then realSolver f hK L Q B output ho hob (retarded 0)
          else realResidual f hK L Q B output ho hob W₁ (retarded 1)) (realSectorTestToLp u) ∧
        (fun y ↦ euclideanComplexInclusion (SR o u y)) = S o (realSectorTestInclusion u)) ∧
      (∀ u, ContDiff ℝ ∞ (AR u) ∧ AR u =ᵐ[volume]
        realSource f hK L output ho hob (realSectorTestToLp u) ∧
        (fun y ↦ euclideanComplexInclusion (AR u y)) = A (realSectorTestInclusion u)) ∧
      (∀ u, EqOn (physicalWeakApply
        (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (S 0 u y).ofLp) (fderiv ℝ (fun y ↦ (S 0 u y).ofLp)))
        (fun y ↦ (A u y + S 1 u y).ofLp) (ball x r)) ∧
      (∀ u, EqOn (physicalWeakApply
        (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (euclideanComplexInclusion (SR 0 u y)).ofLp)
        (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (SR 0 u y)).ofLp)))
        (fun y ↦ (euclideanComplexInclusion (AR u y + SR 1 u y)).ofLp) (ball x r))) ∧
      (∀ u : graphTestSpace (d+1) (d+1),
        ∃ D : E → E →L[ℝ] (Fin (d+1) → ℂ),
          Mollification.HasWeakFDerivOn volume
            (fun y ↦ (pairedSolver f hK L Q B output ho hob (retarded 0) (graphTestToLp u) y).ofLp)
            D univ ∧ MemLp D 2 volume ∧
          physicalWeakApply
            (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
            (fun y ↦ (pairedSolver f hK L Q B output ho hob (retarded 0) (graphTestToLp u) y).ofLp)
            D =ᵐ[volume.restrict (ball x r)]
            fun y ↦ ((pairedSource f hK L output ho hob +
              pairedResidual f hK L Q B output ho hob W₁ (retarded 1)) (graphTestToLp u) y).ofLp) ∧
      (∀ u : realSectorTestSpace d (d+1),
        ∃ D : E → E →L[ℝ] (Fin (d+1) → ℂ),
          Mollification.HasWeakFDerivOn volume
            (fun y ↦ (l2ComplexInclusion volume
              (realSolver f hK L Q B output ho hob (retarded 0) (realSectorTestToLp u)) y).ofLp)
            D univ ∧ MemLp D 2 volume ∧
          physicalWeakApply
            (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
            (fun y ↦ (l2ComplexInclusion volume
              (realSolver f hK L Q B output ho hob (retarded 0) (realSectorTestToLp u)) y).ofLp)
            D =ᵐ[volume.restrict (ball x r)]
            fun y ↦ (l2ComplexInclusion volume
              ((realSource f hK L output ho hob +
                realResidual f hK L Q B output ho hob W₁ (retarded 1)) (realSectorTestToLp u)) y).ofLp)) ∧
      let U := ball x (min r f.physicalRadius)
      let W := ball x normRadius
      let R := localRealCompression (U := W) isOpen_ball.measurableSet U
        (pairedResidual f hK L Q B output ho hob W₁ (retarded 1))
      ∃ hmem : ∀ u, MemRestrictionSobolev U 1 (R u),
      ∃ hbound : ∀ u, restrictionSobolevNorm U 1 (R u) ≤
          (4*completeLocalCost)*‖u‖,
      let Rp := residualToLpOnBall x hrU hUW R hmem hbudget hbound
      let Kloc := localizedResidual (two_lt_ballSobolevExponent x hrU).le
        χ₂ χ₃ isOpen_ball.measurableSet Rp
      let Inv := neumannInverse Kloc
      let Corr := correctedSource (two_lt_ballSobolevExponent x hrU).le
        χ₂ χ₃ isOpen_ball.measurableSet Rp
      let uQ := smoothCoefficientL2 hΩ (hRQ.trans hQR) hNormBall Q hQ
      let uB := smoothCoefficientL2 hΩ (hRQ.trans hQR) hNormBall B hB
      let a := fun s ↦ restrictionSobolevNorm W s uQ + restrictionSobolevNorm W s uB
      let β := sectorLowOrder d + (d+2)
      ‖Kloc‖ ≤ θ ∧ HasSum (fun j : ℕ ↦ (-Kloc)^j) Inv ∧
      (1+Kloc)*Inv = 1 ∧ Inv*(1+Kloc) = 1 ∧ ‖Inv‖ ≤ (1-θ)⁻¹ ∧
      (∀ u : LocalL2 W E, Kloc u =ᵐ[volume.restrict W]
        zeroExtend isOpen_ball.measurableSet
          (bumpL2 (p := 2) le_rfl χ₂ (R (bumpL2 (p := 2) le_rfl χ₃ u)))) ∧
      (∀ (s : ℕ) (u : LocalL2 W E), MemRestrictionSobolev W s u →
        (MemRestrictionSobolev W (s+1) (Kloc u) ∧
          restrictionSobolevNorm W (s+1) (Kloc u) ≤ gainCost (s+1) *
            (restrictionSobolevNorm W s u + (1+a (s+1+β))*‖u‖)) ∧
        (MemRestrictionSobolev W (s+1) (Kloc.adjoint u) ∧
          restrictionSobolevNorm W (s+1) (Kloc.adjoint u) ≤ gainCost (s+1) *
            (restrictionSobolevNorm W s u + (1+a (s+1+β))*‖u‖))) ∧
      (∀ (s : ℕ) (u : LocalL2 W E), MemRestrictionSobolev W s u →
        MemRestrictionSobolev W s (Inv u) ∧
          restrictionSobolevNorm W s (Inv u) ≤ inverseTameConstant θ gainCost s *
            (restrictionSobolevNorm W s u + (1+a (s+β))*‖u‖)) ∧
      (∀ h : smoothSource W E, ∃ v : E → E,
        ContDiffOn ℝ ∞ v W ∧ v =ᵐ[volume.restrict W] Inv h) ∧
      (∃ Zsmooth : smoothSource W E →ₗ[ℝ] (E → E), ∀ h,
        ContDiff ℝ ∞ (Zsmooth h) ∧ Zsmooth h =ᵐ[volume.restrict W] Corr h ∧
        tsupport (Zsmooth h) ⊆ tsupport (χ₂ : E → ℝ) ∧
        W.indicator (Zsmooth h) = Zsmooth h ∧
        Zsmooth h =ᵐ[volume] zeroExtend isOpen_ball.measurableSet (Corr h) ∧
        ∀ y, χ₃ y • Zsmooth h y = Zsmooth h y) ∧
      ∀ h : LocalL2 W E,
        (∀ᵐ y ∂volume.restrict W, y ∉ tsupport (χ₂ : E → ℝ) → Corr h y = 0) ∧
        bumpL2 (p := 2) le_rfl χ₃ (Corr h) = Corr h ∧
        (∀ᵐ y ∂volume.restrict (ball x χ₂.rIn), Corr h y + R (Corr h) y = h y) ∧
        (∀ᵐ y ∂volume, y ∉ tsupport (χ₂ : E → ℝ) →
          zeroExtend isOpen_ball.measurableSet (Corr h) y = 0) ∧
        ‖Corr h‖ ≤ (1-θ)⁻¹*‖h‖ := by
  classical
  have hnormData := exists_coefficient_restriction_norm_bounds
    (d := d) (Ω := Ω) (x := x) (RQ := RQ) hΩ hRQ hKΩ
  let normRadius := hnormData.choose
  have hQR : RQ < normRadius := hnormData.choose_spec.choose
  have hNormBall : closedBall x normRadius ⊆ Ω := hnormData.choose_spec.choose_spec.choose
  have hcoeffData := hnormData.choose_spec.choose_spec.choose_spec.2.2.2.2
  let coefficientCost := hcoeffData.choose
  have hcoefficientCost := hcoeffData.choose_spec.1
  have hcoefficientBounds := hcoeffData.choose_spec.2
  have hconstructed := exists_normalized_complete_weak_smooth_operators_of_selected_collar
    (d := d) (Ω := Ω) hΩ x (RQ := RQ) hRQ hKΩ A₀ hK (M := M) hM f hf
  choose evolutionTime speedGap rootSize rootCost hprotection hcommon
    hradii hevolution hlocal hfixed using hconstructed
  refine ⟨evolutionTime, speedGap, rootSize, rootCost, hprotection, hcommon,
    hradii, hevolution, hlocal, ?_⟩
  choose L hL angular χout χsource hs output r hr ho horange hoc hos
    hop hsourceMask houtMask hselected hthreshold hconstants using hfixed
  refine ⟨L, hL, angular, χout, χsource, hs, output, r, hr, ho, horange, hoc, hos,
    hop, hsourceMask, houtMask, hselected, hthreshold, ?_⟩
  choose base cost maskCost Rbox Dpdo Dgain Gain ra rb amplitudeCost
    hbase hcost hmaskCost hRbox hDpdo hDgain hGain hra hrab hamp
    hangular hcoverage completeCost hcompleteCost completeLocalCost hcompleteLocalCost
    hoperators using hconstants
  refine ⟨base, cost, maskCost, Rbox, Dpdo, Dgain, Gain, ra, rb, amplitudeCost,
    hbase, hcost, hmaskCost, hRbox, hDpdo, hDgain, hGain, hra, hrab, hamp, hangular, hcoverage,
    completeCost, hcompleteCost, completeLocalCost, hcompleteLocalCost, normRadius, hQR, hNormBall,
    coefficientCost, hcoefficientCost, hcoefficientBounds, ?_⟩
  have hbudget : 0 ≤ 4*completeLocalCost := mul_nonneg (by norm_num) hcompleteLocalCost
  have hrU : 0 < min r f.physicalRadius := lt_min hr f.physicalRadius_pos
  have hUW : ball x (min r f.physicalRadius) ⊆ ball x normRadius :=
    (ball_subset_ball ((min_le_right _ _).trans
      (show f.physicalRadius ≤ 4*f.physicalRadius by linarith only [f.physicalRadius_pos]))).trans
      (ball_subset_closedBall.trans
        (f.physicalBall_coefficientDomain.trans (closedBall_subset_ball hQR)))
  obtain ⟨χ₂, χ₃, h₂, h₃, hnest, hne, hopen, hcore, hplateau, hinv⟩ :=
    exists_fixed_cutoffs_localSobolevInverse (F := E) (Nat.zero_lt_succ d)
      x hrU isOpen_ball.measurableSet hUW (mem_ball_self hrU) hbudget hθ₀ hθ₁
  refine ⟨hbudget, hrU, hUW, χ₂, χ₃, h₂, h₃, hnest, hne, hopen, hcore, hplateau, ?_, ?_⟩
  · intro y hy
    refine ⟨show y ∈ {y | output y = 1} from interior_subset
      (hop (ball_subset_closedBall (ball_subset_ball (min_le_left _ _) hy))), ?_⟩
    exact show y ∈ {y | f.inputMask y = 1} from interior_subset
      (f.inputMask_plateau (ball_subset_closedBall
        (ball_subset_ball ((min_le_right _ _).trans (by linarith only [f.physicalRadius_pos])) hy)))
  obtain ⟨D, hD, hmeasured⟩ := exists_measuredOperator_physical_positive_constants
    (q := d+1) χ₂ χ₃ χ₂.contDiff χ₃.contDiff χ₂.hasCompactSupport χ₃.hasCompactSupport
    (bump_norm_le_one χ₂) (bump_norm_le_one χ₃)
  let gainCost s := (8*(D s*completeCost 1 s))*coefficientCost (s-1+sectorLowOrder d)
  have hgainCost s : 0 ≤ gainCost s := mul_nonneg
    (mul_nonneg (by norm_num) (mul_nonneg (zero_le_one.trans (hD s)) (hcompleteCost 1 s)))
    (zero_le_one.trans (hcoefficientCost _))
  refine ⟨gainCost, hgainCost, ?_⟩
  intro Q hQ hQrange hQlow B hB hBlow
  have hoperatorData := hoperators Q hQ hQrange hQlow B hB hBlow
  choose Φ C G Op hprotected hdata ho' hob hib hest using hoperatorData
  refine ⟨Φ, C, G, Op, hprotected, hdata, ho', hob, hib, ?_⟩
  intro retarded W₁ T Tplus
  refine ⟨hest, ?_⟩
  intro U W R
  have hendpoint := hest.1.1.2.2.2.2.2
  have hreal := (hendpoint W U isOpen_ball.measurableSet isOpen_ball.measurableSet).2.2.1
  have hmem : ∀ u, MemRestrictionSobolev U 1 (R u) := fun u ↦ (hreal u).1
  have hbound : ∀ u, restrictionSobolevNorm U 1 (R u) ≤
      (4*completeLocalCost)*‖u‖ := fun u ↦ (hreal u).2
  refine ⟨hmem, hbound, ?_⟩
  intro Rp Kloc Inv Corr uQ uB a β
  obtain ⟨hK, hsum, hleft, hright, hnorm, hgraded⟩ := hinv R hmem hbound
  obtain ⟨hzero, hsupport⟩ := localSobolevInverse_zeroExtension_support x hrU
    isOpen_ball.measurableSet hUW R hmem hbudget hbound χ₂ χ₃ hθ₁ hnest hcore hplateau hK
  have hcoeff := hcoefficientBounds Q B hQ hB
  have ha s : 0 ≤ a s := add_nonneg restrictionSobolevNorm_nonneg restrictionSobolevNorm_nonneg
  have hmono : Monotone a := fun s t hst ↦ add_le_add
    (restrictionSobolevNorm_mono (hcoeff.1 t).1 hst)
    (restrictionSobolevNorm_mono (hcoeff.1 t).2 hst)
  have hpositive := hest.1.1.2.2.2.1
  let high s := 1+cNorm (closedBall x RQ) (s-1+sectorLowOrder d) Q+
    cNorm (closedBall x RQ) (s-1+sectorLowOrder d) B
  have hhigh s : 0 ≤ high s := add_nonneg
    (add_nonneg zero_le_one (cNorm_nonneg _ _ _)) (cNorm_nonneg _ _ _)
  have hmeasured' := hmeasured (Tplus 1) (completeCost 1) high (hcompleteCost 1) hhigh
    (hpositive 1) W W isOpen_ball.measurableSet isOpen_ball.measurableSet
      (h₃.trans hUW) (h₂.trans hUW)
  have hid : Kloc = localRealCompression (U := W) isOpen_ball.measurableSet W
      (physicalPairedSectorSum {()} (fun _ : Unit ↦
        measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
          (bump_norm_le_one χ₂) (bump_norm_le_one χ₃) (Tplus 1))) :=
    localizedResidual_eq_real_measuredOperator isOpen_ball.measurableSet x hrU hUW
      (Tplus 1) hmem hbudget hbound χ₂ χ₃ h₂
  have hg (s : ℕ) (u : LocalL2 W E) (hu : MemRestrictionSobolev W s u) :
      (MemRestrictionSobolev W (s+1) (Kloc u) ∧
        restrictionSobolevNorm W (s+1) (Kloc u) ≤ gainCost (s+1) *
          (restrictionSobolevNorm W s u + (1+a (s+1+β))*‖u‖)) ∧
      (MemRestrictionSobolev W (s+1) (Kloc.adjoint u) ∧
        restrictionSobolevNorm W (s+1) (Kloc.adjoint u) ≤ gainCost (s+1) *
          (restrictionSobolevNorm W s u + (1+a (s+1+β))*‖u‖)) := by
    have hc := (hcoeff.2 (s+sectorLowOrder d)).2.2
    have hh : high (s+1) ≤ coefficientCost (s+sectorLowOrder d)*(1+a (s+1+β)) := by
      dsimp only [high]
      simp only [Nat.add_sub_cancel]
      apply hc.trans
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (hcoefficientCost _))
      change 1+restrictionSobolevNorm W (s+sectorLowOrder d+(d+2)) uQ+
        restrictionSobolevNorm W (s+sectorLowOrder d+(d+2)) uB ≤ 1+a (s+1+β)
      have ham := hmono (show s+sectorLowOrder d+(d+2) ≤ s+1+β by dsimp only [β]; omega)
      dsimp only [a] at ham
      linarith
    have henlarge {v : LocalL2 W E} (hn : restrictionSobolevNorm W (s+1) v ≤
        (8*(D (s+1)*completeCost 1 (s+1)))*(restrictionSobolevNorm W s u+high (s+1)*‖u‖)) :
        restrictionSobolevNorm W (s+1) v ≤ gainCost (s+1)*
          (restrictionSobolevNorm W s u+(1+a (s+1+β))*‖u‖) := by
      apply hn.trans
      dsimp only [gainCost]
      simp only [Nat.add_sub_cancel]
      calc
        _ ≤ (8*(D (s+1)*completeCost 1 (s+1)))*
            (coefficientCost (s+sectorLowOrder d)*restrictionSobolevNorm W s u+
              (coefficientCost (s+sectorLowOrder d)*(1+a (s+1+β)))*‖u‖) := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg (by norm_num) (mul_nonneg (zero_le_one.trans (hD _)) (hcompleteCost _ _)))
          exact add_le_add
            (le_mul_of_one_le_left restrictionSobolevNorm_nonneg (hcoefficientCost _))
            (mul_le_mul_of_nonneg_right hh (norm_nonneg u))
        _ = _ := by ring
    rw [hid]
    have hm := hmeasured' (s+1)
    simp only [Nat.add_sub_cancel] at hm
    exact ⟨⟨(hm.2.2.1 u hu).1, henlarge (hm.2.2.1 u hu).2⟩,
      ⟨(hm.2.2.2 u hu).1, henlarge (hm.2.2.2 u hu).2⟩⟩
  have hreg s u hu := (hg s u hu).1.1
  have hinverse := hgraded gainCost a β hgainCost ha hmono hreg
    (fun s u hu ↦ (hg s u hu).1.2)
  refine ⟨hK, hsum, hleft, hright, hnorm, hzero, hg, hinverse, ?_, ?_, hsupport⟩
  · intro h
    exact exists_contDiffOn_infty_ae_eq_of_memRestrictionSobolev isOpen_ball (Inv h)
      (fun s ↦ (hinverse s h (h.property s)).1)
  refine ⟨smoothCorrectedSourceLinear isOpen_ball (two_lt_ballSobolevExponent x hrU).le
    χ₂ χ₃ isOpen_ball.measurableSet Rp (hK.trans_lt hθ₁) (h₂.trans hUW) hreg, ?_⟩
  intro h
  have hz := smoothCorrectedSource_spec isOpen_ball (two_lt_ballSobolevExponent x hrU).le
    χ₂ χ₃ isOpen_ball.measurableSet Rp (hK.trans_lt hθ₁) (h₂.trans hUW) hreg h
  exact ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2,
    smoothCorrectedSource_ae_zeroExtend isOpen_ball (two_lt_ballSobolevExponent x hrU).le
      χ₂ χ₃ isOpen_ball.measurableSet Rp (hK.trans_lt hθ₁) (h₂.trans hUW) hreg h,
    smoothCorrectedSource_cutoff isOpen_ball (two_lt_ballSobolevExponent x hrU).le
      χ₂ χ₃ isOpen_ball.measurableSet Rp (hK.trans_lt hθ₁) (h₂.trans hUW) hreg hnest h⟩

end JanetCartan.FixedDomainInverse
