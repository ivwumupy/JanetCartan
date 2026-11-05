module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.InitializedObservedResidual.RetainedRetardedLeakage
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.SuppliedPdoLeakage
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.SignedCharacteristicLeakage
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrescribedEllipticLeakage
public import JanetCartan.Analysis.Microlocal.SelectedResidualInputs.CollarDomain

/-!
# Complete residual leakage on a supplied normalized inverse

Every analytic certificate in the supplied normalized inverse is used directly.
The same characteristic residual, endpoint/algebraic PDO terms and elliptic
complement yield leakage for the literal half-scaled and reflected letters.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteAssembly
open SelectedResidualInputs FourierIntegral.LowBounds.FrequencyCutoff EvolutionIntegratedLocalization
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
open FiniteChain.Graph FiniteChain.Graph.KernelLimits FiniteChain.Graph.PhysicalShells
open SelectedEvenProofMasks ProtectedMasks JanetCartan.Localization EvolutionIntegratedLocalization
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "TPoint" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)

local notation "Coeff" => Fin (d+1) → Mat
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ

/-- Apply the characteristic, endpoint, algebraic and elliptic producers to
one supplied normalized inverse. The algebraic and geometric hypotheses below
are the unchanged certificates returned by
`exists_normalized_complete_smooth_fixed_inverse_of_selected_collar_on_enlarged_bands`;
no source localization, graph regularization or residual leakage is an input.
All losses precede the accuracy and all constants precede the varying history
and proof localizers. This supplies the factor leakage field in the original
`ObservedChains.measuredResidual_hchain_of_individual_estimates` application
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_retained_prescribed_complete_residual_leakage_constants
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (A₀ : Coeff) {K : Set E} {M : ℝ}
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hKcompact : IsCompact K)
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
    (Aprofile : ℕ → ℝ) (hAprofile : ∀ k, 0 ≤ Aprofile k)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (L : ℝ) (hL : f.radialThreshold ≤ L)
    (angular : f.centers → Euclidean d → ℝ) (χout χsource : f.centers → E → ℂ)
    (hs : ∀ p, ContDiff ℝ ∞ (χsource p))
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hout : tsupport output ⊆ ball x f.physicalRadius)
    (hob : ∀ y, ‖output y‖ ≤ 1) (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
    (houtMask : ∀ p y, (output y : ℂ) * χout p ((physicalCoordinates (f.chart p).index).symm y) =
      (output y : ℂ))
    (hsourceMask : ∀ p y, χsource p ((physicalCoordinates (f.chart p).index).symm y) *
      (f.inputMask y : ℂ) = (f.inputMask y : ℂ))
    (base : Fin 2 → f.centers → ℝ) (cost : Fin 2 → f.centers → ℕ → ℝ)
    (Rbox : f.centers → ℝ) (Dpdo Dgain Gain : f.centers → ℕ → ℝ)
    (ra rb : f.centers → ℝ) (amplitudeCost : f.centers → ℕ → ℝ)
    (hra : ∀ p, 0 < ra p) (hrab : ∀ p, ra p ≤ rb p)
    (hamp : ∀ p m, 0 < amplitudeCost p m)
    (hangular : ∀ p, ContDiff ℝ ∞ (angular p) ∧
      ∀ η ∈ tsupport (angular p), 0 < (f.chart p).radialSection η)
    (hplateau : ∀ p, ∀ ζ ∈ tsupport (fun ξ ↦ (dilatedConicMask (f.angularMask p) (2*L)
      (physicalCoordinates (f.chart p).index ξ) : ℂ)),
      conicMask (angular p) =ᶠ[𝓝 (spatialPart ζ)] fun _ ↦ (1 : ℝ))
    (hcoverage : ∀ p, FinitePdo.RetainedConstruction.DiagonalFrequencyCoverage
      (f.chart p).radialSection (coordinateSplit (f.chart p).index p.val.val).2
      ((f.chart p).bufferRadius/2) (ra p) (rb p) (selectedEndpointMultiplier f p L))
    (halgebraic : ∀ p : f.centers,
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
                      (1 + high) * vectorFourierSobolevNorm (-((n : ℝ)+1)) u)) :
    ∀ a₀ b₀ : ℝ, 0 < a₀ →
    ∃ tlo thi : ℝ, 0 < tlo ∧ 0 < thi ∧
      ∀ {ι κ ιu ιz : Type*} [Fintype ι] [Fintype κ] [Fintype ιu] [Fintype ιz],
      ∀ (eT : Module.Basis ι ℝ (JointVariables E))
        (eI : Module.Basis κ ℝ (ℝ × JointVariables E))
        (eu : OrthonormalBasis ιu ℝ E) (ez : OrthonormalBasis ιz ℝ E),
      ∀ J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E,
      MeasurePreserving (graphInputCoordinates J) volume volume →
      ∀ (buffer Rbase εcollar δT δI : ℝ) (Hmask Hcollar : ℕ → ℝ),
      0 < buffer → (∀ j, 0 ≤ Hmask j) → (∀ j, 0 ≤ Hcollar j) →
      0 < εcollar → 0 < δT → 0 < δI →
      ∀ χ : (ℝ × JointVariables E) → ℂ, ContDiff ℝ ∞ χ →
      (∀ v, |v.1| ≤ εcollar / 4 → χ v = 1) →
      tsupport χ ⊆ {v | |v.1| ≤ εcollar / 2} →
      (∀ j v, ‖iteratedFDeriv ℝ j χ v‖ ≤ Hcollar j) →
      ∀ ψ : f.centers → E → ℝ, (∀ p, ContDiff ℝ ∞ (ψ p)) →
      (∀ p, HasCompactSupport (ψ p)) → (∀ p y, ‖ψ p y‖ ≤ 1) →
      (∀ p (backward : Bool) y, y ∈ (if backward then tsupport (chartInputMask f p)
        else tsupport (endpointOutputMask f p output)) → ψ p y = 1) →
      (∀ p y, y ∈ closedBall 0 Rbase → ψ p y = 1) →
      ∃ (bSigned : ℕ → ((f.centers × Fin 3) ⊕ Unit) → Bool → ℕ)
        (Csigned : ℕ → ((f.centers × Fin 3) ⊕ Unit) → Bool → ℕ → ℝ),
        (∀ order letter backward q, 0 ≤ Csigned order letter backward q) ∧
    ∀ (Q : E → Fin (d+1) → Mat) (hQ : ContDiffOn ℝ ∞ Q Ω)
      (hQrange : MapsTo Q Ω (closedBall A₀ f.coefficientRadius))
      (hQlow : cNorm (closedBall x RQ) (sectorLowOrder d) Q ≤ M)
      (B : E → Mat) (hB : ContDiffOn ℝ ∞ B Ω)
      (hBlow : cNorm (closedBall x RQ) (sectorLowOrder d) B ≤ M),
    ∀ (Φ : f.centers → Z × ℝ → Z)
      (C : f.centers → OpenPartialHomeomorph TPoint TPoint)
      (G : f.centers → TPoint → ℝ)
      (Op : Fin 2 → f.centers → H →L[ℂ] H),
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
                cNorm (closedBall x RQ) (m+9) B)) →
    let W₁ := fun p ↦ selectedConicAmplitude f p Q B (Φ p) (C p) (angular p) 1
    ∀ order Rstar : ℕ, 10 ≤ Rstar → ∀ slowScale ρ : ℝ, 1 ≤ slowScale → slowScale ≤ ρ →
        (∀ j, cNorm (closedBall x RQ) j Q ≤ Aprofile j * slowScale ^ (j-Rstar)) →
        (∀ j, cNorm (closedBall x RQ) j B ≤ Aprofile j * slowScale ^ (j-Rstar)) →
      ∀ Gext : f.centers → TPoint → ℝ,
      (∀ p, ContDiffOn ℝ ∞ (Gext p) {q | q.2.2.2 ≠ 0}) →
      (∀ p, ∀ q ∈ ConicPhase.domain (f.chart p).radialSection
        (closedBall ((coordinateSplit (f.chart p).index x).1,
      ((coordinateSplit (f.chart p).index x).1,
        ((coordinateSplit (f.chart p).index x).2,
          (coordinateSplit (f.chart p).index p.val.val).2)))
      (2*(f.chart p).maskRadius)),
        (Gext p) =ᶠ[𝓝 q] ConicPhase.phase (f.chart p).radialSection (C p)) →
        ∀ (mInput mOutput : LocalizerSymbol (d+1)) (Ki Oi Ko Oo : Set (E × E)),
        IsBufferedLocalizer mInput Ki Oi → IsBufferedLocalizer mOutput Ko Oo →
        (∀ y ξ, mInput (y,-ξ) = mInput (y,ξ)) →
        (∀ y ξ, mOutput (y,-ξ) = mOutput (y,ξ)) →
        tsupport mInput ⊆ closedBall 0 Rbase ×ˢ frequencyAnnulus a₀ b₀ →
        tsupport mOutput ⊆ closedBall 0 Rbase ×ˢ frequencyAnnulus a₀ b₀ →
        (∀ j z, ‖iteratedFDeriv ℝ j mInput z‖ ≤ Hmask j) →
        (∀ j z, ‖iteratedFDeriv ℝ j mOutput z‖ ≤ Hmask j) →
        (∀ z ∈ tsupport mInput, closedBall z buffer ⊆ interior {z | mOutput z = 1}) →
        let mif := fun p ↦ canonicalProofLocalizer (coordinateSplit (f.chart p).index) mInput
        let mof := fun p ↦ canonicalProofLocalizer (coordinateSplit (f.chart p).index) mOutput
      (∀ p, ∀ (o : Bool) (ρ : ℝ), 0 < ρ → ∀ (u y : E) (r' : ℝ) (w : JointVariables E),
        r' ∈ Icc 0 (6*f.physicalRadius) → r' ≤ (f.chart p).maskRadius →
        w.1.1 0 ∈ closedBall (coordinateSplit (f.chart p).index x).1 ((f.chart p).maskRadius/2) →
        spatialPart w.1.1 ∈ closedBall (coordinateSplit (f.chart p).index x).2 ((f.chart p).maskRadius/2) →
        spatialPart w.2.1 ∈ ConicPhase.radialSectionBand (f.chart p).radialSection
      (coordinateSplit (f.chart p).index p.val.val).2 ((f.chart p).maskRadius/2) (ra p / thi) (ra p / tlo) →
        (y,w.2.2.1) ∈ cthickening (buffer/2) (tsupport (mif p)) →
        (u,w.2.2.2) ∈ tsupport (fun q ↦ 1-(mof p) q) →
        (δI ≤ phaseGradientSquare eI (jointElapsedPhase o
        (SymbolBudgets.normalizedTwoTimePhase ρ
          (curriedPhase (f.chart p).radialSection (C p))) u y) (r',w) ∧
      (r' ≤ εcollar → δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase o
        (SymbolBudgets.normalizedTwoTimePhase ρ
          (curriedPhase (f.chart p).radialSection (C p))) u y (r',w)) w)) ∧
        (δI ≤ phaseGradientSquare eI (jointElapsedPhase o
        (SymbolBudgets.normalizedTwoTimePhase ρ (fun t s u η ↦ (Gext p) (t,s,u,η))) u y) (r',w) ∧
      (r' ≤ εcollar → δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase o
        (SymbolBudgets.normalizedTwoTimePhase ρ (fun t s u η ↦ (Gext p) (t,s,u,η))) u y (r',w)) w))) →
        ∀ (letter : (f.centers × Fin 3) ⊕ Unit) (reflected backward : Bool),
        ∀ (hK : IsCompact K) (U : Set E) (hU : MeasurableSet U),
        tsupport μ ⊆ U → tsupport ν ⊆ U →
        ∀ R Lout : H →L[ℂ] H,
        (∀ u, R u =ᵐ[volume] fun y ↦ WithLp.toLp 2
          (rightLocalizer ρ mInput (fun z ↦ (u z).ofLp) y)) →
        (∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Lout u =ᵐ[volume]
          fun y ↦ WithLp.toLp 2 (leftLocalizer ρ mOutput (fun z ↦ (u z).ofLp) y)) →
        let P := measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
          (FiniteResidual.FiniteIdentity.selectedFullPhysicalResidualTerm f hK L Q B W₁
            output ho.continuous hob hib (Op 1) (letter, reflected))
        let S := if backward then P.adjoint else P
        ∀ accuracy (u : LocalL2 U (EuclideanSpace ℂ (Fin (d+1)))),
          let v := (1 - localRetardedOperator hU U Lout)
            (localRetardedOperator hU U S (localRetardedOperator hU U R u))
          v ∈ (restrictionSobolevScale U (EuclideanSpace ℂ (Fin (d+1))) hU).level order ∧
          (restrictionSobolevScale U (EuclideanSpace ℂ (Fin (d+1))) hU).gradeNorm order v ≤
            Csigned order letter backward accuracy * ρ ^ ((order : ℝ) + (3*(d+1) : ℕ)) *
              slowScale ^ bSigned order letter backward * (slowScale / ρ) ^ accuracy * ‖u‖ := by
  classical
  have hρb p := (hf p).1
  have hsrcρ p := (hf p).2.1
  have hretardedData := exists_retained_prescribed_measured_retarded_leakage_constants
    f hρb hsrcρ ra rb hra hrab amplitudeCost hamp Aprofile hAprofile
    μ ν hμ hν hμc hνc hμb hνb
  intro a₀ b₀ ha₀
  obtain ⟨tlo, thi, htlo, hthi, hretardedData⟩ := hretardedData a₀ b₀ ha₀
  refine ⟨tlo, thi, htlo, hthi, ?_⟩
  intro ι κ ιu ιz _ _ _ _ eT eI eu ez J hJ
    buffer Rbase εcollar δT δI Hmask Hcollar hbuffer hHmask hHcollar hε hδT hδI
    χ hχ hχone hχsupport hχder ψ hψ hψs hψb hψmask hψY
  have hretardedBound := fun order : ℕ ↦ hretardedData
    output ho hoc hout L hL eT eI eu ez J hJ
    buffer Rbase εcollar δT δI Hmask Hcollar hHmask hHcollar hε hδT hδI
    χ hχ hχone hχsupport hχder ψ hψ hψs hψb hψmask hψY order
  choose bLoss Cmq hCmq hretarded using hretardedBound
  obtain ⟨bPdo, Cpdo, hCpdo, hleakPdo⟩ :=
    exists_retained_prescribed_measured_threePDO_leakage_constants
      f hΩ hRQ.le hKΩ (selected_constant_complement_domain_of_supplied_collar f hf)
      L hL output ho hoc hout μ ν hμ hν hμc hνc hμb hνb
      hρb hsrcρ ra rb hcoverage amplitudeCost hamp halgebraic Aprofile hAprofile
      (b₀ := b₀) ha₀ Hmask hHmask eT eu ez J hJ Rbase ψ hψ hψs hψmask hψY hbuffer
  choose D hD hcompare using fun order ↦ exists_selectedSignedCharacteristic_local_leakage_comparison d order
  choose bElliptic Celliptic hCelliptic helliptic using fun order backward ↦
    exists_prescribed_measured_elliptic_leakage_constants f hKcompact hΩ hKΩ
      output ho hoc hout hob L hL μ ν hμ hν hμc hνc hμb hνb
      Aprofile Aprofile hAprofile hAprofile eT eu ez backward order
      ha₀ J hJ Rbase Hmask hHmask hbuffer
  let bCharacteristic := fun order p (branch : Fin 3) (backward : Bool) ↦
    ![bPdo order p 1 backward, bLoss order p, bPdo order p 2 backward] branch
  let Cbase := fun order p (branch : Fin 3) (backward : Bool) accuracy ↦
    ![Cpdo order p 1 backward accuracy, Cmq order p accuracy, Cpdo order p 2 backward accuracy] branch
  let Ccharacteristic := fun order p branch backward accuracy ↦
    D order * Cbase order p branch backward accuracy
  have hCbase order p branch backward accuracy : 0 ≤ Cbase order p branch backward accuracy := by
    fin_cases branch
    · exact hCpdo order p 1 backward accuracy
    · exact hCmq order p accuracy
    · exact hCpdo order p 2 backward accuracy
  let bSigned := fun order ↦ Sum.elim
    (fun pj : f.centers × Fin 3 ↦ bCharacteristic order pj.1 pj.2)
    (fun _ : Unit ↦ bElliptic order)
  let Csigned := fun order ↦ Sum.elim
    (fun pj : f.centers × Fin 3 ↦ Ccharacteristic order pj.1 pj.2)
    (fun _ : Unit ↦ Celliptic order)
  have hCsigned order letter backward accuracy : 0 ≤ Csigned order letter backward accuracy := by
    cases letter with
    | inl pj => exact mul_nonneg (hD order).le (hCbase order pj.1 pj.2 backward accuracy)
    | inr _ => exact hCelliptic order backward accuracy
  refine ⟨bSigned, Csigned, hCsigned, ?_⟩
  intro Q hQ hQrange hQlow B hB hBlow Φ C G Op hgeometry W₁
  choose hroot hhom hrootball hminor hproj hsource hinverse hbuffer'
    hphase hdiff hinvariants hstate hdiag' hnear hphaseCost houter hmaps
    hG hGdiag hGgerm hGres hcancellation hsourceeq
    hsolver hresidual hPW hendpoint hphysical hamplitudes using hgeometry
  have hpdo := hleakPdo Q hQ hQrange hQlow B hB hBlow Φ C angular
    (fun p ↦ (hamplitudes p 1).2.2.2.2.1)
    (fun p j m ↦ (hamplitudes p j).2.2.2.2.2.2.2.2 m)
    Rbox Dpdo Dgain Gain hendpoint hob
  intro order Rstar hRstar slowScale ρ hScale hScaleρ hQprofile hBprofile
    Gext hGext hGermExt mInput mOutput Ki Oi Ko Oo hmi hmo hei heo hmisupp hmosupp
    hmiJets hmoJets hdiag mif mof hshort letter reflected backward
    hK U hU hμU hνU R Lout hR hLout P S accuracy u v
  cases letter with
  | inr ell =>
    cases ell
    exact helliptic order backward Rstar (by omega) ρ slowScale hScale hScaleρ
      Q B hQ hB hQrange
      ((cNorm_mono_order (by have := (sectorLowOrder_bounds d).2.2; omega)).trans hQlow)
      ((cNorm_mono_order (by have := (sectorLowOrder_bounds d).2.2; omega)).trans hBlow)
      hQprofile hBprofile mInput mOutput Ki Oi Ko Oo hmi hmo hei heo hmisupp hmosupp
      hmiJets hmoJets hdiag R Lout hR hLout W₁ hib (Op 1) reflected accuracy U hU hμU hνU u
  | inl pj =>
    rcases pj with ⟨p, branch⟩
    have hρ : ρ ≠ 0 := (zero_lt_one.trans_le (hScale.trans hScaleρ)).ne'
    have hcani (p : f.centers) := ProtectedMasks.IsBufferedLocalizer.canonicalProofLocalizer
      (coordinateSplit (f.chart p).index) hmi
    have hcano (p : f.centers) := ProtectedMasks.IsBufferedLocalizer.canonicalProofLocalizer
      (coordinateSplit (f.chart p).index) hmo
    have hcanisupp (p : f.centers) := canonicalProofLocalizer_support_bounds (f.chart p).index hmisupp
    have hcanosupp (p : f.centers) := canonicalProofLocalizer_support_bounds (f.chart p).index hmosupp
    have hcaniJets (p : f.centers) (j : ℕ) (z : E × E) :
        ‖iteratedFDeriv ℝ j (mif p) z‖ ≤ Hmask j := by
      rw [norm_iteratedFDeriv_canonicalProofLocalizer]
      exact hmiJets j _
    have hcanoJets (p : f.centers) (j : ℕ) (z : E × E) :
        ‖iteratedFDeriv ℝ j (mof p) z‖ ≤ Hmask j := by
      rw [norm_iteratedFDeriv_canonicalProofLocalizer]
      exact hmoJets j _
    have hdiagCan (p : f.centers) : ∀ z ∈ tsupport (mif p),
        closedBall z buffer ⊆ interior {v | mof p v = 1} := by
      rw [tsupport_canonicalProofLocalizer]
      exact canonicalProofLocalizer_closedBall_plateau (f.chart p).index hdiag
    let mi := canonicalProofLocalizer (coordinateSplit (f.chart p).index) mInput
    let mo := canonicalProofLocalizer (coordinateSplit (f.chart p).index) mOutput
    obtain ⟨Ri', _, hRi⟩ := exists_bounded_physicalLocalizers (q := d+1) hρ mi
      (hcani p).smooth.continuous (hcani p).compactSupport
    obtain ⟨Li, hLi, _⟩ := exists_bounded_physicalLocalizers (q := d+1) hρ mo
      (hcano p).smooth.continuous (hcano p).compactSupport
    let Ri := Ri'.adjoint
    have hRcov : physicalOperator (f.chart p).index Ri = R :=
      physicalOperator_rightLocalizer (f.chart p).index ρ mInput R Ri hR hRi
    have hLcov : physicalOperator (f.chart p).index Li = Lout :=
      physicalOperator_leftLocalizer (f.chart p).index ρ mOutput Lout Li hLout hLi
    have hRreal := boundedRightLocalizer_star_of_even ρ mInput hei R hR
    have hLreal := boundedLeftLocalizer_star_of_even hρ mOutput
      hmo.smooth.continuous hmo.compactSupport heo Lout hLout
    let Bleak := Cbase order p branch backward accuracy * ρ ^ ((order : ℝ) + (3*(d+1) : ℕ)) *
      slowScale ^ bCharacteristic order p branch backward * (slowScale / ρ) ^ accuracy
    have hBleak : 0 ≤ Bleak := by
      have := hCbase order p branch backward accuracy
      have hρpos : 0 < ρ := zero_lt_one.trans_le (hScale.trans hScaleρ)
      have hScalePos : 0 < slowScale := zero_lt_one.trans_le hScale
      dsimp only [Bleak]
      positivity
    have hlocal := hcompare order f hK L Q B W₁
      output ho.continuous hob hib (Op 1) p branch reflected backward U hU
      μ ν hμ.continuous hν.continuous hμb hνb hμU hνU R Lout Ri Li hRcov hLcov
      hRreal hLreal Bleak hBleak
    have hb := hlocal (by
      fin_cases branch
      · exact hpdo order Rstar hRstar slowScale ρ hScale hScaleρ hQprofile hBprofile
          mif mof _ _ (fun p ↦ (hcani p).smooth) (fun p ↦ (hcani p).compactSupport)
          (fun p ↦ (hcani p).range) hcano hdiagCan hcanisupp hcanosupp hcaniJets hcanoJets
          p 1 backward Ri Li hRi hLi accuracy
      · exact hretarded order Rstar hRstar slowScale ρ hScale (hScale.trans hScaleρ)
          Q B hQprofile hBprofile Φ C angular
          hphase hbuffer' hdiff hnear hphaseCost (fun p ↦ (hangular p).2)
          (fun p ↦ (hangular p).1) hplateau
          (fun p j ↦ (hamplitudes p j).1) (fun p j ↦ (hamplitudes p j).2.2.2.2.1)
          (fun p ↦ (hamplitudes p 2).2.2.2.1)
          (fun p j ↦ (hamplitudes p j).2.2.2.2.2.1)
          hphysical (fun p q hq ↦ (hinvariants p q hq).2.1)
          (fun p j m ↦ (hamplitudes p j).2.2.2.2.2.2.2.2 m)
          G χout χsource hs (base 1) (cost 1) (Op 1) hG hGgerm hGres hPW
          hob hib houtMask hsourceMask
          Gext hGext hGermExt mif mof (fun p ↦ (hcani p).smooth) (fun p ↦ (hcano p).smooth)
          (fun p ↦ (hcani p).compactSupport) (fun p ↦ (hcano p).compactSupport)
          (fun p ↦ (hcani p).range) (fun p ↦ (hcano p).range)
          hcanisupp hcanosupp hcaniJets hcanoJets hshort p Ri Li hRi hLi accuracy backward
      · exact hpdo order Rstar hRstar slowScale ρ hScale hScaleρ hQprofile hBprofile
          mif mof _ _ (fun p ↦ (hcani p).smooth) (fun p ↦ (hcani p).compactSupport)
          (fun p ↦ (hcani p).range) hcano hdiagCan hcanisupp hcanosupp hcaniJets hcanoJets
          p 2 backward Ri Li hRi hLi accuracy) u
    refine ⟨hb.1, hb.2.trans_eq ?_⟩
    simp only [Bleak, Csigned, bSigned, Sum.elim_inl, Ccharacteristic]
    ring

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
