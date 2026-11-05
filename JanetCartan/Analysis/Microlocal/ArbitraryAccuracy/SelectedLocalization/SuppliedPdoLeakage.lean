module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.MeasuredPdoLeakage
public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Estimates

/-!
# PDO leakage on the retained normalized inverse

The normalized inverse already fixes its coefficient family, characteristic
charts, complete amplitudes and physical masks. This module applies the selected
symbol and regularization estimates to those witnesses. No operator family is
selected again, and the leakage constants precede coefficients, proof masks and
accuracy.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 256
set_option maxRecDepth 4096
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteAssembly
open Characteristic Characteristic.ResidualCoordinates Characteristic.RootFamily
open Characteristic.ConicAmplitude Characteristic.ConicPhase
open Characteristic.AmplitudeBounds
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.SymbolBudgets
open Characteristic.PdoRealization Characteristic.AlgebraicSymbols
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic FinitePdo FiniteEvolution
open FinitePdo.RetainedConstruction
open ActualCarriers Characteristic.AlgebraicChart
open FourierIntegral FourierIntegral.LowBounds Pseudodifferential AmplitudeBound
open FourierIntegral.LowBounds.FrequencyCutoff
open JanetCartan.CharacteristicTransport.CompleteResidual
open FiniteChain.Graph FiniteChain.Graph.KernelLimits FiniteChain.Graph.PhysicalShells
open FiniteChain.Graph.KernelEstimates.NoncomparableGeometry
open EvolutionIntegratedLocalization
universe uI uU uZ
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "TPoint" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)
local notation "Coeff" => Fin (d+1) → Mat
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "H" => SpacetimeL2 d (d+1)

/-- The three measured PDO residuals of the supplied normalized inverse have
prescribed-mask Fourier leakage, with constants before the current coefficients,
charts, proof masks and accuracy. The algebraic and endpoint certificates are
the retained outputs of
`exists_normalized_complete_smooth_fixed_inverse_of_selected_collar_on_enlarged_bands`.
The complement-domain input is produced by
`selected_constant_complement_domain_of_supplied_collar`. Normal-amplitude bounds
are instantiated on the literal symbols at the original
doubled threshold. The full zeroth-order coefficient, both measurement masks,
and both literal orientations are retained.

Consumer: the PDO part of the same-inverse complete signed residual leakage in
`NormalizedResidualWords.ObservedChains.measuredResidual_hchain_of_individual_estimates`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`, and
`app:ch_regular_base:eq:measured-adjoint`). -/
theorem exists_retained_prescribed_measured_threePDO_leakage_constants
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hΩ : IsOpen Ω) (hRQ : 0 ≤ RQ) (hball : closedBall x RQ ⊆ Ω)
    (hdom : ∀ p : f.centers, ∀ A' : Coeff, A' ∈ closedBall A₀ f.coefficientRadius →
      let c := f.chart p
      (physicalCoordinates c.index ⁻¹' Ω) ×ˢ
        (normalizeCovector c.radialSection '' tsupport
          (selectedEndpointMultiplier f p f.radialThreshold)) ⊆
        complementDomain c.index (fun _ : E ↦ A')
          (fieldRoot (coordinateSplit c.index) (fun _ : E ↦ A') c.root) c.row c.col
          (normalizedRootDomain c))
    (threshold : ℝ) (hthreshold : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hout : tsupport output ⊆ ball x f.physicalRadius)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (hchartBuffer : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hmask : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    (ra rb : f.centers → ℝ)
    (hcoverage : ∀ p, DiagonalFrequencyCoverage (f.chart p).radialSection
      (coordinateSplit (f.chart p).index p.val.val).2 ((f.chart p).bufferRadius/2)
      (ra p) (rb p) (selectedEndpointMultiplier f p threshold))
    (amplitudeCost : f.centers → ℕ → ℝ) (hamp : ∀ p m, 0 < amplitudeCost p m)
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
                      (1 + high) * vectorFourierSobolevNorm (-((n : ℝ)+1)) u))
    (Aprofile : ℕ → ℝ) (hAprofile : ∀ k, 0 ≤ Aprofile k)
    {a₀ b₀ : ℝ} (ha₀ : 0 < a₀)
    (Hmask : ℕ → ℝ) (hHmask : ∀ k, 0 ≤ Hmask k)
    {ι : Type uI} {ιu : Type uU} {ιz : Type uZ} [Fintype ι] [Fintype ιu] [Fintype ιz]
    (eT : Module.Basis ι ℝ (JointVariables E))
    (eu : OrthonormalBasis ιu ℝ E) (ez : OrthonormalBasis ιz ℝ E)
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (hJ : MeasurePreserving (graphInputCoordinates J) volume volume)
    (Rbase : ℝ) (ψ : f.centers → E → ℝ)
    (hψ : ∀ p, ContDiff ℝ ∞ (ψ p)) (hψs : ∀ p, HasCompactSupport (ψ p))
    (hψmask : ∀ p (backward : Bool) y,
      y ∈ (if backward then tsupport (chartInputMask f p)
        else tsupport (endpointOutputMask f p output)) → ψ p y = 1)
    (hψY : ∀ p y, y ∈ closedBall 0 Rbase → ψ p y = 1)
    {buffer : ℝ} (hbuffer : 0 < buffer) :
    ∃ (bPdo : ℕ → f.centers → Fin 3 → Bool → ℕ)
      (Cpdo : ℕ → f.centers → Fin 3 → Bool → ℕ → ℝ),
      (∀ order p j backward q, 0 ≤ Cpdo order p j backward q) ∧
    ∀ (Q : E → Coeff) (hQ : ContDiffOn ℝ ∞ Q Ω)
      (hQrange : MapsTo Q Ω (closedBall A₀ f.coefficientRadius))
      (hQlow : cNorm (closedBall x RQ) (sectorLowOrder d) Q ≤ M)
      (B : E → Mat) (hB : ContDiffOn ℝ ∞ B Ω)
      (hBlow : cNorm (closedBall x RQ) (sectorLowOrder d) B ≤ M)
      (Φ : f.centers → Z × ℝ → Z)
      (Cchart : f.centers → OpenPartialHomeomorph TPoint TPoint)
      (angular : f.centers → Euclidean d → ℝ),
    let z := fun p : f.centers ↦
      let e := coordinateSplit (f.chart p).index
      ((e x).1, ((e x).2, (e p.val.val).2))
    let Fs := fun p ↦ selectedBufferedAmplitude f p Q B (Φ p) (Cchart p)
    let W := fun p ↦ selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p)
    (∀ p, ContDiff ℝ ∞
      (collared (f.chart p).radialSection 1 (angular p) (Fs p 1))) →
    (∀ p j m, BoundedTwoTimeOrderSeminorm (if j=0 then 0 else 1)
        (bufferedJetSet (f.chart p).radialSection (z p) ((f.chart p).bufferRadius/2)
          (ra p) (rb p)) m (W p j) ∧
      twoTimeOrderSeminorm (if j=0 then 0 else 1)
        (bufferedJetSet (f.chart p).radialSection (z p) ((f.chart p).bufferRadius/2)
          (ra p) (rb p)) m (W p j) ≤
        amplitudeCost p m * (1+cNorm (closedBall x RQ) (m+10) Q+
          cNorm (closedBall x RQ) (m+9) B)) →
    ∀ (Rbox : f.centers → ℝ) (Dpdo Dgain Gain : f.centers → ℕ → ℝ),
    (∀ p, EndpointPdoEstimates (f.chart p).index (closedBall x RQ) Q B
      (endpointOutputMask f p output) (FiniteAlgebraic.chartInputMask f p)
      (selectedEndpointSymbol f p threshold Q (W p 1)) (Rbox p) M
      (Dpdo p) (Dgain p) (Gain p)) →
    (∀ y, ‖output y‖ ≤ 1) →
    ∀ order Rstar : ℕ, 10 ≤ Rstar → ∀ slowScale ρ : ℝ, 1 ≤ slowScale → slowScale ≤ ρ →
      (∀ j, cNorm (closedBall x RQ) j Q ≤ Aprofile j * slowScale ^ (j-Rstar)) →
      (∀ j, cNorm (closedBall x RQ) j B ≤ Aprofile j * slowScale ^ (j-Rstar)) →
      ∀ (mif mof : f.centers → LocalizerSymbol (d+1))
        (Ko Oo : f.centers → Set (E × E)),
      (∀ p, ContDiff ℝ ∞ (mif p)) → (∀ p, HasCompactSupport (mif p)) →
      (∀ p z, mif p z ∈ Icc (0 : ℝ) 1) →
      (∀ p, IsBufferedLocalizer (mof p) (Ko p) (Oo p)) →
      (∀ p, ∀ z ∈ tsupport (mif p), closedBall z buffer ⊆ interior {z | mof p z = 1}) →
      (∀ p, tsupport (mif p) ⊆ closedBall 0 Rbase ×ˢ frequencyAnnulus a₀ b₀) →
      (∀ p, tsupport (mof p) ⊆ closedBall 0 Rbase ×ˢ frequencyAnnulus a₀ b₀) →
      (∀ p j z, ‖iteratedFDeriv ℝ j (mif p) z‖ ≤ Hmask j) →
      (∀ p j z, ‖iteratedFDeriv ℝ j (mof p) z‖ ≤ Hmask j) →
      ∀ (p : f.centers) (branch : Fin 3) (backward : Bool),
      let mi := mif p
      let mo := mof p
      let P := measuredOperator
        (μ ∘ physicalCoordinates (f.chart p).index) (ν ∘ physicalCoordinates (f.chart p).index)
        (hμ.continuous.comp (physicalCoordinates (f.chart p).index).continuous)
        (hν.continuous.comp (physicalCoordinates (f.chart p).index).continuous)
        (fun y ↦ hμb _) (fun y ↦ hνb _)
        (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
          (![selectedSourceSymbol f p (2*threshold),
            selectedEndpointSymbol f p threshold Q (W p 1),
            selectedAlgebraicSymbol f p (2*threshold) Q B 1] branch))
      let Top := if backward then P.adjoint else P
      ∀ Mi Mo : H →L[ℂ] H,
      (∀ u, Mi u =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (rightLocalizer ρ mi (fun z ↦ (u z).ofLp) y)) →
      (∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
        fun y ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun z ↦ (u z).ofLp) y)) →
      ∀ accuracy u,
      MemVectorFourierSobolev (order : ℝ) ((1 - Mo) (Top (Mi u))) ∧
      vectorFourierSobolevNorm (order : ℝ) ((1 - Mo) (Top (Mi u))) ≤
        Cpdo order p branch backward accuracy * ρ ^ ((order : ℝ) + (3 * (d+1) : ℕ)) *
          slowScale ^ bPdo order p branch backward * (slowScale / ρ) ^ accuracy * ‖u‖ := by
  classical
  have hψplateau (p : f.centers) (backward : Bool) (y : E)
      (hy : y ∈ leakageOutputCarrier backward
        (tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p))
        (closedBall 0 Rbase)) : ψ p y = 1 := by
    rcases hy with hy | hy
    · apply hψmask p backward y
      cases backward with
      | false => obtain ⟨v, hv, rfl⟩ := hy; exact hv.1
      | true => obtain ⟨v, hv, rfl⟩ := hy; exact hv.2
    · exact hψY p y hy
  have hpdoBound := fun order : ℕ ↦
    exists_selected_measured_threePDO_fourier_leakage_constants
      f hΩ hRQ hball (fun p ↦ (halgebraic p).1) hdom
      threshold (f.radialThreshold_ge_one.trans hthreshold) hthreshold output ho hoc hout
      μ ν hμ hν hμc hνc hμb hνb hchartBuffer hmask ra rb hcoverage amplitudeCost hamp
      Aprofile hAprofile (b := b₀) ha₀ Hmask hHmask eT eu ez J hJ
      (fun _ ↦ closedBall 0 Rbase) (fun _ ↦ isCompact_closedBall 0 Rbase)
      ψ hψ hψs hψplateau hbuffer order
  choose bPdo Cpdo hCpdo hleakPdo using hpdoBound
  refine ⟨bPdo, Cpdo, hCpdo, ?_⟩
  intro Q hQ hQrange hQlow B hB hBlow Φ Cchart angular z Fs W hsmooth hamplitudes
    Rbox Dpdo Dgain Gain hendpoint hob order Rstar hRstar slowScale ρ hScale hScaleρ
    hQprofile hBprofile mif mof Ko Oo hmi hmic hmirange hmo hdiag hmisupp hmosupp
    hmiJets hmoJets p branch backward mi mo P Top Mi Mo hMi hMo accuracy u
  have hbasei (p : f.centers) : Prod.fst '' tsupport (mif p) ⊆ closedBall 0 Rbase := by
    rintro _ ⟨v, hv, rfl⟩
    exact (hmisupp p hv).1
  have hbaseo (p : f.centers) : Prod.fst '' tsupport (mof p) ⊆ closedBall 0 Rbase := by
    rintro _ ⟨v, hv, rfl⟩
    exact (hmosupp p hv).1
  have hnormal (p : f.centers) : ∃ Ralg Malg : ℝ,
      ∀ o : Fin 2, GraphNormalAmplitudeBounds
        (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
          (selectedAlgebraicSymbol f p (2*threshold) Q B o)) Ralg Malg := by
    obtain ⟨_, _, ε, _, Ralg, _, Malg, _, Calg, Dalg, Galg, _, _, _, hactual⟩ := halgebraic p
    have htwo : f.radialThreshold ≤ 2*threshold := by
      linarith [f.radialThreshold_ge_one]
    have hlocal := hactual (2*threshold) htwo Q B hQ hB hQrange hQlow hBlow
    exact ⟨Ralg, Malg, fun o ↦ (hlocal.2.2.2.2.2
      (selectedAlgebraicSymbol f p (2*threshold) Q B o)
      (by fin_cases o <;> simp [selectedAlgebraicSymbol])).2.1⟩
  choose Ralg Malg hnormal using hnormal
  exact hleakPdo order mif mof Ko Oo hmi hmic hmirange hmo hdiag
    (fun p v hv ↦ (hmisupp p hv).2) hbasei hbaseo hmiJets hmoJets
    Rstar hRstar slowScale ρ hScale hScaleρ Q B hQ hB hQrange hQprofile hBprofile
    Φ Cchart angular
    (fun p ↦ (hsmooth p).comp evolutionToCharacteristicPoint.contDiff)
    hamplitudes hob (fun _ ↦ Ralg) (fun _ ↦ Malg) Rbox
    (fun p ↦ Dpdo p (2*(d+2)+1) * (1+M+M))
    (fun o p ↦ hnormal p o) (fun p ↦ (hendpoint p).1)
    p branch backward Mi Mo hMi hMo accuracy u

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
