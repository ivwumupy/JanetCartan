module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.SuppliedResidualCosts.Algebraic

/-!
# Both actual algebraic coordinate certificates for the PDO tail

Extract both literal entries of the algebraic clause already retained by the
supplied fixed inverse. The source product, doubled threshold, coefficient
fields and chart masks are exactly those of the original construction.
Consumer: `exists_selected_algebraic_tail_symbol_profiles` in
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication
open RegularSector RegularSector.FiniteAssembly
open ActualCarriers Characteristic Characteristic.AlgebraicChart
open Characteristic.RootFamily Characteristic.ResidualCoordinates
open Characteristic.AlgebraicSymbols Characteristic.EvolutionIntegral Characteristic.PdoRealization
open Characteristic.AmplitudeBounds FiniteMasks FiniteMasks.ActualFamily FiniteEvolution FiniteAlgebraic
open JanetCartan.CharacteristicTransport.CompleteResidual
open AmplitudeBound FourierIntegral Pseudodifferential
variable {d : ℕ}
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
local notation "H" => SpacetimeL2 d (d+1)

/-- The actual retained algebraic construction supplies the normal and
ordered coordinate certificates for BOTH the solver inverse and its complete
physical residual, before varying the radial threshold or coefficient fields.
This is the precise primitive producer for the full-frequency tail-symbol
application; no tail or Fréchet-profile hypothesis is inserted
(`app:ch_regular_base:eq:energy-complete-residual`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_supplied_algebraic_tail_coordinate_certificates
    (f : ActualMaskFamily Ω x RQ A₀ K M)
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
    ∃ (Ralg Malg : f.centers → ℝ) (Calg : f.centers → ℕ → ℝ),
      (∀ p, 0 < Ralg p) ∧ (∀ p, 0 < Malg p) ∧ (∀ p m, 0 < Calg p m) ∧
      ∀ L ≥ f.radialThreshold, ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) (sectorLowOrder d) Q ≤ M →
        cNorm (closedBall x RQ) (sectorLowOrder d) B ≤ M →
        ∀ (p : f.centers) (o : Fin 2),
          GraphNormalAmplitudeBounds
            (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
              (selectedAlgebraicSymbol f p (2*L) Q B o)) (Ralg p) (Malg p) ∧
          ∀ m ξ is, is.length ≤ m → ∀ z,
            (1+‖ξ‖)*‖matrixAmplitudeCoordinateDerivList is
              (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
                (selectedAlgebraicSymbol f p (2*L) Q B o) ξ) z‖ ≤
              Calg p m*(1+cNorm (closedBall x RQ) (m+1) Q+
                cNorm (closedBall x RQ) (m+1) B) := by
  classical
  choose hroot hsource ε hε Ralg hRalg Malg hMalg Calg Dalg Galg
    hCalg hDalg hGalg hlocal using halgebraic
  refine ⟨Ralg, Malg, Calg, hRalg, hMalg, hCalg, ?_⟩
  intro L hL Q B hQ hB hmap hQl hBl p o
  have hLtwo : f.radialThreshold ≤ 2*L := by
    linarith only [f.radialThreshold_ge_one, hL]
  have ha := hlocal p (2*L) hLtwo Q B hQ hB hmap hQl hBl
  have hb := ha.2.2.2.2.2 (selectedAlgebraicSymbol f p (2*L) Q B o)
    (by fin_cases o <;> simp [selectedAlgebraicSymbol])
  exact ⟨hb.2.1, hb.2.2.1⟩

end JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication
