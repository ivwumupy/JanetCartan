module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.PhysicalMasks
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.SupportedBudgets
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.CoordinateSobolev

/-!
# Actual algebraic PDOs on the finite physical family

Instantiate the two algebraic symbol budgets with the retained inverse, the
selected spatial collar and the original common physical masks. Constants
precede the original coefficient fields and all radial enlargements. Coordinate
transport gives the literal physical operators and adjoints. The retarded
family and complement equation are retained on the same selected charts.

This closes indices zero and three of `directPDOSymbols`; the endpoint and
source PDOs, complete differential identity and finite real solver remain
separate obligations of `app:ch_regular_base:thm:sector`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
open Set Metric Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAlgebraic
open ActualCarriers Characteristic Characteristic.AlgebraicChart
open Characteristic.RootFamily Characteristic.ResidualCoordinates
open Characteristic.AlgebraicSymbols Characteristic.EvolutionIntegral Characteristic.PdoRealization
open Characteristic.AmplitudeBounds FiniteMasks FiniteMasks.ActualFamily FiniteEvolution
open JanetCartan.CharacteristicTransport.CompleteResidual
open AmplitudeBound FourierIntegral Pseudodifferential
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "H" => SpacetimeL2 d (d+1)
local notation "Coeff" => Fin (d+1) → Mat

/-- Construct the finite physical family and instantiate BOTH algebraic PDO
terms, including their literal adjoints, from the original coefficient
neighborhood. No inverse estimate, symbol estimate or operator estimate is
assumed. The common finite low order is `sectorLowOrder d`; the algebraic
high reserve remains `2*(d+2)+2`. Retain the same root, complement equation,
retarded charts and all physical/angular/low masks for the final assembly.
Sources: `complement-symbol`, `energy-complete-residual`, `measured-adjoint`. -/
theorem exists_finite_physical_algebraic_pdos
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (A₀ : Coeff) {K : Set E} (hK : IsCompact K)
    (hKzero : (0 : E) ∉ K)
    (hregular : ∀ ξ ∈ K, determinant A₀ ξ = 0 → fderiv ℝ (determinant A₀) ξ ≠ 0)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ f : ActualMaskFamily Ω x RQ A₀ K M,
      (∀ p : f.centers, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
        (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4) ∧
      (∀ p : f.centers, SelectedChartPhysicalEvolution (f.chart p) (f.angularMask p)
        ((physicalCoordinates (f.chart p).index).symm '' tsupport f.inputMask)
        ((physicalCoordinates (f.chart p).index) ⁻¹' Ω)) ∧
      ∀ p : f.centers,
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
                      (1 + high) * vectorFourierSobolevNorm (-((n : ℝ)+1)) u) := by
  classical
  obtain ⟨f, hradii, hevolution, hinverse⟩ :=
    exists_finite_physical_evolution_and_algebraic_inverse hΩ x hRQ hKΩ A₀ hK hKzero hregular hM
  refine ⟨f, hradii, hevolution, ?_⟩
  intro p c
  obtain ⟨hc, hsource, ε, hε, inverseCost, hcost, hactual⟩ := hinverse p
  obtain ⟨ho, hs, hco, hcs, hcarrier⟩ := chartPhysicalMasks_properties f p
  obtain ⟨hρ, hsρ, hρrange⟩ := chartConicMask_properties f p
  obtain ⟨Rbox, hRbox, C, Mbound, hMbound, hC, hbudgets⟩ :=
    exists_selected_algebraicSymbols_supported_budgets f p hΩ hRQ hKΩ hc hsource
      _ hρ hsρ hρrange _ _ ho hs hco hcs hcarrier M hM inverseCost hcost
  obtain ⟨D, G, hD, hG, hgain⟩ :=
    exists_selected_algebraicSymbols_integer_gain_constants f p hΩ hRQ hKΩ hc hsource
      _ hρ hsρ hρrange _ _ ho hs hco hcs hcarrier M hM inverseCost hcost
  refine ⟨hc, hsource, ε, hε, Rbox, hRbox, Mbound, hMbound, C, D, G, hC, hD, hG, ?_⟩
  intro L hL Q B hQ hB hQrange hQlow hBlow h β U b pb
  obtain ⟨hspectral, hh, hroot, hdom, _, hinv⟩ := hactual L hL Q hQ hQrange
  have hinv' ζ (hζ : ζ ∈ tsupport β) := (hinv ζ hζ).2
  have horder : 2 * (d+2) + 2 ≤ sectorLowOrder d := by
    have := (sectorLowOrder_bounds d).2.2
    omega
  have hq := (cNorm_mono_order horder).trans hQlow
  have hb := (cNorm_mono_order horder).trans hBlow
  have hsymbols := hbudgets L Q B hQ hB hQrange hq hb hdom hinv'
  have hoperators := hgain L Q B hQ hB hQrange hq hb hdom hinv'
  refine ⟨hspectral, hh, hroot, hdom, fun ζ hζ ↦ (hinv ζ hζ).1, ?_⟩
  intro s hsymbol
  have hsymbolData := hsymbols s hsymbol
  refine ⟨hsymbolData.1, hsymbolData.2.1, hsymbolData.2.2.2, ?_⟩
  intro n T high
  have hforward (u : H) (hu : MemVectorFourierSobolev (n : ℝ) u) := physicalOperator_sobolev_bound c.index
    (maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p) s)
    (n : ℝ) ((n : ℝ)+1) ((d+1 : ℝ) * (d+1) * G n) high
    (fun v hv ↦ (hoperators s hsymbol n v hv).1) u hu
  have hadjoint (u : H) (hu : MemVectorFourierSobolev (n : ℝ) u) := physicalOperator_sobolev_bound c.index
    (maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p) s).adjoint
    (n : ℝ) ((n : ℝ)+1) ((d+1 : ℝ) * (d+1) * G n) high
    (fun v hv ↦ (hoperators s hsymbol n v hv).2) u hu
  have hadjoint' (u : H) (hu : MemVectorFourierSobolev (n : ℝ) u) :
      MemVectorFourierSobolev ((n : ℝ)+1) (T.adjoint u) ∧
      vectorFourierSobolevNorm ((n : ℝ)+1) (T.adjoint u) ≤
        ((d+1 : ℝ) * (d+1) * G n) *
          (vectorFourierSobolevNorm (n : ℝ) u + high * ‖u‖) := by
    simpa only [T, physicalOperator_adjoint] using hadjoint u hu
  refine ⟨fun u hu ↦ ⟨hforward u hu, hadjoint' u hu⟩, ?_⟩
  intro u
  have hconstant : 0 ≤ (d+1 : ℝ) * (d+1) * G n :=
    mul_nonneg (by positivity) (hG n)
  have hhigh : 0 ≤ high := by
    apply mul_nonneg (zero_le_one.trans (hD _))
    linarith [cNorm_nonneg (closedBall x RQ) (n + (2 * (d+2) + 2)) Q,
      cNorm_nonneg (closedBall x RQ) (n + (2 * (d+2) + 2)) B]
  have hnegative := negativeVectorFourierSobolev_tame_bound_of_adjoint
    (t := (n : ℝ)+1) (Nat.cast_nonneg n) (by positivity) hconstant hhigh T hadjoint' u
  have hnegativeAdjoint := negativeVectorFourierSobolev_tame_bound_of_adjoint
    (t := (n : ℝ)+1) (Nat.cast_nonneg n) (by positivity) hconstant hhigh T.adjoint
    (fun v hv ↦ by simpa only [ContinuousLinearMap.adjoint_adjoint] using hforward v hv) u
  simpa only [Nat.cast_add, Nat.cast_one] using And.intro hnegative hnegativeAdjoint

end JanetCartan.RegularSector.FiniteAlgebraic
