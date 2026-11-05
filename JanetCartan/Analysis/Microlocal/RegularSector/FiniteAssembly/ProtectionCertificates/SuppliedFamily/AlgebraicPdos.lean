module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.ProtectionCertificates.SuppliedFamily.InverseBounds

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.PhysicalMasks
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.SupportedBudgets
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.CoordinateSobolev

/-!
# Physical algebraic PDO estimates on a supplied finite family

The conic inverse, supported symbols and their literal adjoints use the supplied
protected family and its original masks.
Consumer: `exists_finite_algebraic_pdo_sums_of_selected_collar`.
Sources: `app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`
and `app:ch_regular:eq:chain-tail` in `paper.tex`.
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

/-- Retain a supplied finite family through the physical algebraic PDO estimates.
`hf` is exactly the original selector's collar conclusion, also retained as the
first projection of `exists_actualMaskFamily_with_stationary_source_radii`.
No new family, reference, masks or radial threshold is selected. Constants
precede the varying coefficients and radial enlargement. Consumer: the
supplied-family continuation of
`exists_finite_protected_direct_operator_bounds_and_equations`.
Sources: `app:ch_regular_base:thm:sector`, `complement-symbol`,
`sector-theorem-residual`, `measured-adjoint`, `energy-complete-residual`. -/
theorem exists_finite_physical_algebraic_pdos_of_selected_collar
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
  obtain ⟨evolutionTime, speedGap, rootSize, rootCost, hprotection, hradii, hevolution, hinverse⟩ :=
    exists_finite_physical_evolution_and_algebraic_inverse_of_selected_collar hΩ x hRQ hKΩ A₀ hM f hf
  refine ⟨evolutionTime, speedGap, rootSize, rootCost, hprotection, hradii, hevolution, ?_⟩
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
