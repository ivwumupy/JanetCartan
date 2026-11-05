module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.AlgebraicSums

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.ProtectionCertificates.SuppliedFamily.AlgebraicPdos

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.Construction

/-!
# Finite algebraic sums on the supplied protected family

The supported algebraic operators and their literal finite sums use the same
local root, masks and protection certificates.
Consumer: `exists_finite_protected_direct_operator_bounds_and_equations_of_selected_collar`.
Sources: `app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`
and `app:ch_regular:eq:chain-tail` in `paper.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
open Set Metric Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAssembly
open ActualCarriers Characteristic Characteristic.AlgebraicChart
open Characteristic.RootFamily Characteristic.ResidualCoordinates
open Characteristic.AlgebraicSymbols Characteristic.EvolutionIntegral Characteristic.PdoRealization
open Characteristic.AmplitudeBounds FiniteMasks FiniteMasks.ActualFamily FiniteEvolution FiniteAlgebraic
open JanetCartan.CharacteristicTransport.CompleteResidual
open AmplitudeBound FourierIntegral Pseudodifferential
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "H" => SpacetimeL2 d (d+1)
local notation "Coeff" => Fin (d+1) → Mat

/-- Retain a supplied finite family through the literal finite algebraic sums.
`hf` is exactly the original selector's collar conclusion, also retained as the
first projection of `exists_actualMaskFamily_with_stationary_source_radii`.
No new family, reference, masks or radial threshold is selected. Constants
precede the varying coefficients and radial enlargement. Consumer: the
supplied-family continuation of
`exists_finite_protected_direct_operator_bounds_and_equations`.
Sources: `app:ch_regular_base:thm:sector`, `complement-symbol`,
`sector-theorem-residual`, `measured-adjoint`, `energy-complete-residual`. -/
theorem exists_finite_algebraic_pdo_sums_of_selected_collar
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
    ∃ cost : ℕ → ℝ, (∀ n, 0 ≤ cost n) ∧
    ∀ L ≥ f.radialThreshold, ∀ (Q : E → Coeff) (B : E → Mat),
      ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
      MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
      cNorm (closedBall x RQ) (sectorLowOrder d) Q ≤ M →
      cNorm (closedBall x RQ) (sectorLowOrder d) B ≤ M →
      ∀ (o : Fin 2) (n : ℕ),
        let T := selectedFiniteAlgebraicPDO f L Q B o
        let high := 1+cNorm (closedBall x RQ) (n+sectorLowOrder d) Q+
          cNorm (closedBall x RQ) (n+sectorLowOrder d) B
        (∀ V : H →L[ℂ] H, (V = T ∨ V = T.adjoint) → ∀ u,
          MemVectorFourierSobolev (n : ℝ) u →
          MemVectorFourierSobolev ((n : ℝ)+1) (V u) ∧
          vectorFourierSobolevNorm ((n : ℝ)+1) (V u) ≤
            cost n * (vectorFourierSobolevNorm (n : ℝ) u+high*‖u‖)) ∧
        (∀ V : H →L[ℂ] H, (V = T ∨ V = T.adjoint) → ∀ u,
          MemVectorFourierSobolev (-(n : ℝ)) (V u) ∧
          vectorFourierSobolevNorm (-(n : ℝ)) (V u) ≤
            ((d+1 : ℝ)*(d+1)*cost n)*(1+high)*
              vectorFourierSobolevNorm (-((n : ℝ)+1)) u) := by
  classical
  obtain ⟨evolutionTime, speedGap, rootSize, rootCost, hprotection, hradii, hevolution, hlocal⟩ :=
    exists_finite_physical_algebraic_pdos_of_selected_collar hΩ x hRQ hKΩ A₀ hM f hf
  have hlocalKeep := hlocal
  choose hroot hsource ε hε Rbox hRbox Mbound hMbound C D G hC hD hG hactual using hlocal
  let cost n := ∑ p : f.centers, ((d+1 : ℝ)*(d+1)*G p n)*D p (2*(d+2)+(n+1))
  have hcost n : 0 ≤ cost n := Finset.sum_nonneg fun p _ ↦
    mul_nonneg (mul_nonneg (by positivity) (hG p n)) (zero_le_one.trans (hD p _))
  refine ⟨evolutionTime, speedGap, rootSize, rootCost, hprotection, hradii, hevolution, hlocalKeep, cost, hcost, ?_⟩
  intro L hL Q B hQ hB hQrange hQlow hBlow o n T high
  let chartOp p := maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p)
    (selectedAlgebraicSymbol f p L Q B o)
  have hhigh : 0 ≤ high := by
    dsimp [high]
    linarith [cNorm_nonneg (closedBall x RQ) (n+sectorLowOrder d) Q,
      cNorm_nonneg (closedBall x RQ) (n+sectorLowOrder d) B]
  have hlocalBound p (V : H →L[ℂ] H)
      (hV : V = physicalOperator (f.chart p).index (chartOp p) ∨
        V = (physicalOperator (f.chart p).index (chartOp p)).adjoint)
      (u : H) (hu : MemVectorFourierSobolev (n : ℝ) u) :
      MemVectorFourierSobolev ((n : ℝ)+1) (V u) ∧
      vectorFourierSobolevNorm ((n : ℝ)+1) (V u) ≤
        (((d+1 : ℝ)*(d+1)*G p n)*D p (2*(d+2)+(n+1))) *
          (vectorFourierSobolevNorm (n : ℝ) u+high*‖u‖) := by
    have hd := hactual p L hL Q B hQ hB hQrange hQlow hBlow
    have hsymbol := hd.2.2.2.2.2 (selectedAlgebraicSymbol f p L Q B o)
      (by fin_cases o <;> simp [selectedAlgebraicSymbol])
    have he := (hsymbol.2.2.2 n).1 u hu
    have hv : MemVectorFourierSobolev ((n : ℝ)+1) (V u) ∧
        vectorFourierSobolevNorm ((n : ℝ)+1) (V u) ≤
          ((d+1 : ℝ)*(d+1)*G p n) * (vectorFourierSobolevNorm (n : ℝ) u+
            (D p (2*(d+2)+(n+1)) *
              (1+cNorm (closedBall x RQ) (n+(2*(d+2)+2)) Q+
                cNorm (closedBall x RQ) (n+(2*(d+2)+2)) B))*‖u‖) := by
      rcases hV with rfl | rfl
      · exact he.1
      · exact he.2
    refine ⟨hv.1, hv.2.trans ?_⟩
    have horder : n+(2*(d+2)+2) ≤ n+sectorLowOrder d := by
      have := (sectorLowOrder_bounds d).2.2
      omega
    have hsmall : 1+cNorm (closedBall x RQ) (n+(2*(d+2)+2)) Q+
        cNorm (closedBall x RQ) (n+(2*(d+2)+2)) B ≤ high := by
      exact add_le_add (add_le_add le_rfl (cNorm_mono_order horder)) (cNorm_mono_order horder)
    have hdim : 0 ≤ (d+1 : ℝ)*(d+1)*G p n := mul_nonneg (by positivity) (hG p n)
    have hnorm : vectorFourierSobolevNorm (n : ℝ) u ≤
        D p (2*(d+2)+(n+1))*vectorFourierSobolevNorm (n : ℝ) u :=
      le_mul_of_one_le_left (norm_nonneg _) (hD p _)
    calc
      _ ≤ ((d+1 : ℝ)*(d+1)*G p n)*
          (D p (2*(d+2)+(n+1))*vectorFourierSobolevNorm (n : ℝ) u+
            (D p (2*(d+2)+(n+1))*high)*‖u‖) := by
          apply mul_le_mul_of_nonneg_left _ hdim
          exact add_le_add hnorm (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsmall (zero_le_one.trans (hD p _))) (norm_nonneg u))
      _ = _ := by ring
  have hchart p (V : H →L[ℂ] H) (hV : V = chartOp p ∨ V = (chartOp p).adjoint)
      (u : H) (hu : MemVectorFourierSobolev (n : ℝ) u) :
      MemVectorFourierSobolev ((n : ℝ)+1) (V u) ∧
      vectorFourierSobolevNorm ((n : ℝ)+1) (V u) ≤
        (((d+1 : ℝ)*(d+1)*G p n)*D p (2*(d+2)+(n+1))) *
          (vectorFourierSobolevNorm (n : ℝ) u+high*‖u‖) := by
    have hV' : physicalOperator (f.chart p).index V = physicalOperator (f.chart p).index (chartOp p) ∨
        physicalOperator (f.chart p).index V = (physicalOperator (f.chart p).index (chartOp p)).adjoint := by
      rcases hV with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (physicalOperator_adjoint _ _).symm
    have hb := hlocalBound p _ hV' ((physicalPullbackL2 (f.chart p).index).symm u)
      ((memVectorFourierSobolev_physicalPullbackL2_symm _ _ _).mpr hu)
    simpa only [physicalOperator_apply, LinearIsometryEquiv.apply_symm_apply,
      memVectorFourierSobolev_physicalPullbackL2_symm,
      vectorFourierSobolevNorm_physicalPullbackL2_symm, LinearIsometryEquiv.norm_map] using hb
  have hpositive (V : H →L[ℂ] H) (hV : V = T ∨ V = T.adjoint)
      (u : H) (hu : MemVectorFourierSobolev (n : ℝ) u) :
      MemVectorFourierSobolev ((n : ℝ)+1) (V u) ∧
      vectorFourierSobolevNorm ((n : ℝ)+1) (V u) ≤
        cost n * (vectorFourierSobolevNorm (n : ℝ) u+high*‖u‖) := by
    rcases hV with rfl | rfl
    · simpa only [T, selectedFiniteAlgebraicPDO, chartOp, cost, Finset.sum_mul] using finitePhysicalOperator_sobolev_bound
        (fun p ↦ (f.chart p).index) chartOp n ((n : ℝ)+1)
        (fun p ↦ ((d+1 : ℝ)*(d+1)*G p n)*D p (2*(d+2)+(n+1))) (fun _ ↦ high)
        (fun p ↦ hchart p _ (Or.inl rfl)) u hu
    · rw [show T = finitePhysicalOperator (fun p ↦ (f.chart p).index) chartOp from rfl,
        finitePhysicalOperator_adjoint]
      simpa only [T, selectedFiniteAlgebraicPDO, chartOp, cost, Finset.sum_mul] using finitePhysicalOperator_sobolev_bound
        (fun p ↦ (f.chart p).index) (fun p ↦ (chartOp p).adjoint) n ((n : ℝ)+1)
        (fun p ↦ ((d+1 : ℝ)*(d+1)*G p n)*D p (2*(d+2)+(n+1))) (fun _ ↦ high)
        (fun p ↦ hchart p _ (Or.inr rfl)) u hu
  refine ⟨hpositive, ?_⟩
  intro V hV u
  rcases hV with rfl | rfl
  · simpa only [Nat.cast_add, Nat.cast_one] using negativeVectorFourierSobolev_tame_bound_of_adjoint
      (Nat.cast_nonneg n) (by positivity) (hcost n) hhigh T
      (fun v hv ↦ hpositive _ (Or.inr rfl) v hv) u
  · simpa only [Nat.cast_add, Nat.cast_one] using negativeVectorFourierSobolev_tame_bound_of_adjoint
      (Nat.cast_nonneg n) (by positivity) (hcost n) hhigh T.adjoint
      (fun v hv ↦ by simpa only [ContinuousLinearMap.adjoint_adjoint] using
        (hpositive T (Or.inl rfl) v hv)) u

end JanetCartan.RegularSector.FiniteAssembly
