module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.Construction

/-!
# Actual finite sums of the two algebraic PDO terms

Select the algebraic family once, retain every local inverse and symbol
conclusion, and sum its literal physical operators. Both orientations have
one additive original coefficient norm at the fixed sector order. These are
the algebraic solver and differentiated algebraic residual terms consumed by
`energy-complete-residual`; the retarded and endpoint terms are assembled
separately.
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

/-- The two literal algebraic symbols: the solver inverse and its full physical
coefficient derivative, including B (`complement-symbol`, `energy-complete-residual`). -/
def selectedAlgebraicSymbol {Ω : Set E} {x : E} {RQ M : ℝ} {A₀ : Coeff} {K : Set E}
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (L : ℝ)
    (Q : E → Coeff) (B : E → Mat) (o : Fin 2) : E → E → CMat :=
  let c := f.chart p
  let b := directAlgebraicSymbol
    (conicBminus c.radialSection c.index Q (fieldRoot (coordinateSplit c.index) Q c.root) c.row c.col)
    (conicSourceSymbol c.radialSection (conicMask (f.spatialMask p)) c.sourceMask)
    (fun ζ ↦ (dilatedConicMask (f.angularMask p) L (physicalCoordinates c.index ζ) : ℂ))
  if o = 0 then b else physicalSymbolApply
    (fun y a ↦ (coefficient c.index Q y a).map Complex.ofReal)
    (fun y ↦ (zeroth c.index B y).map Complex.ofReal) b

/-- Finite original-coordinate sum with both of the selected family's physical
masks. The physical scalar 1/i is inserted only when assembling the solver
and residual (`energy-complete-residual`). -/
def selectedFiniteAlgebraicPDO {Ω : Set E} {x : E} {RQ M : ℝ} {A₀ : Coeff} {K : Set E}
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Coeff) (B : E → Mat) (o : Fin 2) : H →L[ℂ] H :=
  finitePhysicalOperator (fun p ↦ (f.chart p).index)
    (fun p ↦ maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p)
      (selectedAlgebraicSymbol f p L Q B o))

/-- Construct the SAME finite algebraic family, preserving its complete local
output, and prove the finite forward and literal-adjoint gain. The uniform
low order and fixed high shift are chosen before Q, B, L and Sobolev order.
This is an actual PDO construction, not a premise on the assembled operator;
it supplies two terms, not the full sector theorem (`sector-theorem-residual`). -/
theorem exists_finite_algebraic_pdo_sums
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
  obtain ⟨f, hradii, hevolution, hlocal⟩ :=
    exists_finite_physical_algebraic_pdos hΩ x hRQ hKΩ A₀ hK hKzero hregular hM
  have hlocalKeep := hlocal
  choose hroot hsource ε hε Rbox hRbox Mbound hMbound C D G hC hD hG hactual using hlocal
  let cost n := ∑ p : f.centers, ((d+1 : ℝ)*(d+1)*G p n)*D p (2*(d+2)+(n+1))
  have hcost n : 0 ≤ cost n := Finset.sum_nonneg fun p _ ↦
    mul_nonneg (mul_nonneg (by positivity) (hG p n)) (zero_le_one.trans (hD p _))
  refine ⟨f, hradii, hevolution, hlocalKeep, cost, hcost, ?_⟩
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
