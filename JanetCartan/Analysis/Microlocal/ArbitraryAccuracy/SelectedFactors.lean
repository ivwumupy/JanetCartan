module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.PdoIdentification
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Collars

/-!
# Identifying the selected finite factors for residual chains

The four PDO entries are the literal selected algebraic, source, upper-endpoint,
and full differentiated algebraic symbols. The finite identities below keep
the common output, the original input, the physical coordinate permutations,
and the enlarged threshold. These identify the operators to which the
factor estimates for `app:ch_regular:lem:finite-chain` must be applied; they
do not assert the analytic estimates or the complete differential equation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy
open RegularSector RegularSector.FiniteAssembly RegularSector.FiniteEvolution
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo RegularSector.FiniteMasks
open RegularSector.FiniteMasks.ActualFamily RegularSector.Characteristic
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily RegularSector.Characteristic.PdoRealization
open RegularSector.Characteristic.EvolutionIntegral FourierIntegral FourierIntegral.LowBounds
open CharacteristicTransport.CompleteResidual
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)

/-- All four entries of the localization producer are the SAME selected
symbols at `2*L`. In particular entry three differentiates the entire
algebraic symbol with the original zeroth-order coefficient
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem selected_directPDOSymbols_eq_four_selected_symbols
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : TwoTimeAmplitude d (d+1)) :
    directPDOSymbols
      (fun y a ↦ (coefficient (f.chart p).index Q y a).map Complex.ofReal)
      (fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal) W₁
      (conicBminus (f.chart p).radialSection (f.chart p).index Q
        (fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root)
        (f.chart p).row (f.chart p).col)
      (conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
        (f.chart p).sourceMask) (selectedEndpointMultiplier f p L) =
      ![selectedAlgebraicSymbol f p (2*L) Q B 0,
        selectedSourceSymbol f p (2*L), selectedEndpointSymbol f p L Q W₁,
        selectedAlgebraicSymbol f p (2*L) Q B 1] := rfl

private theorem physicalOperator_comp_sourceCutMultiplier
    (i : Fin (d+1)) (a : E → ℝ) (ha : Continuous a) (hab : ∀ y, ‖a y‖ ≤ 1)
    (T : H →L[ℂ] H) :
    (physicalOperator i T).comp (sourceCutMultiplier a ha hab) =
      physicalOperator i (T.comp (sourceCutMultiplier (a ∘ physicalCoordinates i)
        (ha.comp (physicalCoordinates i).continuous) (fun _ ↦ hab _))) := by
  ext1 u
  simp only [ContinuousLinearMap.comp_apply, physicalOperator_apply,
    physicalPullbackL2_sourceCutMultiplier]

/-- Distribute the actual common masks across the finite retarded sum.
Each input multiplier stays to the RIGHT of its retained retarded factor.
Consumer: the selected complete residual identity below
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem selectedFiniteRetarded_commonMasks_eq_chart_sum
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (Op : f.centers → H →L[ℂ] H) :
    (sourceCutMultiplier output ho hob).comp
      ((finitePhysicalOperator (fun p ↦ (f.chart p).index) Op).comp
        (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib)) =
    finitePhysicalOperator (fun p ↦ (f.chart p).index) (fun p ↦
      (sourceCutMultiplier (output ∘ physicalCoordinates (f.chart p).index)
        (ho.comp (physicalCoordinates (f.chart p).index).continuous) (fun _ ↦ hob _)).comp
      ((Op p).comp (sourceCutMultiplier (f.inputMask ∘ physicalCoordinates (f.chart p).index)
        (f.inputMask_smooth.continuous.comp (physicalCoordinates (f.chart p).index).continuous)
        (fun _ ↦ hib _)))) := by
  classical
  ext1 u
  simp only [finitePhysicalOperator, ContinuousLinearMap.comp_apply, sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact DFunLike.congr_fun
    ((congrArg (fun A : H →L[ℂ] H ↦ (sourceCutMultiplier output ho hob).comp A)
      (physicalOperator_comp_sourceCutMultiplier (f.chart p).index f.inputMask
        f.inputMask_smooth.continuous hib (Op p))).trans
      (sourceCutMultiplier_comp_physicalOperator (f.chart p).index output ho hob _)) u

/-- Exact finite decomposition of the selected solver and complete error
into chart factors. The normal-amplitude certificates are the precise
outputs of `exists_finite_algebraic_pdo_sums`, used only to identify output
masking. No leakage bound is assumed. This supplies the SAME operators for
the `CompleteFactor` and `FiniteCosts` applications
(`app:ch_regular:lem:finite-chain`, `energy-complete-residual`). -/
theorem selectedFinite_solver_and_completeError_eq_chart_factors
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) (hL : f.radialThreshold ≤ L)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
    (Op : Bool → f.centers → H →L[ℂ] H)
    (R C : Fin 2 → f.centers → ℝ)
    (hb : ∀ o p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L) Q B o)) (R o p) (C o p)) :
    let P := fun p k ↦ maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
      (![selectedAlgebraicSymbol f p (2*L) Q B 0, selectedSourceSymbol f p (2*L),
        selectedEndpointSymbol f p L Q (W₁ p), selectedAlgebraicSymbol f p (2*L) Q B 1] k)
    let T := fun k ↦ (sourceCutMultiplier output ho hob).comp
      ((finitePhysicalOperator (fun p ↦ (f.chart p).index) (Op k)).comp
        (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
    let Tc := fun k p ↦
      (sourceCutMultiplier (output ∘ physicalCoordinates (f.chart p).index)
        (ho.comp (physicalCoordinates (f.chart p).index).continuous) (fun _ ↦ hob _)).comp
      ((Op k p).comp (sourceCutMultiplier (f.inputMask ∘ physicalCoordinates (f.chart p).index)
        (f.inputMask_smooth.continuous.comp (physicalCoordinates (f.chart p).index).continuous)
        (fun _ ↦ hib _)))
    let S := fun p ↦ Tc false p + (1 / Complex.I) • P p 0
    let G := fun p ↦ P p 1 + (P p 2 + Tc true p + (1 / Complex.I) • P p 3)
    selectedFiniteDirectSolver f L Q B output ho hob (T false) =
      finitePhysicalOperator (fun p ↦ (f.chart p).index) S ∧
    selectedFiniteCompleteError f L Q B W₁ output ho hob (T true) =
      finitePhysicalOperator (fun p ↦ (f.chart p).index) G - 1 ∧
    (selectedFiniteCompleteError f L Q B W₁ output ho hob (T true)).adjoint =
      finitePhysicalOperator (fun p ↦ (f.chart p).index) (fun p ↦ (G p).adjoint) - 1 := by
  classical
  intro P T Tc S G
  have ht k : T k = finitePhysicalOperator (fun p ↦ (f.chart p).index) (Tc k) :=
    selectedFiniteRetarded_commonMasks_eq_chart_sum f output ho hob hib (Op k)
  have ha o := selectedFiniteAlgebraicPDO_commonOutput f L Q B o output ho hob hsupp
    (R o) (C o) (hb o)
  have hp := selectedFiniteSourcePDO_commonOutput f L hL output ho hob hsupp
  have hscalar : (1 / Complex.I : ℂ) = -Complex.I := by simp
  have hsum (A D : f.centers → H →L[ℂ] H) :
      finitePhysicalOperator (fun p ↦ (f.chart p).index) (fun p ↦ A p + D p) =
        finitePhysicalOperator (fun p ↦ (f.chart p).index) A +
        finitePhysicalOperator (fun p ↦ (f.chart p).index) D := by
    simp [finitePhysicalOperator, FiniteEvolution.physicalOperator, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.add_comp, Finset.sum_add_distrib]
  have hsmul (a : ℂ) (A : f.centers → H →L[ℂ] H) :
      finitePhysicalOperator (fun p ↦ (f.chart p).index) (fun p ↦ a • A p) =
        a • finitePhysicalOperator (fun p ↦ (f.chart p).index) A := by
    simp [finitePhysicalOperator, FiniteEvolution.physicalOperator,
      ContinuousLinearMap.smul_comp, Finset.smul_sum]
  have hS : selectedFiniteDirectSolver f L Q B output ho hob (T false) =
      finitePhysicalOperator (fun p ↦ (f.chart p).index) S := by
    change T false + (-Complex.I) •
      (sourceCutMultiplier output ho hob).comp (selectedFiniteAlgebraicPDO f (2*L) Q B 0) = _
    rw [ht, ha]
    change finitePhysicalOperator (fun p ↦ (f.chart p).index) (Tc false) +
      (-Complex.I) • finitePhysicalOperator (fun p ↦ (f.chart p).index) (fun p ↦ P p 0) =
      finitePhysicalOperator (fun p ↦ (f.chart p).index)
        (fun p ↦ Tc false p + (1 / Complex.I) • P p 0)
    conv_rhs =>
      rw [hsum (Tc false) (fun p ↦ (1 / Complex.I) • P p 0),
        hsmul (1 / Complex.I) (fun p ↦ P p 0)]
    rw [hscalar]
  have hG : selectedFiniteCompleteError f L Q B W₁ output ho hob (T true) =
      finitePhysicalOperator (fun p ↦ (f.chart p).index) G - 1 := by
    change ((sourceCutMultiplier output ho hob).comp (selectedFiniteSourcePDO f L) - 1) +
      (selectedFiniteEndpointPDO f L Q W₁ output + T true + (-Complex.I) •
        (sourceCutMultiplier output ho hob).comp (selectedFiniteAlgebraicPDO f (2*L) Q B 1)) = _
    rw [← hp, ht, ha]
    change (finitePhysicalOperator (fun p ↦ (f.chart p).index) (fun p ↦ P p 1) - 1) +
      (finitePhysicalOperator (fun p ↦ (f.chart p).index) (fun p ↦ P p 2) +
        finitePhysicalOperator (fun p ↦ (f.chart p).index) (Tc true) +
        (-Complex.I) • finitePhysicalOperator (fun p ↦ (f.chart p).index) (fun p ↦ P p 3)) =
      finitePhysicalOperator (fun p ↦ (f.chart p).index)
        (fun p ↦ P p 1 + (P p 2 + Tc true p + (1 / Complex.I) • P p 3)) - 1
    conv_rhs =>
      rw [hsum (fun p ↦ P p 1) (fun p ↦ P p 2 + Tc true p + (1 / Complex.I) • P p 3),
        hsum (fun p ↦ P p 2 + Tc true p) (fun p ↦ (1 / Complex.I) • P p 3),
        hsum (fun p ↦ P p 2) (Tc true),
        hsmul (1 / Complex.I) (fun p ↦ P p 3)]
    rw [hscalar]
    exact sub_add_eq_add_sub _ _ _
  refine ⟨hS, hG, ?_⟩
  calc
    _ = (finitePhysicalOperator (fun p ↦ (f.chart p).index) G - 1).adjoint :=
      congrArg (fun A : H →L[ℂ] H ↦ A.adjoint) hG
    _ = (finitePhysicalOperator (fun p ↦ (f.chart p).index) G).adjoint -
        (1 : H →L[ℂ] H).adjoint := map_sub _ _ _
    _ = (finitePhysicalOperator (fun p ↦ (f.chart p).index) G).adjoint - 1 :=
      congrArg (fun A : H →L[ℂ] H ↦
        (finitePhysicalOperator (fun p ↦ (f.chart p).index) G).adjoint - A)
        ContinuousLinearMap.adjoint_one
    _ = _ := congrArg (fun A : H →L[ℂ] H ↦ A - 1)
      (finitePhysicalOperator_adjoint (fun p ↦ (f.chart p).index) G)

end JanetCartan.ArbitraryAccuracy
