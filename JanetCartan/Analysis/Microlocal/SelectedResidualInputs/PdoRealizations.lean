module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades

/-!
# Literal regularizations of all four selected PDO branches

Retain the algebraic solver as well as the three complete-residual terms.
All use the original common physical masks and canonical frequency cutoffs.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedResidualInputs
open SelectedLocalization
open FourierIntegral FullLowBounds LowBounds LowBounds.FrequencyCutoff
open RegularSector RegularSector.Characteristic RegularSector.Characteristic.PdoRealization
open RegularSector.Characteristic.EvolutionIntegral RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily RegularSector.FiniteAssembly
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo
open CharacteristicTransport.CompleteResidual ResidualLocalization
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)

/-- Apply the existing residual PDO realizations and the common-output
algebraic realization to all four original direct symbols. The two normal
amplitude certificates are retained by the supplied-family direct constructor;
its endpoint estimate gives `hend`. Consumer: the complete physical residual
restriction estimate and the retained direct solver identification
(`app:ch_regular_base:eq:energy-complete-residual`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_fourPDO_regularizations
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (threshold : ℝ) (ht : 0 < threshold)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hos : tsupport output ⊆ ball x f.physicalRadius)
    (hob : ∀ y, ‖output y‖ ≤ 1)
    {Ralg Malg : Fin 2 → ℝ}
    (halg : ∀ o, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*threshold) Q B o)) (Ralg o) (Malg o))
    {Rend Mend : ℝ}
    (hend : GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (endpointOutputMask f p output) (chartInputMask f p)
        (selectedEndpointSymbol f p threshold Q W₁)) Rend Mend) :
    let cP := directPDOSymbols
      (fun y a ↦ (coefficient (f.chart p).index Q y a).map Complex.ofReal)
      (fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal) W₁
      (conicBminus (f.chart p).radialSection (f.chart p).index Q
        (fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root)
        (f.chart p).row (f.chart p).col)
      (conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
        (f.chart p).sourceMask) (selectedEndpointMultiplier f p threshold)
    let A := fun backward (j : Fin 4) ↦ orientedMaskedPDOAmplitude backward
      (endpointOutputMask f p output) (chartInputMask f p) (cP j)
    let F := tsupport (selectedEndpointMultiplier f p threshold)
    (∀ backward j, ContDiff ℝ ∞ (fun v : (E × E) × E ↦ A backward j v.1.1 v.1.2 v.2)) ∧
    IsClosed F ∧ (0 : E) ∉ F ∧
    (∀ backward j x y ξ, ξ ∉ F → A backward j x y ξ = 0) ∧
    ∃ Preg : Bool → Fin 4 → ℕ → H →L[ℂ] H,
      (∀ j l, Preg true j l = (Preg false j l).adjoint) ∧
      (∀ backward j l (u : graphTestSpace (d+1) (d+1)),
        Preg backward j l (graphTestToLp u) =ᵐ[volume] fun x ↦ WithLp.toLp 2
          (((if backward then reverseGraphOperator else graphOperator)
            (fun x ξ ↦ inner ℝ x ξ)
            (frequencyCutFullAmplitude (complexPhysicalCutoff l) (A backward j))
            (fun y ↦ (u.val y).ofLp)) x)) ∧
      (∀ backward j u, Tendsto (fun l ↦ Preg backward j l u) atTop
        (𝓝 ((if backward then
          (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
            (cP j)).adjoint
          else maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
            (cP j)) u))) := by
  classical
  intro cP A F
  obtain ⟨hs, hF, hzero, hsupp, Preg, hAdj, hreal, hlim⟩ :=
    exists_selected_threePDO_regularizations f p threshold ht Q B W₁ output ho hoc hos hob
      (halg 1) hend
  obtain ⟨_, _, hco, hcs, _⟩ := chartPhysicalMasks_properties f p
  let e := physicalCoordinates (f.chart p).index
  obtain ⟨hsolver, Tsolver, hsolverAdj, hsolverReal, hsolverLim⟩ :=
    exists_commonOutputPDO_oriented_regularizations _ _ _ hco hcs (halg 0)
      (output ∘ e) (ho.comp e.contDiff) (hoc.comp_homeomorph e.toHomeomorph)
      (fun y ↦ hob (e y)) (endpointOutputMask_mul_chartOutputMask f p hos)
  have hcP : cP 0 = selectedAlgebraicSymbol f p (2*threshold) Q B 0 := by
    rw [show cP = _ from selected_directPDOSymbols_eq_four_selected_symbols f p threshold Q B W₁]
    rfl
  have hfrequency := selected_directPDO_frequency_support f p ht
    (fun y a ↦ (coefficient (f.chart p).index Q y a).map Complex.ofReal)
    (fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal) W₁
    (conicBminus (f.chart p).radialSection (f.chart p).index Q
      (fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root)
      (f.chart p).row (f.chart p).col)
    (conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
      (f.chart p).sourceMask) output
  let Tall : Bool → Fin 4 → ℕ → H →L[ℂ] H :=
    fun backward ↦ Fin.cases (Tsolver backward) (Preg backward)
  refine ⟨?_, hF, hzero, hfrequency.2.2, Tall, ?_, ?_, ?_⟩
  · intro backward j
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · dsimp only [A]
      rw [hcP]
      exact hsolver backward
    · fin_cases j
      · exact hs backward 0
      · exact hs backward 1
      · exact hs backward 2
  · intro j l
    refine Fin.cases (hsolverAdj l) (fun j ↦ hAdj j l) j
  · intro backward j l u
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · dsimp only [A]
      rw [hcP]
      exact hsolverReal backward l u
    · fin_cases j
      · exact hreal backward 0 l u
      · exact hreal backward 1 l u
      · exact hreal backward 2 l u
  · intro backward j u
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · rw [hcP]
      exact hsolverLim backward u
    · fin_cases j
      · exact hlim backward 0 u
      · exact hlim backward 1 u
      · exact hlim backward 2 u

end JanetCartan.ArbitraryAccuracy.SelectedResidualInputs
