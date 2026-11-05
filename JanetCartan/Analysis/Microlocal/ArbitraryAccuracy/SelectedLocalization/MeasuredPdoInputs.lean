module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.MeasuredPdoCommon
public import JanetCartan.Analysis.Microlocal.SelectedResidualInputs.PdoRealizations

/-!
# Actual measured regularizations of the selected PDO branches

The retained source, algebraic and endpoint normal-amplitude certificates
supply the literal measured operators, with both original measurement masks.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FullLowBounds LowBounds LowBounds.FrequencyCutoff
open RegularSector RegularSector.Characteristic RegularSector.Characteristic.PdoRealization
open RegularSector.Characteristic.EvolutionIntegral RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily RegularSector.FiniteAssembly
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo
open CharacteristicTransport.CompleteResidual ResidualLocalization
open RegularSector.FiniteResidual.SelectedChart
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "CMat" => Matrix (Fin q) (Fin q) ℂ
local notation "H" => SpacetimeL2 d q

variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "Mat" => MetricTensor (d+1)

/-- Apply the retained source, endpoint and both algebraic certificates to
all four measured PDO branches. The actual measurement composition is identified
with the same canonical measured kernel; its finite regularizations and literal
adjoints converge strongly. The full zeroth-order field, original common masks
and doubled radial threshold are retained. Consumer: measured characteristic
letters of the normalized residual words
(`app:ch_regular_base:eq:energy-complete-residual`,
`app:ch_regular_base:eq:measured-adjoint`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_fourPDO_measured_regularizations
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (threshold : ℝ) (ht : 0 < threshold)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hos : tsupport output ⊆ ball x f.physicalRadius)
    (hob : ∀ y, ‖output y‖ ≤ 1)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
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
    let χo := fun x ↦ (μ x : ℂ) * endpointOutputMask f p output x
    let χs := fun y ↦ (ν y : ℂ) * chartInputMask f p y
    let A := fun backward (j : Fin 4) ↦ orientedMaskedPDOAmplitude backward
      χo χs (cP j)
    let F := tsupport (selectedEndpointMultiplier f p threshold)
    (∀ j, measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
      (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p) (cP j)) =
        maskedPhysicalPDO χo χs (cP j)) ∧
    (∀ backward j, ContDiff ℝ ∞ (fun v : (E × E) × E ↦ A backward j v.1.1 v.1.2 v.2)) ∧
    IsClosed F ∧ (0 : E) ∉ F ∧
    (∀ backward j x y ξ, ξ ∉ F → A backward j x y ξ = 0) ∧
    ∃ Preg : Bool → Fin 4 → ℕ → SpacetimeL2 d (d+1) →L[ℂ] SpacetimeL2 d (d+1),
      (∀ j l, Preg true j l = (Preg false j l).adjoint) ∧
      (∀ backward j l (u : graphTestSpace (d+1) (d+1)),
        Preg backward j l (graphTestToLp u) =ᵐ[volume] fun x ↦ WithLp.toLp 2
          (((if backward then reverseGraphOperator else graphOperator)
            (fun x ξ ↦ inner ℝ x ξ)
            (frequencyCutFullAmplitude (complexPhysicalCutoff l) (A backward j))
            (fun y ↦ (u.val y).ofLp)) x)) ∧
      (∀ backward j u, Tendsto (fun l ↦ Preg backward j l u) atTop
        (𝓝 ((if backward then
          (maskedPhysicalPDO χo χs (cP j)).adjoint
          else maskedPhysicalPDO χo χs (cP j)) u))) := by
  classical
  intro cP χo χs A F
  obtain ⟨_, hcout, _⟩ := endpointOutputMask_properties f p ho hoc hos
  obtain ⟨_, _, hco, hcs, _⟩ := chartPhysicalMasks_properties f p
  obtain ⟨Rsrc, _, Csrc, _, hsrc, _⟩ := exists_endpoint_source_pdo_budgets f p threshold ho hoc hos
  obtain ⟨hsourceSmooth, Tsrc, hsrcAdj, hsrcReal, hsrcLim⟩ :=
    exists_measured_maskedPDO_oriented_regularizations _ _ _ hcout hcs hsrc μ ν hμ hν hμb hνb
  obtain ⟨hendpointSmooth, Tend, hendAdj, hendReal, hendLim⟩ :=
    exists_measured_maskedPDO_oriented_regularizations _ _ _ hcout hcs hend μ ν hμ hν hμb hνb
  let e := physicalCoordinates (f.chart p).index
  have hregular (o : Fin 2) :=
    exists_measured_commonOutputPDO_oriented_regularizations _ _ _ hco hcs (halg o)
      (output ∘ e) (ho.comp e.contDiff) (fun y ↦ hob (e y))
      (endpointOutputMask_mul_chartOutputMask f p hos) μ ν hμ hν hμb hνb
  choose halgebraicSmooth Talg halgAdj halgReal halgLim using hregular
  have hcP : cP = ![selectedAlgebraicSymbol f p (2*threshold) Q B 0,
      selectedSourceSymbol f p (2*threshold), selectedEndpointSymbol f p threshold Q W₁,
      selectedAlgebraicSymbol f p (2*threshold) Q B 1] :=
    selected_directPDOSymbols_eq_four_selected_symbols f p threshold Q B W₁
  have hfrequency := selected_directPDO_frequency_support f p ht
    (fun y a ↦ (coefficient (f.chart p).index Q y a).map Complex.ofReal)
    (fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal) W₁
    (conicBminus (f.chart p).radialSection (f.chart p).index Q
      (fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root)
      (f.chart p).row (f.chart p).col)
    (conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
      (f.chart p).sourceMask) output
  refine ⟨?_, ?_, hfrequency.1, hfrequency.2.1, ?_,
    fun backward j ↦ ![Talg 0 backward, Tsrc backward, Tend backward, Talg 1 backward] j,
    ?_, ?_, ?_⟩
  · intro j
    rw [hcP]
    fin_cases j
    · exact measured_commonOutputPDO_eq _ _ _ (halg 0) (output ∘ e) (ho.comp e.contDiff)
        (fun y ↦ hob (e y)) (endpointOutputMask_mul_chartOutputMask f p hos) μ ν hμ hν hμb hνb
    · exact measured_maskedPhysicalPDO_eq _ _ _ hsrc μ ν hμ hν hμb hνb
    · exact measured_maskedPhysicalPDO_eq _ _ _ hend μ ν hμ hν hμb hνb
    · exact measured_commonOutputPDO_eq _ _ _ (halg 1) (output ∘ e) (ho.comp e.contDiff)
        (fun y ↦ hob (e y)) (endpointOutputMask_mul_chartOutputMask f p hos) μ ν hμ hν hμb hνb
  · intro backward j
    dsimp only [A]
    rw [hcP]
    fin_cases j
    · exact halgebraicSmooth 0 backward
    · exact hsourceSmooth backward
    · exact hendpointSmooth backward
    · exact halgebraicSmooth 1 backward
  · intro backward j y z ξ hξ
    have he := measured_orientedPDOAmplitude_eq μ ν (LinearIsometryEquiv.refl ℝ E)
      (endpointOutputMask f p output) (chartInputMask f p) (cP j) backward y z ξ
    change orientedMaskedPDOAmplitude backward χo χs (cP j) y z ξ = 0
    simp only [LinearIsometryEquiv.coe_refl, id_eq] at he
    exact he.trans (by rw [hfrequency.2.2 backward j y z ξ hξ, smul_zero])
  · intro j l
    fin_cases j
    · exact halgAdj 0 l
    · exact hsrcAdj l
    · exact hendAdj l
    · exact halgAdj 1 l
  · intro backward j l u
    dsimp only [A]
    rw [hcP]
    fin_cases j
    · exact halgReal 0 backward l u
    · exact hsrcReal backward l u
    · exact hendReal backward l u
    · exact halgReal 1 backward l u
  · intro backward j u
    rw [hcP]
    fin_cases j
    · exact halgLim 0 backward u
    · exact hsrcLim backward u
    · exact hendLim backward u
    · exact halgLim 1 backward u

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
