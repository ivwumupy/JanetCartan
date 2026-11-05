module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Regularizations
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.FrequencySupport
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Assembly

/-!
# PDO inputs on the retained selected witnesses

For the PDO block of
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`,
construct joint normalized symbol and mask grades, noncomparable physical
grades, joint smoothness, original frequency support and literal forward
and adjoint regularizations of branches one, two and three. The source
certificate is constructed from the actual masks; the other two certificates
are retained outputs of `FiniteAssembly.exists_finite_direct_operator_bounds`.
The smaller endpoint output is applied without altering the original source
mask or doubled threshold. `exists_selected_threePDO_completeFactor_grades`
combines the actual branch producers and the buffered-localizer profiles,
with zero offsets and constants uniform over the fixed selected family.

The original branch orders are `0, -1, -1`, before the proved common
order-zero domination. The remaining inputs are the original coefficient
profile and the precise geometric, seminorm and normal-amplitude certificates
from the retained construction. The parent instantiates them on the SAME
witnesses and applies the complete chart leakage theorem. These PDO inputs
alone do not prove that leakage theorem or the unconditional existence result.
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
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)

/-- The three actual residual PDO branches have joint smoothness, the
original frequency carrier, and literal forward/adjoint representatives
converging strongly to the SAME selected operators. The source certificate
comes from `exists_endpoint_source_pdo_budgets`. The algebraic and endpoint
certificates are the exact retained outputs of
`FiniteAssembly.exists_finite_direct_operator_bounds`; no localized operator
bound is assumed. The full `B` and the source-before-Fourier ordering remain
unchanged. Consumer: `hAp`, frequency/cutoff inputs, `hrealp`, and `hlimp` in
`CompleteFactor` (`app:ch_regular_base:eq:energy-complete-residual`,
`app:ch_regular:lem:finite-chain`). Quantitative symbol grades are separate. -/
theorem exists_selected_threePDO_regularizations
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (threshold : ℝ) (ht : 0 < threshold)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hos : tsupport output ⊆ ball x f.physicalRadius)
    (hob : ∀ y, ‖output y‖ ≤ 1)
    {Ralg Malg : ℝ}
    (halg : GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*threshold) Q B 1)) Ralg Malg)
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
    let A := fun backward (j : Fin 3) ↦ orientedMaskedPDOAmplitude backward
      (endpointOutputMask f p output) (chartInputMask f p) (cP (![1, 2, 3] j))
    let F := tsupport (selectedEndpointMultiplier f p threshold)
    (∀ backward j, ContDiff ℝ ∞ (fun v : (E × E) × E ↦ A backward j v.1.1 v.1.2 v.2)) ∧
    IsClosed F ∧ (0 : E) ∉ F ∧
    (∀ backward j x y ξ, ξ ∉ F → A backward j x y ξ = 0) ∧
    ∃ Preg : Bool → Fin 3 → ℕ → H →L[ℂ] H,
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
            (cP (![1, 2, 3] j))).adjoint
          else maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
            (cP (![1, 2, 3] j))) u))) := by
  classical
  intro cP A F
  obtain ⟨hout, hcout, _⟩ := endpointOutputMask_properties f p ho hoc hos
  obtain ⟨_, _, hco, hcs, _⟩ := chartPhysicalMasks_properties f p
  obtain ⟨Rsrc, _, Csrc, _, hsrc, _⟩ := exists_endpoint_source_pdo_budgets f p threshold ho hoc hos
  obtain ⟨hsourceSmooth, Tsrc, hsrcAdj, hsrcReal, hsrcLim⟩ :=
    exists_maskedPDO_oriented_regularizations _ _ _ hcout hcs hsrc
  obtain ⟨hendpointSmooth, Tend, hendAdj, hendReal, hendLim⟩ :=
    exists_maskedPDO_oriented_regularizations _ _ _ hcout hcs hend
  let e := physicalCoordinates (f.chart p).index
  obtain ⟨halgebraicSmooth, Talg, halgAdj, halgReal, halgLim⟩ :=
    exists_commonOutputPDO_oriented_regularizations _ _ _ hco hcs halg
      (output ∘ e) (ho.comp e.contDiff) (hoc.comp_homeomorph e.toHomeomorph)
      (fun y ↦ hob (e y)) (endpointOutputMask_mul_chartOutputMask f p hos)
  have hcP : cP = ![selectedAlgebraicSymbol f p (2*threshold) Q B 0,
      selectedSourceSymbol f p (2*threshold), selectedEndpointSymbol f p threshold Q W₁,
      selectedAlgebraicSymbol f p (2*threshold) Q B 1] :=
    selected_directPDOSymbols_eq_four_selected_symbols f p threshold Q B W₁
  have hsmooth backward j : ContDiff ℝ ∞ (fun v : (E × E) × E ↦
      A backward j v.1.1 v.1.2 v.2) := by
    dsimp only [A]
    rw [hcP]
    fin_cases j
    · exact hsourceSmooth backward
    · exact hendpointSmooth backward
    · exact halgebraicSmooth backward
  have hfrequency := selected_directPDO_frequency_support f p ht
    (fun y a ↦ (coefficient (f.chart p).index Q y a).map Complex.ofReal)
    (fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal) W₁
    (conicBminus (f.chart p).radialSection (f.chart p).index Q
      (fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root)
      (f.chart p).row (f.chart p).col)
    (conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
      (f.chart p).sourceMask) output
  refine ⟨hsmooth, hfrequency.1, hfrequency.2.1,
    fun backward j ↦ hfrequency.2.2 backward (![1, 2, 3] j),
    fun backward j ↦ ![Tsrc backward, Tend backward, Talg backward] j, ?_, ?_, ?_⟩
  · intro j l
    fin_cases j
    · exact hsrcAdj l
    · exact hendAdj l
    · exact halgAdj l
  · intro backward j l u
    dsimp only [A]
    rw [hcP]
    fin_cases j
    · exact hsrcReal backward l u
    · exact hendReal backward l u
    · exact halgReal backward l u
  · intro backward j u
    rw [hcP]
    fin_cases j
    · exact hsrcLim backward u
    · exact hendLim backward u
    · exact halgLim backward u

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
