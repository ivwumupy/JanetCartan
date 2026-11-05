module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.SignedMeasuredLeakage
/-!
# Local leakage of the actual signed characteristic letters

The endpoint, retarded and full-B algebraic branches are exactly the three
letters in the normalized complete residual. Their known measured Fourier
estimates transfer to the genuine local restriction product, including the
external half, 1/i, whole conjugates and literal adjoints.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
open Set MeasureTheory
open scoped JanetCartan.RegularSector.Realization
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open ResidualLocalization LocalSobolev Pseudodifferential FourierIntegral.LowBounds
open RegularSector RegularSector.Realization RegularSector.FiniteAssembly
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.RetardedLocalization
open RegularSector.FiniteEvolution RegularSector.Characteristic.ResidualCoordinates
open RegularSector.FiniteMasks.ActualFamily RegularSector.FiniteResidual.FiniteIdentity
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => SpacetimeL2 d q


variable {Ω : Set E} {x : E} {RQ M : ℝ} {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set E}
open RegularSector.FinitePdo RegularSector.FiniteAlgebraic CharacteristicTransport.CompleteResidual

/-- Apply the measured chart comparison to the three actual normalized
characteristic letters. The Fourier input is precisely the endpoint, retarded
or full-B algebraic estimate in
`exists_finite_selected_direct_construction_with_measured_characteristic_leakage`.
The half and `1/i` remain in the operator; their norms are at most one. The
comparison constant precedes the selected family, fields, proof masks, domain
and accuracy. Consumer: the signed local constructor and the leakage input
of every ordered residual word (`app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:chain-tail`, `app:ch_regular_base:eq:measured-adjoint`). -/
theorem exists_selectedSignedCharacteristic_local_leakage_comparison (d m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
      {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
      (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (threshold : ℝ)
      (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
      (B : Euclidean (d+1) → MetricTensor (d+1))
      (W₁ : f.centers → TwoTimeAmplitude d (d+1))
      (output : Euclidean (d+1) → ℝ) (ho : Continuous output)
      (hob : ∀ y, ‖output y‖ ≤ 1) (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
      (T : f.centers → SpacetimeL2 d (d+1) →L[ℂ] SpacetimeL2 d (d+1))
      (p : f.centers) (branch : Fin 3) (reflected backward : Bool)
      (U : Set (Euclidean (d+1))) (hU : MeasurableSet U)
      (μ ν : Euclidean (d+1) → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
      (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1),
    tsupport μ ⊆ U → tsupport ν ⊆ U →
    ∀ R Lout Ri Li : SpacetimeL2 d (d+1) →L[ℂ] SpacetimeL2 d (d+1),
    physicalOperator (f.chart p).index Ri = R → physicalOperator (f.chart p).index Li = Lout →
    (∀ u, R (star u) = star (R u)) → (∀ u, Lout (star u) = star (Lout u)) →
    ∀ Bleak : ℝ, 0 ≤ Bleak →
    let S₀ := ![maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
        (selectedEndpointSymbol f p threshold Q (W₁ p)),
      selectedCommonChartRetarded f p output ho hob hib (T p),
      maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*threshold) Q B 1)] branch
    let A := measuredOperator (μ ∘ physicalCoordinates (f.chart p).index)
      (ν ∘ physicalCoordinates (f.chart p).index)
      (hμ.comp (physicalCoordinates (f.chart p).index).continuous)
      (hν.comp (physicalCoordinates (f.chart p).index).continuous)
      (fun _ ↦ hμb _) (fun _ ↦ hνb _) S₀
    (∀ u, MemVectorFourierSobolev (m : ℝ)
        ((1 - Li) ((if backward then A.adjoint else A) (Ri u))) ∧
      vectorFourierSobolevNorm (m : ℝ)
        ((1 - Li) ((if backward then A.adjoint else A) (Ri u))) ≤ Bleak * ‖u‖) →
    let P := measuredOperator μ ν hμ hν hμb hνb
      (selectedFullPhysicalResidualTerm f hK threshold Q B W₁ output ho hob hib T
        (.inl (p, branch), reflected))
    let S := if backward then P.adjoint else P
    ∀ u : LocalL2 U (EuclideanSpace ℂ (Fin (d+1))),
      let v := (1 - localRetardedOperator hU U Lout)
        (localRetardedOperator hU U S (localRetardedOperator hU U R u))
      v ∈ (restrictionSobolevScale U (EuclideanSpace ℂ (Fin (d+1))) hU).level m ∧
      (restrictionSobolevScale U (EuclideanSpace ℂ (Fin (d+1))) hU).gradeNorm m v ≤
        C * Bleak * ‖u‖ := by
  obtain ⟨C, hC, hb⟩ := exists_signedMeasuredChart_local_restriction_comparison d (d+1) m
  refine ⟨C, hC, ?_⟩
  intro Ω x RQ M A₀ K f hK threshold Q B W₁ output ho hob hib T p branch reflected backward
    U hU μ ν hμ hν hμb hνb hμs hνs R Lout Ri Li hRi hLi hR hL Bleak hBleak S₀ A hbound P S u v
  let scalar : ℂ := ![1, 1, 1/Complex.I] branch
  have hcommon : selectedCommonChartResidualTerm f p threshold Q B (W₁ p) output ho hob hib
      (T p) branch = scalar • S₀ := by
    fin_cases branch <;> simp [selectedCommonChartResidualTerm, scalar, S₀]
  have hphysical : physicalOperator (f.chart p).index
      (selectedCommonChartResidualTerm f p threshold Q B (W₁ p) output ho hob hib (T p) branch) =
      scalar • physicalOperator (f.chart p).index S₀ := by
    rw [hcommon]
    ext1 w
    simp only [physicalOperator_apply, smul_apply, map_smul]
  have hletter : selectedFullPhysicalResidualTerm f hK threshold Q B W₁ output ho hob hib T
      (.inl (p, branch), reflected) =
      if reflected then boundedConjugate (((1/2 : ℂ)*scalar) • physicalOperator (f.chart p).index S₀)
        else ((1/2 : ℂ)*scalar) • physicalOperator (f.chart p).index S₀ := by
    simp only [selectedFullPhysicalResidualTerm, Sum.elim_inl, hphysical, smul_smul]
  have hz : ‖(1/2 : ℂ)*scalar‖ ≤ 1 := by
    fin_cases branch <;> norm_num [scalar, norm_mul, norm_div]
  have h := hb (f.chart p).index U hU S₀ R Lout Ri Li hRi hLi hR hL
    μ ν hμ hν hμb hνb hμs hνs ((1/2 : ℂ)*scalar) reflected backward Bleak hBleak hbound u
  have hv : v = (1 - localRetardedOperator hU U Lout)
      (localRetardedOperator hU U
        (if backward then
          (measuredOperator μ ν hμ hν hμb hνb
            (if reflected then boundedConjugate (((1/2 : ℂ)*scalar) • physicalOperator (f.chart p).index S₀)
              else ((1/2 : ℂ)*scalar) • physicalOperator (f.chart p).index S₀)).adjoint
        else measuredOperator μ ν hμ hν hμb hνb
            (if reflected then boundedConjugate (((1/2 : ℂ)*scalar) • physicalOperator (f.chart p).index S₀)
              else ((1/2 : ℂ)*scalar) • physicalOperator (f.chart p).index S₀))
        (localRetardedOperator hU U R u)) := by
    dsimp only [v, S, P]
    rw [hletter]
  rw [hv]
  refine ⟨h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_left hz (mul_nonneg hC.le hBleak)).trans_eq (mul_one _)) (norm_nonneg u)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
