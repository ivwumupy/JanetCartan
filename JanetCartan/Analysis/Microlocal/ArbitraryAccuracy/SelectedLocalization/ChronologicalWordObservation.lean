module
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.NormalizedWordDecay
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.SignedWordChain

/-!
# Chronological observations on the original normalized inverse space

Whole-space zero extension transports the chronological analytic chain into
its exact ordered complex word. The finite-word summation then produces the
local measured residual powers, with real projection only after each word
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:finite-observation`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open ResponseTransfer LocalSobolev
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.RetardedLocalization

/-- Whole-space zero extension transports the chronological analytic chain
into its exact reversed complex operator list. No projection or support loss
is inserted between letters (`app:ch_regular:lem:finite-chain`). -/
theorem zeroExtend_factorChain_univ {d q : ℕ} {ι : Type*}
    (T : ℕ → ι → SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (u : ι → LocalL2 (univ : Set (Euclidean (d+1))) (EuclideanSpace ℂ (Fin q)))
    (n : ℕ) (i : ι) :
    SmallSupport.zeroExtend MeasurableSet.univ
      (factorChain (fun j i ↦
        (localRetardedOperator MeasurableSet.univ univ (T j i)).toLinearMap) u n i) =
    (List.ofFn (fun j : Fin n ↦ T j.val i)).reverse.prod
      (SmallSupport.zeroExtend MeasurableSet.univ (u i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.reverse_concat, List.prod_cons]
    change SmallSupport.zeroExtend MeasurableSet.univ
      (restrictL2 univ (T n i (SmallSupport.zeroExtend MeasurableSet.univ
        (factorChain (fun j i ↦
          (localRetardedOperator MeasurableSet.univ univ (T j i)).toLinearMap) u n i)))) = _
    rw [zeroExtend_restrictL2_univ, ih]
    rfl

/-- Reversing the finite chronological indices matches the operator list
in the normalized residual power expansion (`app:ch_regular:eq:chain-tail`). -/
private theorem reverse_ofFn_rev {α : Type*} {n : ℕ} (w : Fin n → α) :
    (List.ofFn (fun j ↦ w j.rev)).reverse = List.ofFn w := by
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp only [List.getElem_reverse, List.length_ofFn, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    simp only [List.length_reverse, List.length_ofFn] at hj hk
    omega

open RegularSector RegularSector.FiniteAssembly RegularSector.Realization
open RegularSector.NormalizedSolver RegularSector.NormalizedResidualWords
open RegularSector.FiniteMasks.ActualFamily RegularSector.FiniteResidual.FiniteIdentity
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.RetardedLocalization
open LocalSobolev ResidualLocalization FourierIntegral.LowBounds
variable {d : ℕ} {ι : Type*}
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
variable (L : ι → ℝ) (Q : ι → Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
variable (B : ι → Euclidean (d+1) → MetricTensor (d+1))
variable (W₁ : ι → f.centers → TwoTimeAmplitude d (d+1))
variable (output : Euclidean (d+1) → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
variable (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : ι → f.centers → (SpacetimeL2 d (d+1)) →L[ℂ] (SpacetimeL2 d (d+1)))
variable (μ ν : Euclidean (d+1) → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
variable (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
variable {U : Set (Euclidean (d+1))} (hU : MeasurableSet U)
variable (hμU : tsupport μ ⊆ U) (hνU : tsupport ν ⊆ U)
variable (W : Set (Euclidean (d+1))) (hW : MeasurableSet W) (s : ℕ) (ρ A : ι → ℝ)
variable (u : ι → LocalL2 U (EuclideanSpace ℝ (Fin (d+1))))
include hμU hνU


/-- The chronological whole-space observations supplied by the analytic
chain theorem imply the exact observed powers on the original local inverse
space. Finite indices are reversed explicitly; the letters are never commuted.
Consumer: `rapidDecayAt_inverse_of_finite_chains.hchain`
(`app:ch_regular:eq:chain-tail`, `app:ch_regular:eq:finite-observation`). -/
theorem normalizedSource_measuredResidual_hchain_of_factorChains
    (hsupp : tsupport output ⊆ Metric.ball x f.physicalRadius)
    (R C : ι → f.centers → ℝ)
    (hb : ∀ i p, FourierIntegral.GraphNormalAmplitudeBounds
      (RegularSector.Characteristic.PdoRealization.maskedPhysicalPDOCycleSymbol
        (FiniteAlgebraic.chartOutputMask f p) (FiniteAlgebraic.chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L i) (Q i) (B i) 1)) (R i p) (C i p)) :
    let letters := fun i a ↦ measuredOperator μ ν hμ hν hμb hνb
      (selectedFullPhysicalResidualTerm f hK (L i) (Q i) (B i) (W₁ i)
        output ho hob hib (T i) a)
    let source := fun i ↦ restrictL2 univ
      (l2ComplexInclusion volume (SmallSupport.zeroExtend hU (u i)))
    (∀ n (w : ℕ → (((f.centers × Fin 3) ⊕ Unit) × Bool)),
      RapidDecayAt
        (restrictionSobolevScale univ (EuclideanSpace ℂ (Fin (d+1))) MeasurableSet.univ)
        s ρ A (fun i ↦ restrictL2 univ
          ((pairedSource f hK (L i) output ho hob-1)
            (SmallSupport.zeroExtend MeasurableSet.univ
              (factorChain (fun j i ↦
                (localRetardedOperator MeasurableSet.univ univ (letters i (w j))).toLinearMap)
                source n i))))) →
    let retarded := fun i ↦ (sourceCutMultiplier output ho hob).comp
      ((FiniteEvolution.finitePhysicalOperator (fun p ↦ (f.chart p).index) (T i)).comp
        (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
    let P := fun i ↦ measuredOperator μ ν hμ hν hμb hνb
      (pairedResidual f hK (L i) (Q i) (B i) output ho hob (W₁ i) (retarded i))
    ∀ j, RapidDecayAt (restrictionSobolevScale W (EuclideanSpace ℝ (Fin (d+1))) hW)
      s ρ A (fun i ↦ localRealCompression hU W (pairedSource f hK (L i) output ho hob-1)
        ((localRealCompression hU U (P i)^j) (u i))) := by
  intro letters source hchain retarded P
  apply normalizedSource_measuredResidual_hchain_of_complex_words
    f hK L Q B W₁ output ho hob hib T μ ν hμ hν hμb hνb hU hμU hνU
    W hW s ρ A u hsupp R C hb
  intro n w
  let w' : ℕ → (((f.centers × Fin 3) ⊕ Unit) × Bool) := fun j ↦
    if hj : j < n then w ⟨n-1-j, by omega⟩ else (.inr (), false)
  have hw' : List.ofFn (fun j : Fin n ↦ w' j.val) = List.ofFn (fun j ↦ w j.rev) := by
    congr 1
    funext j
    dsimp only [w']
    rw [dite_eq_left j.isLt]
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  have he (i : ι) :
      SmallSupport.zeroExtend MeasurableSet.univ
        (factorChain (fun j i ↦
          (localRetardedOperator MeasurableSet.univ univ (letters i (w' j))).toLinearMap)
          source n i) =
      (List.ofFn (fun k ↦ letters i (w k))).prod
        (l2ComplexInclusion volume (SmallSupport.zeroExtend hU (u i))) := by
    rw [zeroExtend_factorChain_univ]
    change (List.ofFn (fun j : Fin n ↦ letters i (w' j.val))).reverse.prod
      (SmallSupport.zeroExtend MeasurableSet.univ
        (restrictL2 univ (l2ComplexInclusion volume (SmallSupport.zeroExtend hU (u i))))) = _
    rw [zeroExtend_restrictL2_univ]
    have hm : List.ofFn (fun j : Fin n ↦ letters i (w' j.val)) =
        (List.ofFn (fun j : Fin n ↦ w' j.val)).map (letters i) := by
      rw [List.map_ofFn]
      rfl
    rw [hm, hw', ← List.map_reverse, reverse_ofFn_rev, List.map_ofFn]
    rfl
  have h := hchain n w'
  simp_rw [he] at h
  exact h

end JanetCartan.ArbitraryAccuracy.SelectedLocalization

