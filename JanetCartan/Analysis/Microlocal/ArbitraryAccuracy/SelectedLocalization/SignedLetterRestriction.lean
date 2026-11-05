module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PhysicalLeakage
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.LocalizerReality
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.RestrictionFactors.Algebra
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.ResidualTerms

/-!
# Individual signed residual letters on the measured local space

The normalized ordered words use individual complex letters. The Fourier
leakage estimate passes to each external scalar and whole conjugate, without
inserting a real projection. The original measurement masks then identify
the literal local product, including both intermediate zero extensions.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory
open scoped JanetCartan.RegularSector.Realization
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open ResidualLocalization LocalSobolev Pseudodifferential FourierIntegral.LowBounds
open RegularSector RegularSector.Realization RegularSector.FiniteAssembly
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.RetardedLocalization
open RegularSector.FiniteMasks.ActualFamily RegularSector.FiniteResidual.FiniteIdentity
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => SpacetimeL2 d q

private theorem signedLetter_starFiber_restrict (U : Set E) (u : H) :
    (starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap.compLp (restrictL2 U u) =
      restrictL2 U (star u) := by
  apply Lp.ext
  filter_upwards [(starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap.coeFn_compLp (restrictL2 U u),
    restrictL2_coeFn U u, restrictL2_coeFn U (star u), ae_restrict_of_ae (Lp.coeFn_star u)]
    with x hx hy hz hu
  rw [hx, hy, hz, hu]
  rfl

/-- The Fourier estimate for an actual branch gives restriction leakage
for each individual scalar-weighted letter and its whole conjugate. Literal
adjunction conjugates the scalar before the estimate. No real part is taken
between letters. Consumer: the signed complex alphabet in
`NormalizedResidualWords.measured_realResidual_hchain_of_words`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_signedLetter_fourier_restriction_comparison (d q m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (U : Set (Euclidean (d+1))) (hU : MeasurableSet U)
      (T Mi Mo : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q),
      (∀ u, Mi (star u) = star (Mi u)) →
      (∀ u, Mo (star u) = star (Mo u)) →
      ∀ (z : ℂ) (reflected backward : Bool) (B : ℝ), 0 ≤ B →
      (∀ u, MemVectorFourierSobolev (m : ℝ)
          ((1 - Mo) ((if backward then T.adjoint else T) (Mi u))) ∧
        vectorFourierSobolevNorm (m : ℝ)
          ((1 - Mo) ((if backward then T.adjoint else T) (Mi u))) ≤ B * ‖u‖) →
      let P := if reflected then boundedConjugate (z • T) else z • T
      let S := if backward then P.adjoint else P
      ∀ u, restrictL2 U ((1 - Mo) (S (Mi u))) ∈
          (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).level m ∧
        (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).gradeNorm m
          (restrictL2 U ((1 - Mo) (S (Mi u)))) ≤ K * B * ‖z‖ * ‖u‖ := by
  obtain ⟨C, hC, hcompare⟩ := exists_restrictionScale_fourier_comparison (d+1) q m
  let J := (starL' ℝ : EuclideanSpace ℂ (Fin q) ≃L[ℝ]
    EuclideanSpace ℂ (Fin q)).toContinuousLinearMap
  refine ⟨(‖J‖+1)*C, mul_pos (by positivity) hC, ?_⟩
  intro U hU T Mi Mo hi ho z reflected backward B hB hbound P S u
  let G := restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU
  let A := if backward then (z • T).adjoint else z • T
  let w := if backward then star z else z
  have hw : ‖w‖ = ‖z‖ := by cases backward <;> simp [w]
  have hA (v : SpacetimeL2 d q) :
      (1 - Mo) (A (Mi v)) =
        (1 - Mo) ((if backward then T.adjoint else T) (Mi (w • v))) := by
    cases backward <;> simp [A, w, map_smul, map_smulₛₗ]
  have hv (v : SpacetimeL2 d q) :
      restrictL2 U ((1 - Mo) (A (Mi v))) ∈ G.level m ∧
      G.gradeNorm m (restrictL2 U ((1 - Mo) (A (Mi v)))) ≤ C*B*‖z‖*‖v‖ := by
    rw [hA]
    obtain ⟨hm, hn⟩ := hcompare U hU _ _ (hbound (w • v)).1
      (restrictL2_coeFn U _).symm
    refine ⟨hm, hn.trans ?_⟩
    have hb := mul_le_mul_of_nonneg_left (hbound (w • v)).2 hC.le
    simpa only [norm_smul, hw, mul_assoc] using hb
  cases reflected with
  | false =>
    change restrictL2 U ((1 - Mo) (A (Mi u))) ∈ G.level m ∧ _
    refine ⟨(hv u).1, (hv u).2.trans ?_⟩
    have hn : 0 ≤ C*B*‖z‖*‖u‖ := by positivity
    nlinarith [mul_nonneg (norm_nonneg J) hn]
  | true =>
    have he : S = boundedConjugate A := by
      cases backward
      · rfl
      · exact boundedConjugate_adjoint (z • T)
    have hl : (1 - Mo) (S (Mi u)) = star ((1 - Mo) (A (Mi (star u)))) := by
      rw [he]
      change star (A (star (Mi u))) - Mo (star (A (star (Mi u)))) = _
      rw [ho, ← star_sub, hi]
      rfl
    rw [hl, ← signedLetter_starFiber_restrict]
    obtain ⟨hm, hn⟩ := compLp_restrictionSobolev_bound J (hv (star u)).1
    refine ⟨hm, ?_⟩
    change G.gradeNorm m (J.compLp _) ≤ _
    rw [restrictionSobolevScale_gradeNorm hU hm]
    apply hn.trans
    rw [← restrictionSobolevScale_gradeNorm hU (hv (star u)).1]
    have hb := mul_le_mul_of_nonneg_left (hv (star u)).2
      (show 0 ≤ ‖J‖+1 by positivity)
    simpa only [norm_star, mul_assoc] using hb

private theorem local_measured_factor_leakage_eq
    {U : Set E} (hU : MeasurableSet U) (T R Lout : H →L[ℂ] H)
    (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (hμs : tsupport μ ⊆ U) (hνs : tsupport ν ⊆ U)
    (u : LocalL2 U F) :
    (1 - localRetardedOperator hU U Lout)
      (localRetardedOperator hU U (measuredOperator μ ν hμ hν hμb hνb T)
        (localRetardedOperator hU U R u)) =
      restrictL2 U ((1 - Lout)
        (measuredOperator μ ν hμ hν hμb hνb T (R (SmallSupport.zeroExtend hU u)))) := by
  let v := R (SmallSupport.zeroExtend hU u)
  let A := measuredOperator μ ν hμ hν hμb hνb T
  have hi (w : H) : A (SmallSupport.zeroExtend hU (restrictL2 U w)) = A w := by
    change sourceCutMultiplier μ hμ hμb (T (sourceCutMultiplier ν hν hνb
      (SmallSupport.zeroExtend hU (restrictL2 U w)))) = _
    rw [sourceCutMultiplier_zeroExtend_restrictL2 hU ν hν hνb hνs]
    rfl
  have ho (w : H) : SmallSupport.zeroExtend hU (restrictL2 U (A w)) = A w :=
    zeroExtend_restrictL2_sourceCutMultiplier hU μ hμ hμb hμs _
  change restrictL2 U (A (SmallSupport.zeroExtend hU (restrictL2 U v))) -
    restrictL2 U (Lout (SmallSupport.zeroExtend hU (restrictL2 U
      (A (SmallSupport.zeroExtend hU (restrictL2 U v)))))) =
      restrictL2 U (A v - Lout (A v))
  rw [hi, ho, map_sub]

/-- The same supported measured factor has exact local leakage in either
literal orientation. Its two original measurement supports remove the
intermediate zero extensions; no Sobolev bound for zero extension is used.
Consumer: individual signed letters in `finiteChain_observation_rapidDecayAt`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular_base:eq:measured-adjoint`). -/
theorem measuredOperator_oriented_local_leakage_eq
    {U : Set E} (hU : MeasurableSet U) (T R Lout : H →L[ℂ] H)
    (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (hμs : tsupport μ ⊆ U) (hνs : tsupport ν ⊆ U)
    (backward : Bool) (u : LocalL2 U F) :
    let P := measuredOperator μ ν hμ hν hμb hνb T
    let S := if backward then P.adjoint else P
    (1 - localRetardedOperator hU U Lout)
      (localRetardedOperator hU U S (localRetardedOperator hU U R u)) =
      restrictL2 U ((1 - Lout) (S (R (SmallSupport.zeroExtend hU u)))) := by
  intro P S
  cases backward with
  | false => exact local_measured_factor_leakage_eq hU T R Lout μ ν hμ hν hμb hνb hμs hνs u
  | true =>
    dsimp only [S, P, ite_true]
    rw [measuredOperator_adjoint]
    exact local_measured_factor_leakage_eq hU T.adjoint R Lout ν μ hν hμ hνb hμb hνs hμs u

/-- The actual normalized signed characteristic/elliptic letter has the
literal local leakage product, with the original measurement masks and
zero extensions. The adjoint exchanges those masks. This support deduction
supplies the final restriction identification for
`finiteChain_observation_rapidDecayAt.hleak`; it assumes no analytic leakage
(`app:ch_regular:lem:finite-chain`, `app:ch_regular_base:eq:measured-adjoint`). -/
theorem selectedFullPhysicalResidualTerm_local_leakage_eq
    {Ω : Set E} {x : E} {RQ M : ℝ} {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set E}
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : f.centers → SpacetimeL2 d (d+1) →L[ℂ] SpacetimeL2 d (d+1))
    (a : ((f.centers × Fin 3) ⊕ Unit) × Bool)
    (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    {U : Set E} (hU : MeasurableSet U) (hμs : tsupport μ ⊆ U) (hνs : tsupport ν ⊆ U)
    (R Lout : SpacetimeL2 d (d+1) →L[ℂ] SpacetimeL2 d (d+1))
    (backward : Bool) (u : LocalL2 U (EuclideanSpace ℂ (Fin (d+1)))) :
    let P := measuredOperator μ ν hμ hν hμb hνb
      (selectedFullPhysicalResidualTerm f hK L Q B W₁ output ho hob hib T a)
    let S := if backward then P.adjoint else P
    (1 - localRetardedOperator hU U Lout)
      (localRetardedOperator hU U S (localRetardedOperator hU U R u)) =
      restrictL2 U ((1 - Lout) (S (R (SmallSupport.zeroExtend hU u)))) := by
  intro P S
  cases backward with
  | false => exact local_measured_factor_leakage_eq hU _ R Lout μ ν hμ hν hμb hνb hμs hνs u
  | true =>
    dsimp only [S, P, ite_true]
    rw [measuredOperator_adjoint]
    exact local_measured_factor_leakage_eq hU _ R Lout ν μ hν hμ hνb hμb hνs hμs u

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
