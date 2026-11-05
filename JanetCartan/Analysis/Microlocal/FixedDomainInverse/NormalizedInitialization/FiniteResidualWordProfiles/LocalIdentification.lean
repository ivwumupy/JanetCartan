module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualWordProfiles.Basic
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.LocalComplex
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ObservedParameterRemainders.Totalization
public import JanetCartan.Analysis.Sobolev.Local.Cutoff

/-!
# The original local powers have the same finite-word parameter jets

The actual outer measurement mask intertwines every complex local residual
power with its whole-space power. The original final bump commutes with zero
extension, and the retained and totalized phases agree on the original open
parameter domain. Hence all parameter jets are identical, without any
regularity assumption across that domain's boundary.

Consumer: the exact `hfinite` in
`complex_inverse_parameter_envelopes_of_actual_finite_words`
(`app:ch_regular:lem:finite-chain`,
`app:ch_response:eq:response-graded-reduced`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory
open scoped ContDiff Topology NNReal ENNReal JanetCartan.RegularSector.Realization

namespace JanetCartan.FixedDomainInverse.FiniteResidualWordProfiles

open Pseudodifferential FourierIntegral ResponseTransfer ResponseTransfer.Complement
open FourierIntegral.LowBounds
open RegularSector.FiniteAssembly LocalSobolev SmallSupport
open ObservedParameterRemainders

variable {d r : ℕ} {I : Type*}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The complex-linear bundle of the original measured local operator has
the SAME global power after zero extension, including power zero. This uses
only the actual output support (`app:ch_regular:lem:finite-chain`). -/
theorem zeroExtend_complex_measured_power
    {U : Set E} (hU : MeasurableSet U)
    (χout χin : E → ℝ) (ho : Continuous χout) (hi : Continuous χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1)
    (hs : tsupport χout ⊆ U) (T : H →L[ℂ] H) (N : ℕ) (u : LocalL2 U F) :
    zeroExtend hU
        (((complexLocalRetardedOperator hU U (measuredOperator χout χin ho hi hob hib T))^N) u) =
      ((measuredOperator χout χin ho hi hob hib T)^N) (zeroExtend hU u) := by
  have hint : Function.Semiconj (zeroExtend hU)
      (complexLocalRetardedOperator hU U (measuredOperator χout χin ho hi hob hib T))
      (measuredOperator χout χin ho hi hob hib T) :=
    zeroExtend_local_measuredOperator hU hU χout χin ho hi hob hib hs T
  simpa only [FunLike.coe_pow_eq_iterate] using hint.iterate_right N u

private theorem zeroExtend_bump_eq_sourceCutMultiplier
    {U : Set E} (hU : MeasurableSet U) {x : E} (χ : ContDiffBump x) (u : LocalL2 U F) :
    zeroExtend hU (bumpL2 (p := 2) le_rfl χ u) =
      sourceCutMultiplier χ χ.continuous (bump_norm_le_one χ) (zeroExtend hU u) := by
  apply Lp.ext
  filter_upwards [zeroExtend_bumpL2_coeFn hU χ u,
    sourceCutMultiplier_coeFn χ χ.continuous (bump_norm_le_one χ) (zeroExtend hU u),
    zeroExtend_coeFn hU u] with y hb hc hu
  rw [hb, hc, hu]
  exact (algebraMap_smul ℂ (χ y) (U.indicator u y)).symm

/-- The actual local observation and the proved global finite word have
identical Fréchet jets on the original open parameter domain. The only source
identity is the original recut source's zero extension. No intermediate
recutting, representative, or inverse is chosen
(`app:ch_response:eq:response-actual-solver-formula`). -/
theorem local_measured_power_parameter_jets_eq_global
    {U : Set E} (hU : MeasurableSet U) {x : E} (χ₂ χ₃ : ContDiffBump x)
    (hχ₂ : tsupport (χ₂ : E → ℝ) ⊆ U)
    (raw P S : I → H →L[ℂ] H)
    (hP : ∀ i, P i = measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
      (bump_norm_le_one χ₂) (bump_norm_le_one χ₃) (raw i))
    (source : I → Par → LocalL2 U F) (datum : I → Par → H)
    {V : Set Par} (hV : IsOpen V) (lam : I → ℝ)
    (φ : I → Par → E → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (hinitial : ∀ i c, c ∈ V → zeroExtend hU (source i c) =
      carrierMultiplication (lam i) (φ i c)
        ((hφ i).continuous.comp (continuous_const.prodMk continuous_id)) (datum i c))
    (N k : ℕ) (i : I) {c : Par} (hc : c ∈ V) :
    iteratedFDeriv ℝ k
      (fun q ↦ carrierMultiplication (-(lam i))
        (totalizedObservationPhase V (φ i) q)
        (continuous_totalizedObservationPhase (hφ i).contDiffOn q)
        (S i (zeroExtend hU (bumpL2 (p := 2) le_rfl χ₃
          (((complexLocalRetardedOperator hU U (P i))^N) (source i q)))))) c =
      iteratedFDeriv ℝ k
        (fun q ↦ carrierMultiplication (-(lam i)) (φ i q)
          ((hφ i).continuous.comp (continuous_const.prodMk continuous_id))
          (S i (sourceCutMultiplier χ₃ χ₃.continuous (bump_norm_le_one χ₃)
            (((P i)^N) (carrierMultiplication (lam i) (φ i q)
              ((hφ i).continuous.comp (continuous_const.prodMk continuous_id)) (datum i q)))))) c := by
  have he : (fun q ↦ carrierMultiplication (-(lam i))
        (totalizedObservationPhase V (φ i) q)
        (continuous_totalizedObservationPhase (hφ i).contDiffOn q)
        (S i (zeroExtend hU (bumpL2 (p := 2) le_rfl χ₃
          (((complexLocalRetardedOperator hU U (P i))^N) (source i q)))))) =ᶠ[𝓝 c]
      (fun q ↦ carrierMultiplication (-(lam i)) (φ i q)
        ((hφ i).continuous.comp (continuous_const.prodMk continuous_id))
        (S i (sourceCutMultiplier χ₃ χ₃.continuous (bump_norm_le_one χ₃)
          (((P i)^N) (carrierMultiplication (lam i) (φ i q)
            ((hφ i).continuous.comp (continuous_const.prodMk continuous_id)) (datum i q)))))) := by
    filter_upwards [hV.mem_nhds hc] with q hq
    have hp : zeroExtend hU
        (((complexLocalRetardedOperator hU U (P i))^N) (source i q)) =
        ((P i)^N) (zeroExtend hU (source i q)) := by
      rw [hP i]
      exact zeroExtend_complex_measured_power hU χ₂ χ₃ χ₂.continuous χ₃.continuous
        (bump_norm_le_one χ₂) (bump_norm_le_one χ₃) hχ₂ (raw i) N (source i q)
    rw [zeroExtend_bump_eq_sourceCutMultiplier, hp, hinitial i q hq]
    simp only [totalizedObservationPhase_of_mem (φ i) hq]
  exact (he.iteratedFDeriv ℝ k).eq_of_nhds

/-- Transfer the proved global finite-word bounds to the literal local
complex powers and totalized observation used by the complete inverse.
The input `hglobal` is the conclusion of
`actual_finite_residual_word_reserved_bounds_of_one_step`; this theorem adds
only the exact original zero-extension identities. The amplitude and natural
reserve, including reserve zero, are unchanged
(`app:ch_response:eq:response-graded-reduced`). -/
theorem local_finite_word_reserved_bounds_of_global
    {U : Set E} (hU : MeasurableSet U) {x : E} (χ₂ χ₃ : ContDiffBump x)
    (hχ₂ : tsupport (χ₂ : E → ℝ) ⊆ U)
    (raw P S : I → H →L[ℂ] H)
    (hP : ∀ i, P i = measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
      (bump_norm_le_one χ₂) (bump_norm_le_one χ₃) (raw i))
    (source : I → Par → LocalL2 U F) (datum : I → Par → H)
    {V : Set Par} (hV : IsOpen V) (lam A K : I → ℝ) (reserve : ℕ)
    (φ : I → Par → E → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (hinitial : ∀ i c, c ∈ V → zeroExtend hU (source i c) =
      carrierMultiplication (lam i) (φ i c)
        ((hφ i).continuous.comp (continuous_const.prodMk continuous_id)) (datum i c))
    (hglobal : ∀ N s k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      ∀ v : Fin k → Par, (∀ l, ‖v l‖ ≤ 1) →
        let word := fun q ↦ carrierMultiplication (-(lam i)) (φ i q)
          ((hφ i).continuous.comp (continuous_const.prodMk continuous_id))
          (S i (sourceCutMultiplier χ₃ χ₃.continuous (bump_norm_le_one χ₃)
            (((P i)^N) (carrierMultiplication (lam i) (φ i q)
              ((hφ i).continuous.comp (continuous_const.prodMk continuous_id)) (datum i q)))))
        MemVectorFourierSobolev (s : ℝ) (iteratedFDeriv ℝ k word c v) ∧
          vectorFourierSobolevNorm (s : ℝ) (iteratedFDeriv ℝ k word c v) ≤
            C * A i * K i ^ (s+k-reserve)) :
    ∀ N s k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      ∀ v : Fin k → Par, (∀ l, ‖v l‖ ≤ 1) →
        let word := fun q ↦ carrierMultiplication (-(lam i))
          (totalizedObservationPhase V (φ i) q)
          (continuous_totalizedObservationPhase (hφ i).contDiffOn q)
          (S i (zeroExtend hU (bumpL2 (p := 2) le_rfl χ₃
            (((complexLocalRetardedOperator hU U (P i))^N) (source i q)))))
        MemVectorFourierSobolev (s : ℝ) (iteratedFDeriv ℝ k word c v) ∧
          vectorFourierSobolevNorm (s : ℝ) (iteratedFDeriv ℝ k word c v) ≤
            C * A i * K i ^ (s+k-reserve) := by
  intro N s k
  obtain ⟨C, hC, hb⟩ := hglobal N s k
  refine ⟨C, hC, ?_⟩
  intro i c hc v hv word
  have he := local_measured_power_parameter_jets_eq_global hU χ₂ χ₃ hχ₂ raw P S hP
    source datum hV lam φ hφ hinitial N k i hc
  dsimp only [word]
  rw [he]
  exact hb i c hc v hv

end JanetCartan.FixedDomainInverse.FiniteResidualWordProfiles
