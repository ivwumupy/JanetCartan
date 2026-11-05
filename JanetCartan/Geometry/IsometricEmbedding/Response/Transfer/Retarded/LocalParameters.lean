module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.LocalProfile
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.ParameterRealization

/-!
# Parameter derivatives of the literal retarded factors in local Sobolev spaces

For the parameter paragraph of `app:ch_response:thm:response-literal-transfer`,
the actual local L² derivatives are represented by smooth supported fields.
The completed retarded operators commute with these derivatives, and the
proved local norm estimate preserves total grade `s + k`. Frequency and
cutoffs stay fixed during differentiation. Only classical joint smoothness,
common compact support, and input envelope estimates are assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.ResponseTransfer

open RetardedSobolev RetardedSobolev.Spaces LocalSobolev ParameterRealization

/-- The zeroth jet of the retarded completion, transported to the actual local
L² space by the Lebesgue-preserving coordinates. This realizes parameter
derivatives in `app:ch_response:thm:response-literal-transfer`. -/
def retardedSobolevToLocalL2 (d s : ℕ) : Ambient d s →L[ℂ]
    LocalL2 (univ : Set (Euclidean (d + 1))) ℂ := by
  let e := Prod.swap ∘ retardedCoordinates d
  have he : MeasurePreserving e (volume.restrict univ) volume := by
    simpa only [Measure.restrict_univ] using measurePreserving_retardedJetCoordinates d
  exact (Lp.compMeasurePreservingₗᵢ ℂ e he).toContinuousLinearMap.comp
    ((ContinuousLinearMap.proj (zeroIndex d s)).comp (sobolevSubmodule s volume).subtypeL)

/-- The completed-space realization agrees with the literal smooth formula
(`app:ch_response:eq:fixed-factor-transfer`). -/
@[simp] theorem retardedSobolevToLocalL2_ofTest {d : ℕ} (s : ℕ) (f : Test d) :
    retardedSobolevToLocalL2 d s (ofTest s volume f) = retardedTestToLocalL2 f := by
  change Lp.compMeasurePreserving _ _ ((jet_memLp volume (zeroIndex d s) f).toLp _) = _
  rw [Lp.toLp_compMeasurePreserving]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall (fun x ↦ by simp [jet_zeroIndex, retardedTestFunction])

section ClassicalParameters

variable {p d : ℕ} {U : Set (Euclidean p)} (hU : IsOpen U)
  {S : Set (ℝ × (Fin d → ℝ))} (hS : IsCompact S)
  (f : Euclidean p → Test d)
  (hf : ContDiffOn ℝ ∞ (fun z ↦ (f z.1).val z.2) (U ×ˢ univ))
  (hs : ∀ c ∈ U, tsupport (f c).val ⊆ S)

include hU hS hf hs

/-- Classical joint smoothness and common compact support give actual local
L² smoothness at every finite parameter order
(`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiffAt_retardedTestToLocalL2 (k : ℕ) {c : Euclidean p} (hc : c ∈ U) :
    ContDiffAt ℝ k (fun a ↦ retardedTestToLocalL2 (f a)) c := by
  have hh := ((retardedSobolevToLocalL2 d 0).restrictScalars ℝ).contDiff.contDiffAt.comp c
    (contDiffAt_ofTest_of_commonCompactSupport hU hS f hf hs 0 k hc)
  change ContDiffAt ℝ k
    (fun a ↦ retardedSobolevToLocalL2 d 0 (ofTest 0 volume (f a))) c at hh
  simpa only [retardedSobolevToLocalL2_ofTest] using hh

/-- The actual local L² parameter derivative is the L² class of the actual
pointwise derivative field, with spatial and parameter orders unchanged
(`app:ch_response:thm:response-literal-transfer`). -/
theorem iteratedFDeriv_retardedTestToLocalL2_eq (k : ℕ) (v : Fin k → Euclidean p)
    (c : Euclidean p) (hc : c ∈ U) :
    iteratedFDeriv ℝ k (fun a ↦ retardedTestToLocalL2 (f a)) c v =
      retardedTestToLocalL2
        (parameterTest hU hS (fun a ↦ (f a).val) hf hs k v c hc) := by
  have he := congrArg (fun m ↦ m v)
    (((retardedSobolevToLocalL2 d 0).restrictScalars ℝ).iteratedFDeriv_comp_left
      (contDiffAt_ofTest_of_commonCompactSupport hU hS f hf hs 0 k hc) le_rfl)
  change iteratedFDeriv ℝ k
    (fun a ↦ retardedSobolevToLocalL2 d 0 (ofTest 0 volume (f a))) c v =
      retardedSobolevToLocalL2 d 0
        (iteratedFDeriv ℝ k (fun a ↦ ofTest 0 volume (f a)) c v) at he
  simpa only [retardedSobolevToLocalL2_ofTest,
    iteratedFDeriv_ofTest_eq_ofTest_parameterTest hU hS f hf hs 0 k v c hc] using he

private theorem iteratedFDeriv_local_operator_eq
    (T : Ambient d 0 →L[ℂ] Ambient d 0) (t : Test d → Test d)
    (ht : ∀ g, T (ofTest 0 volume g) = ofTest 0 volume (t g))
    (k : ℕ) (v : Fin k → Euclidean p) (c : Euclidean p) (hc : c ∈ U) :
    iteratedFDeriv ℝ k (fun a ↦ retardedTestToLocalL2 (t (f a))) c v =
      retardedTestToLocalL2
        (t (parameterTest hU hS (fun a ↦ (f a).val) hf hs k v c hc)) := by
  let L := (retardedSobolevToLocalL2 d 0).comp T
  have hL (g : Test d) : L (ofTest 0 volume g) = retardedTestToLocalL2 (t g) := by
    simp only [L, ContinuousLinearMap.comp_apply, ht, retardedSobolevToLocalL2_ofTest]
  have he := congrArg (fun m ↦ m v) ((L.restrictScalars ℝ).iteratedFDeriv_comp_left
    (contDiffAt_ofTest_of_commonCompactSupport hU hS f hf hs 0 k hc) le_rfl)
  change iteratedFDeriv ℝ k (fun a ↦ L (ofTest 0 volume (f a))) c v =
    L (iteratedFDeriv ℝ k (fun a ↦ ofTest 0 volume (f a)) c v) at he
  simpa only [hL,
    iteratedFDeriv_ofTest_eq_ofTest_parameterTest hU hS f hf hs 0 k v c hc] using he

/-- Parameter differentiation passes through the same lower and upper
weighted integrals, as an equality in actual local L². The parameter-dependent
physical carrier cancels exactly before differentiation; the frequency and
operators remain fixed (`app:ch_response:thm:response-literal-transfer`). -/
theorem RetardedCutoffs.iteratedFDeriv_demodulated_local_eq (W : RetardedCutoffs d)
    (ρ : ℝ) (ζ : Euclidean p → Euclidean d) (k : ℕ) (v : Fin k → Euclidean p)
    (c : Euclidean p) (hc : c ∈ U) :
    let g := parameterTest hU hS (fun a ↦ (f a).val) hf hs k v c hc
    iteratedFDeriv ℝ k
      (fun a ↦ retardedTestToLocalL2 (W.demodulatedLower ρ (ζ a) (f a))) c v =
        retardedTestToLocalL2 (W.lower g) ∧
    iteratedFDeriv ℝ k
      (fun a ↦ retardedTestToLocalL2 (W.demodulatedUpper ρ (ζ a) (f a))) c v =
        retardedTestToLocalL2 (W.upper g) := by
  obtain ⟨_, _, L, V, _, _, hL, hV, _⟩ :=
    exists_retarded_sobolev_extensions W.lowerEndpoint W.upperEndpoint W.endpoints_le
      0 W.input W.output W.input_smooth W.output_smooth W.input_compact W.output_compact
      W.input_support_strip W.output_support_strip
  constructor
  · simpa only [RetardedCutoffs.demodulatedLower_eq] using
      iteratedFDeriv_local_operator_eq hU hS f hf hs L W.lower hL k v c hc
  · simpa only [RetardedCutoffs.demodulatedUpper_eq] using
      iteratedFDeriv_local_operator_eq hU hS f hf hs V W.upper hV k v c hc

end ClassicalParameters

/-- The local Sobolev parameter profile for both literal retarded factors
(`app:ch_response:thm:response-literal-transfer`). Each fixed word of `k`
parameter directions has total grade `s + k`; constants may depend on this
word, as on the multiindex in the manuscript, but precede the family index and
the parameter. `B` can be any fixed compact parameter box inside `U`.
Classical regularity supplies membership; only input quantitative bounds are
assumed. Frequency and operators are fixed during each differentiation. -/
theorem RetardedCutoffs.demodulated_local_parameter_profile
    {d p : ℕ} (W : RetardedCutoffs d) {ι : Type*}
    {U : Set (Euclidean p)} (hU : IsOpen U)
    {S : Set (ℝ × (Fin d → ℝ))} (hS : IsCompact S)
    (q : ℕ) (B : Set (Euclidean p)) (hB : B ⊆ U)
    (f : ι → Euclidean p → Test d)
    (hsmooth : ∀ i, ContDiffOn ℝ ∞ (fun z ↦ (f i z.1).val z.2) (U ×ˢ univ))
    (hsupport : ∀ i c, c ∈ U → tsupport (f i c).val ⊆ S)
    (ρ : ι → ℝ) (ζ : Euclidean p → Euclidean d) (A K : ι → ℝ)
    (hf : ∀ s k, k ≤ q → ∀ v : Fin k → Euclidean p,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ B →
        (restrictionSobolevScale (univ : Set (Euclidean (d + 1))) ℂ
          MeasurableSet.univ).gradeNorm s
            (iteratedFDeriv ℝ k (fun a ↦ retardedTestToLocalL2 (f i a)) c v) ≤
              C * A i * K i ^ (s + k)) :
    ∀ s k, k ≤ q → ∀ v : Fin k → Euclidean p,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ B →
        let G := restrictionSobolevScale (univ : Set (Euclidean (d + 1))) ℂ
          MeasurableSet.univ
        let l := iteratedFDeriv ℝ k
          (fun a ↦ retardedTestToLocalL2 (W.demodulatedLower (ρ i) (ζ a) (f i a))) c v
        let u := iteratedFDeriv ℝ k
          (fun a ↦ retardedTestToLocalL2 (W.demodulatedUpper (ρ i) (ζ a) (f i a))) c v
        l ∈ G.level s ∧ u ∈ G.level s ∧
          G.gradeNorm s l ≤ C * A i * K i ^ (s + k) ∧
          G.gradeNorm s u ≤ C * A i * K i ^ (s + k) := by
  intro s k hk v
  obtain ⟨D, hD, hb⟩ := W.exists_demodulated_local_norm_bounds s
  obtain ⟨C, hC, hf⟩ := hf s k hk v
  refine ⟨D * C, mul_nonneg hD hC, ?_⟩
  intro i c hc
  dsimp only
  have he := W.iteratedFDeriv_demodulated_local_eq hU hS (f i) (hsmooth i)
    (hsupport i) (ρ i) ζ k v c (hB hc)
  rw [he.1, he.2]
  refine ⟨retardedTestToLocalL2_mem _ s, retardedTestToLocalL2_mem _ s, ?_, ?_⟩
  all_goals
    have hi := hf i c hc
    rw [iteratedFDeriv_retardedTestToLocalL2_eq hU hS (f i) (hsmooth i)
      (hsupport i) k v c (hB hc)] at hi
    have hbound := hb (ρ i) (ζ c)
      (parameterTest hU hS (fun a ↦ (f i a).val) (hsmooth i) (hsupport i) k v c (hB hc))
    simp only [RetardedCutoffs.demodulatedLower_eq,
      RetardedCutoffs.demodulatedUpper_eq] at hbound
  · exact hbound.1.trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hi hD)
  · exact hbound.2.trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hi hD)

end JanetCartan.ResponseTransfer
