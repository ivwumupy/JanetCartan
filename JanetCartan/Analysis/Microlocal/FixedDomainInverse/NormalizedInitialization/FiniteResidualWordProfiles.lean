module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualWordProfiles.Induction
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualWordProfiles.LocalIdentification

/-!
# The same finite residual powers in the inverse envelope

Reapply the quantitative one-step estimates to the actual supported smooth
representatives of the complete measured residual powers. A final application
uses the SAME solver after the original input mask. The original amplitude,
parameter support, and natural derivative reserve are unchanged, and constants
precede the history and all unit parameter directions.

This deduction produces the global finite-word input of
`complex_inverse_parameter_envelopes_of_actual_finite_words`.
`FiniteResidualEnvelopes.Quadratures` and the measured zero-extension power
identities supply its local real/complex identification. The quantitative
one-step hypotheses still require their actual analytic producers; this module
does not assert the unconditional existence theorem.

The original global smooth compact phase is produced by
`exists_initialized_retainedPhaseExtension_joint_profiles`; the power
construction neither chooses nor extends that phase.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.FixedDomainInverse.FiniteResidualWordProfiles

open Pseudodifferential FourierIntegral ResponseTransfer ResponseTransfer.Complement
open FourierIntegral.LowBounds
open RegularSector.FiniteAssembly
open FiniteChain.Graph.KernelLimits
open ResponseTransfer.DirectEvolution.AnnularSobolev
open ResponseTransfer.DirectEvolution.CompactTransfer

variable {d r : ℕ} {I J : Type*} [Fintype J]
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

/-- One-step estimates for the actual measured letters and the SAME final
solver imply the ordered and direction-uniform estimates of every complete
residual power. The original ordinary tame bounds construct all intermediate
smooth representatives. The final expression retains the literal physical
power, source mask, solver, and demodulation; normalized halves and whole
conjugates belong to the supplied original letters and are never replaced.
Consumer: `hfinite` of
`complex_inverse_parameter_envelopes_of_actual_finite_words`
(`app:ch_regular:lem:finite-chain`,
`app:ch_response:eq:response-graded-reduced`). -/
theorem actual_finite_residual_word_reserved_bounds_of_one_step
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (he : MeasurePreserving (graphInputCoordinates e) volume volume)
    {V Csrc : Set Par} (hV : IsOpen V)
    (χout χin : E → ℝ) (ho : Continuous χout) (hi : Continuous χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1)
    (hS : IsCompact (tsupport χout))
    (raw : I → J → H →L[ℂ] H) (P : I → H →L[ℂ] H)
    (hP : ∀ i, P i = ∑ j, measuredOperator χout χin ho hi hob hib (raw i j))
    (hordinary : ∀ i j (s : ℕ), ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : graphTestSpace (d+1) r,
        MemVectorFourierSobolev (s : ℝ)
          (measuredOperator χout χin ho hi hob hib (raw i j) (graphTestToLp u)) ∧
        vectorFourierSobolevNorm (s : ℝ)
          (measuredOperator χout χin ho hi hob hib (raw i j) (graphTestToLp u)) ≤
            C * vectorFourierSobolevNorm (t : ℝ) (graphTestToLp u))
    (lam A K : I → ℝ) (reserve : ℕ)
    (φ : I → Par → E → ℝ)
    (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    {X : Set E} (hX : IsCompact X) (hφs : ∀ i c, c ∈ V → tsupport (φ i c) ⊆ X)
    (hstep : ∀ (a : I → E × Par → F) (ha : ∀ i, ContDiff ℝ ∞ (a i))
      (has : ∀ i q, q.1 ∉ tsupport χout → a i q = 0),
      (∀ i c, c ∉ Csrc → ∀ y, a i (y,c) = 0) →
      ∀ Csource : ℕ → ℕ → ℝ, (∀ l s, 0 ≤ Csource l s) →
      (∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
        let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
        ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
          vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤
            Csource l s * A i * K i ^ (s+l-reserve)) →
      ∀ j (ps : List Par), (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ q : I × V,
          let value := orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps
            (fun c ↦ demodulatedL2Operator (lam q.1) (φ q.1 c)
              ((hφ q.1).continuous.comp (continuous_const.prodMk continuous_id))
              (measuredOperator χout χin ho hi hob hib (raw q.1 j))
              (graphTestToLp (vectorOriginalDatumTest (a q.1) (ha q.1) hS (has q.1) [] c))) q.2
          MemVectorFourierSobolev (s : ℝ) value ∧ vectorFourierSobolevNorm (s : ℝ) value ≤
            C * A q.1 * K q.1 ^ (s+ps.length-reserve))
    (S : I → H →L[ℂ] H)
    (hsolverStep : ∀ (a : I → E × Par → F) (ha : ∀ i, ContDiff ℝ ∞ (a i))
      (has : ∀ i q, q.1 ∉ tsupport χout → a i q = 0),
      (∀ i c, c ∉ Csrc → ∀ y, a i (y,c) = 0) →
      ∀ Csource : ℕ → ℕ → ℝ, (∀ l s, 0 ≤ Csource l s) →
      (∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
        let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
        ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
          vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤
            Csource l s * A i * K i ^ (s+l-reserve)) →
      ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ q : I × V,
          let value := orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps
            (fun c ↦ demodulatedL2Operator (lam q.1) (φ q.1 c)
              ((hφ q.1).continuous.comp (continuous_const.prodMk continuous_id))
              ((S q.1).comp (sourceCutMultiplier χin hi hib))
              (graphTestToLp (vectorOriginalDatumTest (a q.1) (ha q.1) hS (has q.1) [] c))) q.2
          MemVectorFourierSobolev (s : ℝ) value ∧ vectorFourierSobolevNorm (s : ℝ) value ≤
            C * A q.1 * K q.1 ^ (s+ps.length-reserve))
    (a₀ : I → E × Par → F) (ha₀ : ∀ i, ContDiff ℝ ∞ (a₀ i))
    (has₀ : ∀ i q, q.1 ∉ tsupport χout → a₀ i q = 0)
    (hap₀ : ∀ i c, c ∉ Csrc → ∀ y, a₀ i (y,c) = 0)
    (C₀ : ℕ → ℕ → ℝ) (hC₀ : ∀ l s, 0 ≤ C₀ l s)
    (hfourier₀ : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a₀ i (y,q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ C₀ l s * A i * K i ^ (s+l-reserve)) :
    let word := fun N i c ↦ carrierMultiplication (-(lam i)) (φ i c)
      ((hφ i).continuous.comp (continuous_const.prodMk continuous_id))
      (S i (sourceCutMultiplier χin hi hib (((P i)^N)
        (carrierMultiplication (lam i) (φ i c)
          ((hφ i).continuous.comp (continuous_const.prodMk continuous_id))
          (graphTestToLp (vectorOriginalDatumTest (a₀ i) (ha₀ i) hS (has₀ i) [] c))))))
    ∀ N : ℕ, (∀ i, ContDiffOn ℝ ∞ (word N i) V) ∧
      (∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ q : I × V,
          let value := orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (word N q.1) q.2
          MemVectorFourierSobolev (s : ℝ) value ∧ vectorFourierSobolevNorm (s : ℝ) value ≤
            C * A q.1 * K q.1 ^ (s+ps.length-reserve)) ∧
      ∀ s k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
        ∀ v : Fin k → Par, (∀ l, ‖v l‖ ≤ 1) →
          MemVectorFourierSobolev (s : ℝ) (iteratedFDeriv ℝ k (word N i) c v) ∧
            vectorFourierSobolevNorm (s : ℝ) (iteratedFDeriv ℝ k (word N i) c v) ≤
              C * A i * K i ^ (s+k-reserve) := by
  intro word N
  obtain ⟨a, ha, has, hap, hae, Csource, hCsource, hfourier⟩ :=
    exists_actual_residual_power_reserved_source_profiles e he hV χout χin ho hi hob hib hS
      raw P hP hordinary lam A K reserve φ hφ hstep a₀ ha₀ has₀ hap₀ C₀ hC₀ hfourier₀ N
  let next := fun i c ↦ demodulatedL2Operator (lam i) (φ i c)
    ((hφ i).continuous.comp (continuous_const.prodMk continuous_id))
    ((S i).comp (sourceCutMultiplier χin hi hib))
    (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))
  have hnext i : next i = word N i := by
    funext c
    have haClass : graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c) =
        demodulatedL2Operator (lam i) (φ i c)
          ((hφ i).continuous.comp (continuous_const.prodMk continuous_id)) ((P i)^N)
          (graphTestToLp (vectorOriginalDatumTest (a₀ i) (ha₀ i) hS (has₀ i) [] c)) := by
      apply Lp.ext
      have ht : (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c) : E → F)
          =ᵐ[volume] fun y ↦ a i (y,c) := by
        simpa only [originalDatumDerivative, orderedTransferAction] using
          vectorOriginalDatumTest_toLp_ae (a i) (ha i) hS (has i) [] c
      exact ht.trans (hae i c)
    dsimp only [next]
    rw [haClass, demodulated_comp_apply_same_phase]
    rfl
  have hregular i : ContDiffOn ℝ ∞ (word N i) V :=
    contDiffOn_demodulated_supported_operator hV hS hX (a₀ i) (ha₀ i) (has₀ i)
      (lam i) (φ i) (hφ i) (hφs i)
      (((S i).comp (sourceCutMultiplier χin hi hib)).comp ((P i)^N))
  have hword : ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q : I × V,
        let value := orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (word N q.1) q.2
        MemVectorFourierSobolev (s : ℝ) value ∧ vectorFourierSobolevNorm (s : ℝ) value ≤
          C * A q.1 * K q.1 ^ (s+ps.length-reserve) := by
    have h := hsolverStep a ha has hap Csource hCsource hfourier
    change ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q : I × V,
        let value := orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (next q.1) q.2
        MemVectorFourierSobolev (s : ℝ) value ∧ vectorFourierSobolevNorm (s : ℝ) value ≤
          C * A q.1 * K q.1 ^ (s+ps.length-reserve) at h
    simpa only [hnext] using h
  exact ⟨hregular, hword, uniform_jets_of_ordered_reserved_bounds hV (word N) hregular A K reserve hword⟩

end JanetCartan.FixedDomainInverse.FiniteResidualWordProfiles
