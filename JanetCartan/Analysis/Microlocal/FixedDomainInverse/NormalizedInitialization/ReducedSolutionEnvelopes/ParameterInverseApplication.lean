module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.Assembly
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.ParameterAssembly
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.OriginalObservedRemainders

/-!
# The same complex inverse with a natural parameter reserve

Apply the differentiated finite Neumann identity to the literal complex
solver, residual powers, recut source, and primary demodulation. The original
source producer supplies norm-smoothness, and
`exists_observed_parameter_remainders_of_original_profiles` supplies the
displayed actual remainder input. The independent characteristic/reflected/
full-elliptic finite-word producer must supply its displayed bound.

This deduction retains natural subtraction in the derivative reserve and
returns the exact Fourier class consumed by original-cell reconstruction.
It does not construct the finite-word estimates or add a tame scalar estimate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff NNReal ENNReal JanetCartan.RegularSector.Realization

namespace JanetCartan.FixedDomainInverse

open LocalSobolev Pseudodifferential SmallSupport
open RegularSector.Realization ResponseTransfer ResponseTransfer.Complement
open ObservedParameterRemainders

variable {n r : ℕ} {ι : Type*} {Par : Type}
  [NormedAddCommGroup Par] [NormedSpace ℝ Par]
local notation "E" => Euclidean n
local notation "CF" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp CF 2 (volume : Measure E)

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The actual finite complex residual powers and the constructed observed
remainder give the same complete inverse its ordered Fourier envelopes.
The original natural reserve is unchanged, including low total orders.
Only the independent finite-word estimate remains an analytic input beyond
the original-profile remainder producer
(`app:ch_regular:eq:finite-neumann-identity`,
`app:ch_response:eq:response-graded-reduced`). -/
theorem complex_inverse_parameter_envelopes_of_actual_finite_words
    (U : Set E) (hU : MeasurableSet U) {x : E} (χ₃ : ContDiffBump x)
    (R : ι → LocalL2 U CF →L[ℂ] LocalL2 U CF) (hR : ∀ i, ‖R i‖ < 1)
    (S : ι → H →L[ℂ] H) (source : ι → Par → LocalL2 U CF)
    (V : Set Par) (hV : IsOpen V) (hsource : ∀ i, ContDiffOn ℝ ∞ (source i) V)
    (ρ A K : ι → ℝ) (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 1 ≤ K i) (reserve : ℕ)
    (φ : ι → Par → E → ℝ)
    (hφ : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (φ i)) (V ×ˢ univ))
    {X : Set E} (hX : IsCompact X) (hsφ : ∀ i c, c ∈ V → tsupport (φ i c) ⊆ X)
    (hfinite : ∀ j s k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      ∀ v : Fin k → Par, (∀ l, ‖v l‖ ≤ 1) →
        let word := fun q ↦ carrierMultiplication (-(ρ i))
          (totalizedObservationPhase V (φ i) q)
          (continuous_totalizedObservationPhase (hφ i) q)
          (S i (zeroExtend hU (bumpL2 (p := 2) le_rfl χ₃ (((R i)^j) (source i q)))))
        MemVectorFourierSobolev (s : ℝ) (iteratedFDeriv ℝ k word c v) ∧
          vectorFourierSobolevNorm (s : ℝ) (iteratedFDeriv ℝ k word c v) ≤
            C * A i * K i ^ (s+k-reserve))
    (hrem : ∀ s k, ∃ (N : ℕ) (D : ℝ), 0 ≤ D ∧ ∀ i c, c ∈ V →
      ∀ v : Fin k → Par, (∀ j, ‖v j‖ ≤ 1) →
        let u := fun q ↦ complexNeumannInverse (R i) (hR i)
          (((R i)^(N+s)) (source i q))
        let observed := fun q ↦ carrierMultiplication (-(ρ i))
          (totalizedObservationPhase V (φ i) q)
          (continuous_totalizedObservationPhase (hφ i) q)
          (S i (zeroExtend hU (bumpL2 (p := 2) le_rfl χ₃ (u q))))
        MemVectorFourierSobolev (s : ℝ) (iteratedFDeriv ℝ k observed c v) ∧
          vectorFourierSobolevNorm (s : ℝ) (iteratedFDeriv ℝ k observed c v) ≤ D * A i) :
    ∀ s k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      ∀ v : Fin k → Par, (∀ l, ‖v l‖ ≤ 1) →
        let solution := fun q ↦ carrierMultiplication (-(ρ i))
          (totalizedObservationPhase V (φ i) q)
          (continuous_totalizedObservationPhase (hφ i) q)
          (S i (zeroExtend hU (bumpL2 (p := 2) le_rfl χ₃
            (complexNeumannInverse (R i) (hR i) (source i q)))))
        MemVectorFourierSobolev (s : ℝ) (iteratedFDeriv ℝ k solution c v) ∧
          vectorFourierSobolevNorm (s : ℝ) (iteratedFDeriv ℝ k solution c v) ≤
            C * A i * K i ^ (s+k-reserve) := by
  let Rreal := fun i ↦ (R i).restrictScalars ℝ
  let Inv := fun i ↦ (complexNeumannInverse (R i) (hR i)).restrictScalars ℝ
  let observe : ι → Par → LocalL2 U CF →ₗ[ℝ] H := fun i q ↦
    (((carrierMultiplication (-(ρ i)) (totalizedObservationPhase V (φ i) q)
      (continuous_totalizedObservationPhase (hφ i) q)).restrictScalars ℝ).comp
      (((S i).restrictScalars ℝ).comp
        ((zeroExtend (F := CF) (p := 2) hU).toContinuousLinearMap.comp
          (bumpL2 (F := CF) (μ := volume.restrict U) (p := 2) le_rfl χ₃)))).toLinearMap
  have hInv (i : ι) : Inv i * (1 + Rreal i) = 1 :=
    neumannInverse_mul_add ((R i).restrictScalars ℝ) (by simpa using hR i)
  have hsTot (i : ι) (q : Par) (hq : q ∈ V) :
      tsupport (totalizedObservationPhase V (φ i) q) ⊆ X := by
    rw [totalizedObservationPhase_of_mem (φ i) hq]
    exact hsφ i q hq
  have hsmooth (i : ι) (T : LocalL2 U CF →L[ℝ] LocalL2 U CF) :
      ContDiffOn ℝ ∞ (fun q ↦ observe i q (T (source i q))) V :=
    contDiffOn_demodulated_fixed_local_operator hU χ₃ hV hX (ρ i)
      (totalizedObservationPhase V (φ i))
      (continuous_totalizedObservationPhase (hφ i))
      (contDiffOn_totalizedObservationPhase (hφ i)) (hsTot i) (S i) T (source i) (hsource i)
  have hfinite' : ∀ j s k, ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      ∀ v : Fin k → Par, (∀ l, ‖v l‖ ≤ 1) →
        let z := iteratedFDeriv ℝ k (fun q ↦ observe i q (((Rreal i)^j) (source i q))) c v
        z ∈ vectorFourierSobolevScale.level s ∧
          vectorFourierSobolevScale.gradeNorm s z ≤ C * A i * K i ^ (s+k-reserve) := by
    intro j s k
    obtain ⟨C, hC, hf⟩ := hfinite j s k
    refine ⟨C, hC, ?_⟩
    intro i c hc v hv z
    have he : (fun q ↦ observe i q (((Rreal i)^j) (source i q))) =
        (fun q ↦ observe i q (((R i)^j) (source i q))) := by
      funext q
      exact congrArg (observe i q) (complex_operator_power_restrictScalars_apply (R i) j _)
    obtain ⟨hm, hb⟩ := hf i c hc v hv
    have hz : z = iteratedFDeriv ℝ k
        (fun q ↦ observe i q (((R i)^j) (source i q))) c v :=
      congrArg (fun f ↦ iteratedFDeriv ℝ k f c v) he
    rw [hz]
    exact ⟨hm, (vectorFourierSobolevScale_gradeNorm s hm).le.trans hb⟩
  have hrem' : ∀ s k, ∃ (depth : ℕ) (D : ℝ), 0 ≤ D ∧ ∀ i c, c ∈ V →
      ∀ v : Fin k → Par, (∀ l, ‖v l‖ ≤ 1) →
        let z := iteratedFDeriv ℝ k
          (fun q ↦ observe i q (Inv i (((Rreal i)^depth) (source i q)))) c v
        z ∈ vectorFourierSobolevScale.level s ∧ vectorFourierSobolevScale.gradeNorm s z ≤ D * A i := by
    intro s k
    obtain ⟨N, D, hD, hr⟩ := hrem s k
    refine ⟨N+s, D, hD, ?_⟩
    intro i c hc v hv z
    have he : (fun q ↦ observe i q (Inv i (((Rreal i)^(N+s)) (source i q)))) =
        (fun q ↦ observe i q (Inv i (((R i)^(N+s)) (source i q)))) := by
      funext q
      exact congrArg (fun w ↦ observe i q (Inv i w))
        (complex_operator_power_restrictScalars_apply (R i) (N+s) _)
    obtain ⟨hm, hb⟩ := hr i c hc v hv
    have hz : z = iteratedFDeriv ℝ k
        (fun q ↦ observe i q (Inv i (((R i)^(N+s)) (source i q)))) c v :=
      congrArg (fun f ↦ iteratedFDeriv ℝ k f c v) he
    rw [hz]
    exact ⟨hm, (vectorFourierSobolevScale_gradeNorm s hm).le.trans hb⟩
  have hfull := parameter_inverse_reserved_envelope_of_finite_remainders
    vectorFourierSobolevScale Rreal Inv hInv observe source V hV A K reserve hA hK
    (fun i j ↦ hsmooth i ((Rreal i)^j))
    (fun i depth ↦ hsmooth i ((Inv i).comp ((Rreal i)^depth))) hfinite' hrem'
  intro s k
  obtain ⟨C, hC, hf⟩ := hfull s k
  refine ⟨C, hC, ?_⟩
  intro i c hc v hv solution
  obtain ⟨hm, hb⟩ := hf i c hc v hv
  exact ⟨hm, (vectorFourierSobolevScale_gradeNorm s hm).symm.le.trans hb⟩

end JanetCartan.FixedDomainInverse
