module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Space

/-!
# Completeness of the Fourier Sobolev levels

For `app:ch_background:prop:bg-inverse`, a Sobolev Cauchy sequence converges
both in L² and in weighted coefficient ℓ². Continuous coefficient evaluation
identifies the limits, proving completeness without assuming regularity.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace JanetCartan.PeriodicSobolevSpace

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Each actual Fourier Sobolev space is complete
(`app:ch_background:prop:bg-inverse`). -/
instance completeSpace (s : ℕ) : CompleteSpace (PeriodicSobolevSpace n F s) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro f hf
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete
    ((toL2 s).uniformContinuous.comp_cauchySeq hf)
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete
    ((analysisIsometry s).isometry.uniformContinuous.comp_cauchySeq hf)
  have hcoeff (k : Fin n → ℤ) :
      a k = weightedPeriodicL2FourierCoeff s u k := by
    have h₁ := ((lp.evalCLM ℝ (fun _ : Fin n → ℤ ↦ FourierPair F) 2 k).continuous.tendsto a).comp ha
    have h₂ := (((periodicSobolevWeight s k) •
      periodicL2FourierCoeffCLM (F := F) k).continuous.tendsto u).comp hu
    exact tendsto_nhds_unique h₁ h₂
  have hmem : u ∈ periodicSobolevLevel n F s := by
    change Memℓp (weightedPeriodicL2FourierCoeff s u) 2
    have heq : weightedPeriodicL2FourierCoeff s u = a := (funext hcoeff).symm
    rw [heq]
    exact lp.memℓp a
  let v : PeriodicSobolevSpace n F s := (toLevel s).symm ⟨u, hmem⟩
  have hav : analysisIsometry s v = a := by
    apply lp.ext
    exact (funext hcoeff).symm
  refine ⟨v, (analysisIsometry s).isometry.tendsto_nhds_iff.mpr ?_⟩
  rwa [hav]

end JanetCartan.PeriodicSobolevSpace
