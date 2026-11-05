module

public import JanetCartan.Analysis.Sobolev.Local.Fourier.RealInteger
public import JanetCartan.Analysis.Sobolev.Local.Scale.Graded

/-!
# Actual restriction scale for complete residual localization

The consumer `finiteChain_observation_rapidDecayAt` uses a `GradedScale`.
Here the existing Fourier-to-weak-jet comparison is connected to the existing
restriction scale. The comparison constant depends only on dimension, channel
count and Sobolev order. In particular it changes neither loss exponent in
`app:ch_regular:eq:chain-tail` and does not change any operator or localizer.
These are comparison deductions, not producers of the Fourier estimates.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization

open LocalSobolev Pseudodifferential RegularSector.Realization

/-- The genuine complex restriction scale is controlled by the actual
Fourier Sobolev norm. Consumer: the leakage and terminal-factor inputs to
`finiteChain_observation_rapidDecayAt` (`app:ch_regular:eq:chain-tail`). -/
theorem exists_restrictionScale_fourier_comparison (n r m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (EuclideanSpace ℝ (Fin n))) (hU : MeasurableSet U)
      (u : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (v : LocalL2 U (EuclideanSpace ℂ (Fin r))),
      MemVectorFourierSobolev (m : ℝ) u →
      (u : EuclideanSpace ℝ (Fin n) → _) =ᵐ[volume.restrict U] v →
      v ∈ (restrictionSobolevScale U (EuclideanSpace ℂ (Fin r)) hU).level m ∧
      (restrictionSobolevScale U (EuclideanSpace ℂ (Fin r)) hU).gradeNorm m v ≤
        C * vectorFourierSobolevNorm (m : ℝ) u := by
  obtain ⟨C, hC, h⟩ := vector_restrictionSobolev_nat_bounds n r m
  refine ⟨C, hC, fun U hU u v hu huv ↦ ?_⟩
  obtain ⟨hv, hb⟩ := h u hu U v huv
  exact ⟨hv, (restrictionSobolevScale_gradeNorm hU hv).le.trans hb⟩

/-- The real restriction scale uses the literal complex inclusion of the
same real output. Thus real compression of the physical signed pairing can
feed the same finite-chain consumer, without substituting a norm scale
(`app:ch_regular:eq:chain-tail`, `app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_real_restrictionScale_fourier_comparison (n r m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (EuclideanSpace ℝ (Fin n))) (hU : MeasurableSet U)
      (u : Lp (EuclideanSpace ℝ (Fin r)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (v : LocalL2 U (EuclideanSpace ℝ (Fin r))),
      MemVectorFourierSobolev (m : ℝ) (l2ComplexInclusion volume u) →
      (u : EuclideanSpace ℝ (Fin n) → _) =ᵐ[volume.restrict U] v →
      v ∈ (restrictionSobolevScale U (EuclideanSpace ℝ (Fin r)) hU).level m ∧
      (restrictionSobolevScale U (EuclideanSpace ℝ (Fin r)) hU).gradeNorm m v ≤
        C * vectorFourierSobolevNorm (m : ℝ) (l2ComplexInclusion volume u) := by
  obtain ⟨C, hC, h⟩ := real_restrictionSobolev_nat_bounds n r m
  refine ⟨C, hC, fun U hU u v hu huv ↦ ?_⟩
  obtain ⟨hv, hb⟩ := h u hu U v huv
  exact ⟨hv, (restrictionSobolevScale_gradeNorm hU hv).le.trans hb⟩

/-- Transfer a whole family of actual Fourier leakage estimates to the
restriction scale, retaining its fixed frequency and coefficient losses and
the very same outputs at every accuracy. This supplies the precise form of
`hleak` or `hBnear` in `finiteChain_observation_rapidDecayAt`; the Fourier
estimate itself must be produced by the factor localization theorem
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem restrictionScale_bounds_of_fourier_bounds
    {ι X : Type*} [NormedAddCommGroup X] (n r m : ℕ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : MeasurableSet U)
    (u : ι → X → Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (v : ι → X → LocalL2 U (EuclideanSpace ℂ (Fin r)))
    (huv : ∀ i x, (u i x : EuclideanSpace ℝ (Fin n) → _) =ᵐ[volume.restrict U] v i x)
    (ρ L : ι → ℝ) (c : ℝ) (b : ℕ)
    (h : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x,
      MemVectorFourierSobolev (m : ℝ) (u i x) ∧
      vectorFourierSobolevNorm (m : ℝ) (u i x) ≤
        C * (ρ i) ^ c * L i ^ b * (L i / ρ i) ^ q * ‖x‖) :
    ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x,
      v i x ∈ (restrictionSobolevScale U (EuclideanSpace ℂ (Fin r)) hU).level m ∧
      (restrictionSobolevScale U (EuclideanSpace ℂ (Fin r)) hU).gradeNorm m (v i x) ≤
        C * (ρ i) ^ c * L i ^ b * (L i / ρ i) ^ q * ‖x‖ := by
  obtain ⟨K, hK, hc⟩ := exists_restrictionScale_fourier_comparison n r m
  intro q
  obtain ⟨C, hC, hbound⟩ := h q
  refine ⟨K * C, mul_nonneg hK.le hC, fun i x ↦ ?_⟩
  obtain ⟨hm, hb⟩ := hc U hU (u i x) (v i x) (hbound i x).1 (huv i x)
  refine ⟨hm, hb.trans ?_⟩
  convert mul_le_mul_of_nonneg_left (hbound i x).2 hK.le using 1
  ring

/-- Real-output form of `restrictionScale_bounds_of_fourier_bounds`. The
literal complex inclusion supplies Fourier regularity of the physical paired
output, and the same real restriction scale feeds the finite-chain consumer
(`app:ch_regular:eq:chain-tail`). -/
theorem real_restrictionScale_bounds_of_fourier_bounds
    {ι X : Type*} [NormedAddCommGroup X] (n r m : ℕ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : MeasurableSet U)
    (u : ι → X → Lp (EuclideanSpace ℝ (Fin r)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (v : ι → X → LocalL2 U (EuclideanSpace ℝ (Fin r)))
    (huv : ∀ i x, (u i x : EuclideanSpace ℝ (Fin n) → _) =ᵐ[volume.restrict U] v i x)
    (ρ L : ι → ℝ) (c : ℝ) (b : ℕ)
    (h : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x,
      MemVectorFourierSobolev (m : ℝ) (l2ComplexInclusion volume (u i x)) ∧
      vectorFourierSobolevNorm (m : ℝ) (l2ComplexInclusion volume (u i x)) ≤
        C * (ρ i) ^ c * L i ^ b * (L i / ρ i) ^ q * ‖x‖) :
    ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x,
      v i x ∈ (restrictionSobolevScale U (EuclideanSpace ℝ (Fin r)) hU).level m ∧
      (restrictionSobolevScale U (EuclideanSpace ℝ (Fin r)) hU).gradeNorm m (v i x) ≤
        C * (ρ i) ^ c * L i ^ b * (L i / ρ i) ^ q * ‖x‖ := by
  obtain ⟨K, hK, hc⟩ := exists_real_restrictionScale_fourier_comparison n r m
  intro q
  obtain ⟨C, hC, hbound⟩ := h q
  refine ⟨K * C, mul_nonneg hK.le hC, fun i x ↦ ?_⟩
  obtain ⟨hm, hb⟩ := hc U hU (u i x) (v i x) (hbound i x).1 (huv i x)
  refine ⟨hm, hb.trans ?_⟩
  convert mul_le_mul_of_nonneg_left (hbound i x).2 hK.le using 1
  ring

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
