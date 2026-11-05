module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Synthesis
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# A countable basis of the full sampling output

This discharges the countable-output-basis input to `BandKernelData.samplingFamily`
and its trace theorems, on literal Euclidean Lebesgue L². No finite-dimensional
output projection or additional separability assumption is introduced.
-/

@[expose] public noncomputable section
namespace JanetCartan.SamplingKernelBounds

/-- A countable Hilbert basis exists on the full Euclidean output used in
`app:ch_waves:eq:sampling-operator-bounds`. -/
theorem exists_countable_outputBasis (n : ℕ) :
    ∃ s : Set (Output n), s.Countable ∧ Nonempty (HilbertBasis s ℂ (Output n)) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨s, b, _⟩ := exists_hilbertBasis ℂ (Output n)
  let : TopologicalSpace s := ⊥
  let : DiscreteTopology s := ⟨rfl⟩
  have hd : Pairwise (fun i j : s ↦ (1 : ℝ) ≤ dist (b i) (b j)) := by
    intro i j hij
    have he : dist (b i) (b j) ^ 2 = 2 := by
      rw [dist_eq_norm, norm_sub_sq (𝕜 := ℂ), b.orthonormal.norm_eq_one,
        b.orthonormal.norm_eq_one, b.orthonormal.inner_eq_zero hij]
      norm_num
    nlinarith [dist_nonneg (x := b i) (y := b j)]
  have : SecondCountableTopology s :=
    (Metric.isClosedEmbedding_of_pairwise_le_dist zero_lt_one hd).isEmbedding.secondCountableTopology
  have : Countable s := countable_of_Lindelof_of_discrete
  exact ⟨s, Set.to_countable s, ⟨b⟩⟩

/-- Index set for a basis of the entire sampling output
(`app:ch_waves:eq:sampling-operator-bounds`). -/
def outputBasisIndex (n : ℕ) : Set (Output n) := (exists_countable_outputBasis n).choose

instance (n : ℕ) : Countable (outputBasisIndex n) :=
  (exists_countable_outputBasis n).choose_spec.1.to_subtype

/-- A fixed countable output basis for the trace and expectation deductions
(`app:ch_waves:eq:sampling-operator-bounds`). -/
def outputHilbertBasis (n : ℕ) : HilbertBasis (outputBasisIndex n) ℂ (Output n) :=
  (exists_countable_outputBasis n).choose_spec.2.some

end JanetCartan.SamplingKernelBounds
