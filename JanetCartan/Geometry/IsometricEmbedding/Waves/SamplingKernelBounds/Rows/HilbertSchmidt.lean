module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Rows.Basic
public import JanetCartan.Analysis.Operator.HilbertSchmidt.Trace

/-! # Exact prefix Hilbert–Schmidt sums for `app:ch_waves:eq:sampling-operator-bounds` -/

@[expose] public noncomputable section
namespace JanetCartan.SamplingKernelBounds
open RawInputRealization

variable {ι : Type*} [Fintype ι] {n : ℕ} {radius : ι → ℝ}
  {κ : ι → Type*} {δ : Type*}

/-- Hilbert–Schmidt summability and the exact squared norm, on any basis of the
same full input. Only the selected bands need be Hilbert–Schmidt
(`app:ch_waves:eq:sampling-operator-bounds`). The actual band hypotheses are
supplied by `BandKernelData.operator_hilbertSchmidt_bound`. -/
theorem prefixRow_hilbertSchmidt (s : Finset ι)
    (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] Output n)
    (c : ∀ i, HilbertBasis (κ i) ℂ (AnnularL2 n (radius i)))
    (b : HilbertBasis δ ℂ (Input n radius))
    (hT : ∀ i ∈ s, IsHilbertSchmidt (c i) (T i)) :
    IsHilbertSchmidt b (prefixRow s T) ∧
      hilbertSchmidtSq b (prefixRow s T) = ∑ i ∈ s, hilbertSchmidtSq (c i) (T i) := by
  obtain ⟨ε, d, _⟩ := exists_hilbertBasis ℂ (Output n)
  have hs : HasSum (fun j ↦ ‖(prefixRow s T).adjoint (d j)‖ ^ 2)
      (∑ i ∈ s, hilbertSchmidtSq (c i) (T i)) := by
    simp_rw [norm_prefixRow_adjoint_sq]
    apply hasSum_sum
    intro i hi
    obtain ⟨ha, he⟩ := isHilbertSchmidt_adjoint (c i) d (T i) (hT i hi)
    exact he ▸ ha.hasSum
  obtain ⟨hr, he⟩ := isHilbertSchmidt_adjoint d b (prefixRow s T).adjoint hs.summable
  rw [ContinuousLinearMap.adjoint_adjoint] at hr he
  exact ⟨hr, he.trans hs.tsum_eq⟩

/-- Compactness of every unchanged prefix on the full Hilbert input
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem isCompactOperator_prefixRow (s : Finset ι)
    (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] Output n)
    (c : ∀ i, HilbertBasis (κ i) ℂ (AnnularL2 n (radius i)))
    (hT : ∀ i ∈ s, IsHilbertSchmidt (c i) (T i)) :
    IsCompactOperator (prefixRow s T) := by
  obtain ⟨δ, b, _⟩ := exists_hilbertBasis ℂ (Input n radius)
  exact (prefixRow_hilbertSchmidt s T c b hT).1.isCompactOperator

/-- Exact positive trace of the prefix normal
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem positiveTrace_prefixRow_normal (s : Finset ι)
    (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] Output n)
    (c : ∀ i, HilbertBasis (κ i) ℂ (AnnularL2 n (radius i)))
    (d : HilbertBasis δ ℂ (Output n))
    (hT : ∀ i ∈ s, IsHilbertSchmidt (c i) (T i)) :
    positiveTrace d (prefixRow s T ∘L (prefixRow s T).adjoint) =
      ∑ i ∈ s, hilbertSchmidtSq (c i) (T i) := by
  obtain ⟨ε, b, _⟩ := exists_hilbertBasis ℂ (Input n radius)
  obtain ⟨hr, he⟩ := prefixRow_hilbertSchmidt s T c b hT
  rw [positiveTrace_normal_eq b d _ hr, he]

/-- Every finite-dimensional output compression has the same trace budget
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem trace_finiteCompression_prefixRow_normal_le (s : Finset ι)
    (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] Output n)
    (c : ∀ i, HilbertBasis (κ i) ℂ (AnnularL2 n (radius i)))
    (hT : ∀ i ∈ s, IsHilbertSchmidt (c i) (T i))
    (U : Submodule ℂ (Output n)) [FiniteDimensional ℂ U] :
    RCLike.re (LinearMap.trace ℂ U
      (finiteCompression U (prefixRow s T ∘L (prefixRow s T).adjoint)).toLinearMap) ≤
        ∑ i ∈ s, hilbertSchmidtSq (c i) (T i) := by
  obtain ⟨ε, b, _⟩ := exists_hilbertBasis ℂ (Input n radius)
  obtain ⟨hr, he⟩ := prefixRow_hilbertSchmidt s T c b hT
  exact (trace_finiteCompression_normal_le b _ hr U).trans_eq he

/-- Continuity of the exact row Hilbert–Schmidt square follows from continuity
of the band squares. The actual producer is
`BandKernelData.continuous_hilbertSchmidtSq_operator`
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem continuous_hilbertSchmidtSq_prefixRow {P : Type*} [TopologicalSpace P]
    (s : Finset ι) (T : ∀ i, P → AnnularL2 n (radius i) →L[ℂ] Output n)
    (c : ∀ i, HilbertBasis (κ i) ℂ (AnnularL2 n (radius i)))
    (b : HilbertBasis δ ℂ (Input n radius))
    (hT : ∀ p i, i ∈ s → IsHilbertSchmidt (c i) (T i p))
    (hc : ∀ i ∈ s, Continuous (fun p ↦ hilbertSchmidtSq (c i) (T i p))) :
    Continuous (fun p ↦ hilbertSchmidtSq b (prefixRow s (fun i ↦ T i p))) := by
  simp_rw [(prefixRow_hilbertSchmidt s _ c b (hT _)).2]
  exact continuous_finsetSum _ hc

end JanetCartan.SamplingKernelBounds
