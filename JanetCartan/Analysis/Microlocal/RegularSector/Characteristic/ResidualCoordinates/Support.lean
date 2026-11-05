module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.Symbols

/-!
# Vanishing of the actual columns away from the transported source mask

Zero values alone do not make extension commutators vanish. Here the actual
row formula proves a zero germ outside the original source's topological
support, and the correction formula gives a zero germ for the correction as
well. Thus every joint derivative vanishes there. These are local statements
on the actual inverse chart; a buffered containment is still required to
extend the columns across its boundary.
Consumer: the supported version of the complete residual implication.
Source: `app:ch_regular_base:eq:two-term-null-identity` and
`app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
variable {n d : ℕ}

/-- A zero source datum gives a zero actual leading column, with no
additional nullvector or inverse hypotheses. This uses the literal signed
row producer and preserves the original mask.
Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
theorem leadingColumn_eq_zero_of_sourceMask
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (r c : Fin n) (σ : RootState (Euclidean d) → ℝ)
    {q : TwoTimePoint (Euclidean d)} (hq : q ∈ C.target)
    (hσ : σ (C.symm q).2 = 0) (j : Fin n) :
    pencilLeadingColumn e Q B h Φ C r c σ j q = 0 := by
  have hz : pencilSignedRow e Q B h Φ C r c σ q = 0 := by
    apply (twoTimeRowTransport_eq_zero_iff hC _ _ hq).mpr
    simp [pencilSignedDatum, hσ]
  simp [pencilLeadingColumn, hz]

/-- Outside the transported topological source support both actual columns
vanish on a neighborhood. In particular the derivative in the correction
cannot leave a hidden extension commutator there.
Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
theorem columns_eventuallyEq_zero_of_sourceMask
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (r c : Fin n) (σ : RootState (Euclidean d) → ℝ)
    {q : TwoTimePoint (Euclidean d)} (hq : q ∈ C.target)
    (hσ : (C.symm q).2 ∉ tsupport σ) (j : Fin n) :
    pencilLeadingColumn e Q B h Φ C r c σ j =ᶠ[𝓝 q] 0 ∧
      pencilCorrectionColumn e Q B h Φ C r c σ j =ᶠ[𝓝 q] 0 := by
  have hm := (notMem_tsupport_iff_eventuallyEq.mp hσ).comp_tendsto
    (C.symm.continuousAt hq).snd
  have hu : pencilLeadingColumn e Q B h Φ C r c σ j =ᶠ[𝓝 q] 0 := by
    filter_upwards [hm, C.open_target.mem_nhds hq] with p hp hpC
    exact leadingColumn_eq_zero_of_sourceMask e Q B h Φ C hC r c σ hpC hp j
  refine ⟨hu, ?_⟩
  have hd := hu.fderiv (𝕜 := ℝ)
  filter_upwards [hu, hd] with p hp hdp
  simp only [fderiv_zero, Pi.zero_apply] at hdp
  simp [pencilCorrectionColumn, adaptedPencilApply, hp, hdp]

/-- All joint jets of both actual columns vanish off the transported
original source support, including derivatives used by `P W₁`.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem columns_iteratedFDeriv_eq_zero_of_sourceMask
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (r c : Fin n) (σ : RootState (Euclidean d) → ℝ)
    {q : TwoTimePoint (Euclidean d)} (hq : q ∈ C.target)
    (hσ : (C.symm q).2 ∉ tsupport σ) (j : Fin n) (k : ℕ) :
    iteratedFDeriv ℝ k (pencilLeadingColumn e Q B h Φ C r c σ j) q = 0 ∧
      iteratedFDeriv ℝ k (pencilCorrectionColumn e Q B h Φ C r c σ j) q = 0 := by
  obtain ⟨hu, hv⟩ := columns_eventuallyEq_zero_of_sourceMask e Q B h Φ C hC r c σ hq hσ j
  exact ⟨by simpa using (hu.iteratedFDeriv ℝ k).eq_of_nhds,
    by simpa using (hv.iteratedFDeriv ℝ k).eq_of_nhds⟩

/-- The original source-time buffer transports to a zero germ of both
actual columns. The source time is retained by the inverse chart, so the
argument applies also at the closed lower endpoint. Consumer: the lower
buffer in `CompleteResidual.completeResidual_operators_of_graph_regularizations`.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem columns_eventuallyEq_zero_of_lower_source_buffer
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (r c : Fin n) (σ : RootState (Euclidean d) → ℝ) (a : ℝ)
    (hbuffer : tsupport σ ⊆ {w | a < w.1})
    {q : TwoTimePoint (Euclidean d)} (hq : q ∈ C.target) (hs : q.2.1 ≤ a) (j : Fin n) :
    pencilLeadingColumn e Q B h Φ C r c σ j =ᶠ[𝓝 q] 0 ∧
      pencilCorrectionColumn e Q B h Φ C r c σ j =ᶠ[𝓝 q] 0 := by
  apply columns_eventuallyEq_zero_of_sourceMask e Q B h Φ C hC r c σ hq
  intro hm
  have ht := hbuffer hm
  have he := (twoTimeChart_inverse_coordinates hC hq).2.1
  exact (not_lt_of_ge hs) (he ▸ ht)

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
