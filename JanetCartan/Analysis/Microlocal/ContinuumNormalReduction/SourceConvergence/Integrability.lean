module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.SourceConvergence.ReflectedBounds

/-!
# The four source integrals of the actual normal reduction

This discharges `hi`, `hid`, `hir`, and `hiB` in
`TransportKernel.realNormal_principal_reduction_of_test_limit`. The original
Taylor remainder is retained. Primitive order-zero jets through `n+3` and a
compact source test through `n+1` suffice; no Fourier integrability is assumed.
Source: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TransportKernel.SourceConvergence
open ContinuumNormalReduction TransportSymbol Pseudodifferential
variable {n N : ℕ}

/-- All four source transforms are integrable from finite primitive joint
symbol jets, retaining the original Taylor construction and cutoff jets.
Consumer: `realNormal_principal_reduction_of_test_limit`
(`app:ch_background:eq:bg-real-symbol`). -/
theorem source_integrability_of_joint_bounds
    (b : OrthonormalBasis (Fin n) ℝ (Euclidean n))
    (c : Euclidean n → Euclidean n → Euclidean n → ℂ)
    (β : Euclidean n → ℝ) (u : Euclidean n → ℂ) (x : Euclidean n)
    (hc : ContDiff ℝ ∞ (fun p : Variables n ↦ c p.1 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β)
    (hu : ContDiff ℝ (n + 1) u) (huc : HasCompactSupport u)
    (M K : ℕ → ℝ)
    (hM : ∀ j ≤ n + 3, ∀ y ξ,
      ‖iteratedFDeriv ℝ j (fun p : Variables n ↦ c p.1 p.2.1 p.2.2) (x, y, ξ)‖ ≤
        M j)
    (hK : ∀ j ≤ n + 2, ∀ y, ‖iteratedFDeriv ℝ j β y‖ ≤ K j) :
    Integrable (sourceAmplitudeTransform c u x) ∧
    Integrable (sourceAmplitudeTransform (diagonalAmplitude c β) u x) ∧
    Integrable (sourceAmplitudeTransform (diagonalRemainderAmplitude b c β) u x) ∧
    Integrable (sourceAmplitudeTransform (fullTaylorCoefficient c β) u x) := by
  have hM : ∀ j ≤ n + 3, ∀ y ξ,
      ‖iteratedFDeriv ℝ j (fun p : Variables n ↦ c p.1 p.2.1 p.2.2) (x, y, ξ)‖ ≤
        M j * (1 + ‖ξ‖) ^ (0 : ℕ) := by simpa using hM
  have hu : ContDiff ℝ (0 + Module.finrank ℝ (Euclidean n) + 1) u := by simpa using hu
  have hd : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n × Euclidean n ↦ diagonalAmplitude c β p.1 p.2.1 p.2.2) :=
    (hβ.comp contDiff_snd.fst).smul
      (hc.comp (f := fun p : Euclidean n × Euclidean n × Euclidean n ↦ (p.1, p.1, p.2.2)) (by fun_prop))
  have hr := contDiff_diagonalRemainderAmplitude_joint b c β hc hβ
  have hB := contDiff_fullTaylorCoefficient_joint c β hc hβ
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply integrable_sourceAmplitudeTransform_of_sourceSymbolBounds c u x 0
      (hc.continuous.comp (f := fun p : Euclidean n × Euclidean n ↦ (x, p.2, p.1)) (by fun_prop)) hu huc
      (fun ξ ↦ (hc.comp (f := fun y : Euclidean n ↦ (x, y, ξ)) (by fun_prop)).of_le (by simp)) M
    intro j hj y ξ
    exact (norm_iteratedFDeriv_source_le_joint c hc x y ξ j).trans (hM j (by simp at hj; omega) y ξ)
  · apply integrable_sourceAmplitudeTransform_of_sourceSymbolBounds _ u x 0
      (hd.continuous.comp (f := fun p : Euclidean n × Euclidean n ↦ (x, p.2, p.1)) (by fun_prop)) hu huc
      (fun ξ ↦ (hd.comp (f := fun y : Euclidean n ↦ (x, y, ξ)) (by fun_prop)).of_le (by simp))
      (fun j ↦ K j * M 0)
    intro j hj y ξ
    have h0 : ‖c x x ξ‖ ≤ M 0 * (1 + ‖ξ‖) ^ (0 : ℕ) := by
      simpa only [norm_iteratedFDeriv_zero] using hM 0 (by omega) x ξ
    calc
      _ ≤ ‖iteratedFDeriv ℝ j β y‖ * ‖c x x ξ‖ :=
        norm_iteratedFDeriv_diagonalAmplitude_source_le c β hβ x y ξ j
      _ ≤ K j * (M 0 * (1 + ‖ξ‖) ^ (0 : ℕ)) :=
        mul_le_mul (hK j (by simp at hj; omega) y) h0 (norm_nonneg _) ((norm_nonneg _).trans (hK j (by simp at hj; omega) y))
      _ = _ := by ring
  · apply integrable_sourceAmplitudeTransform_of_sourceSymbolBounds _ u x 0
      (hr.continuous.comp (f := fun p : Euclidean n × Euclidean n ↦ (x, p.2, p.1)) (by fun_prop)) hu huc
      (fun ξ ↦ (hr.comp (f := fun y : Euclidean n ↦ (x, y, ξ)) (by fun_prop)).of_le (by simp))
      (fun j ↦ ‖(2 * Real.pi * Complex.I)⁻¹‖ * n *
        ∑ i ∈ Finset.range (j + 2), ((j + 1).choose i : ℝ) * K i * M (j + 1 - i + 1))
    intro j hj y ξ
    simpa only [Fintype.card_fin] using norm_iteratedFDeriv_diagonalRemainderAmplitude_source_le b c β hc hβ x y ξ j 0 M K
      (fun k hk z ↦ hM k (by simp at hj; omega) z ξ) (fun k hk ↦ hK k (by simp at hj; omega) y)
  · apply integrable_sourceAmplitudeTransform_of_sourceSymbolBounds _ u x 0
      (hB.continuous.comp (f := fun p : Euclidean n × Euclidean n ↦ (x, p.2, p.1)) (by fun_prop)) hu huc
      (fun ξ ↦ (hB.comp (f := fun y : Euclidean n ↦ (x, y, ξ)) (by fun_prop)).of_le (by simp))
      (fun j ↦ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * K i * M (j - i + 1))
    intro j hj y ξ
    exact norm_iteratedFDeriv_fullTaylorCoefficient_source_le c β hc hβ x y ξ j 0 M K
      (fun k hk z ↦ hM k (by simp at hj; omega) z ξ) (fun k hk ↦ hK k (by simp at hj; omega) y)

/-- The four integrability premises of the normal test reduction follow from
published primitive full-amplitude mixed jets. The input `A` may be exactly
`C * H` from `exists_transportAmplitude_global_mixed_bound_of_primitiveNorms`;
no kernel estimate is assumed (`app:ch_background:eq:bg-real-symbol`). -/
theorem reflected_source_integrability_of_mixed
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (ha : ContDiff ℝ ∞ (amplitude a J u Ω K))
    {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ p : Variables n, ∀ k ≤ n + 3, ∀ I : Finset (Fin k),
      ∀ v : Fin k → Variables n,
      (∀ j ∈ I, (v j).1 = 0 ∧ (v j).2.1 = 0) →
      (∀ j ∉ I, (v j).2.2 = 0) →
      (1 + ‖p.2.2‖) ^ I.card * ‖iteratedFDeriv ℝ k (amplitude a J u Ω K) p v‖ ≤
        A * ∏ j, ‖v j‖)
    (b : OrthonormalBasis (Fin n) ℝ (Euclidean n))
    (β : Euclidean n → ℝ) (hβ : ContDiff ℝ ∞ β)
    (Bβ : ℕ → ℝ) (hBβ : ∀ k ≤ n + 2, ∀ y, ‖iteratedFDeriv ℝ k β y‖ ≤ Bβ k)
    (f : Euclidean n → ℂ) (hf : ContDiff ℝ (n + 1) f) (hfc : HasCompactSupport f)
    (x : Euclidean n) (i j : Fin n) :
    let c := fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)
    Integrable (sourceAmplitudeTransform c f x) ∧
    Integrable (sourceAmplitudeTransform (diagonalAmplitude c β) f x) ∧
    Integrable (sourceAmplitudeTransform (diagonalRemainderAmplitude b c β) f x) ∧
    Integrable (sourceAmplitudeTransform (fullTaylorCoefficient c β) f x) := by
  obtain ⟨C, _, hC⟩ := exists_reflectedEntry_joint_bound_of_mixed (N := N) (n + 3) i j
  obtain ⟨hc, hbound⟩ := hC a J u Ω K ha A hA hb
  exact source_integrability_of_joint_bounds b _ β f x hc hβ hf hfc
    (fun _ ↦ C * A) Bβ (fun k hk y ξ ↦ hbound (x, y, ξ) k hk) hBβ

end JanetCartan.ContinuumRow.TransportKernel.SourceConvergence
