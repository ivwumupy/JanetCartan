module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.RemainderSobolev.MixedLow
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.PrimitiveDiagonal

/-!
# Reflected full-amplitude jets for source convergence

The finite source reserve for `app:ch_background:eq:bg-full-complex-amplitude`
and `app:ch_background:eq:bg-real-symbol`. The mixed input is the published
conclusion of `TransportSymbol.exists_transportAmplitude_global_mixed_bound_of_primitiveNorms`.
The constant below precedes its single high budget; reflection and `k = 2πξ`
are kept literally. Consumer: the four source integrals in
`TransportKernel.realNormal_principal_reduction_of_test_limit`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TransportKernel.SourceConvergence
open ContinuumNormalReduction TransportSymbol Pseudodifferential
variable {n N : ℕ}

private def sourceFrequencyDilation (t : ℝ) (ht : t ≠ 0) : Variables n →L[ℝ] Variables n :=
  (frequencyDilationEquiv t ht).toContinuousLinearMap

/-- The normalized reflected FULL entry has bounded joint jets, including at
zero frequency, from the primitive mixed jets. The bound keeps the input
budget `A` linear (`app:ch_background:eq:bg-real-symbol`). -/
theorem exists_reflectedEntry_joint_bound_of_mixed (s : ℕ) (i j : Fin n) :
    ∃ C > 0, ∀ (a : Coefficients n N) (J : InputVariables n → ℝ)
      (u : Variables n × Euclidean 2 → SliceVariable n)
      (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2)),
      ContDiff ℝ ∞ (amplitude a J u Ω K) → ∀ A : ℝ, 0 ≤ A →
      (∀ p : Variables n, ∀ k ≤ s, ∀ I : Finset (Fin k),
        ∀ v : Fin k → Variables n,
        (∀ j ∈ I, (v j).1 = 0 ∧ (v j).2.1 = 0) →
        (∀ j ∉ I, (v j).2.2 = 0) →
        (1 + ‖p.2.2‖) ^ I.card * ‖iteratedFDeriv ℝ k (amplitude a J u Ω K) p v‖ ≤
          A * ∏ j, ‖v j‖) →
      ContDiff ℝ ∞ (fun q : Variables n ↦
        (reflectedSymbolAmplitude a J u Ω K (q.1, q.2.1, (2 * Real.pi) • q.2.2) i j : ℂ)) ∧
      ∀ p : Variables n, ∀ k ≤ s,
        ‖iteratedFDeriv ℝ k (fun q : Variables n ↦
          (reflectedSymbolAmplitude a J u Ω K (q.1, q.2.1, (2 * Real.pi) • q.2.2) i j : ℂ)) p‖ ≤ C * A := by
  let t := 2 * Real.pi
  let D := max 1 (max ‖sourceFrequencyDilation (n := n) t (by positivity)‖
    ‖sourceFrequencyDilation (n := n) (-t) (neg_ne_zero.mpr (by positivity))‖)
  have hD : 1 ≤ D := le_max_left _ _
  let L := Complex.ofRealCLM.comp (realMatrixEntry i j)
  let C₀ := ‖L‖ * (4 * (2 * Real.pi) ^ n) * 2 ^ s * D ^ s
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀ + 1, by positivity, ?_⟩
  intro a J u Ω K ha A hA hb
  let f := amplitude a J u Ω K
  have hf : ContDiff ℝ ∞ f := ha
  have hglobal := norm_iteratedFDeriv_global_le_of_mixed f s hA hb
  have hscale (t' : ℝ) (hne : t' ≠ 0) (ht' : ‖sourceFrequencyDilation (n := n) t' hne‖ ≤ D)
      (p : Variables n) (k : ℕ) (hk : k ≤ s) :
      ‖iteratedFDeriv ℝ k (f ∘ sourceFrequencyDilation t' hne) p‖ ≤
        2 ^ s * A * D ^ s := by
    apply (norm_iteratedFDeriv_comp_linear_le (sourceFrequencyDilation t' hne) f hf k p).trans
    exact mul_le_mul (hglobal _ k hk)
      ((pow_le_pow_left₀ (norm_nonneg _) ht' _).trans (pow_le_pow_right₀ hD hk))
      (by positivity) (by positivity)
  let g := fun q : Variables n ↦ (2 * (2 * Real.pi) ^ n) •
    (f (sourceFrequencyDilation t (by positivity) q) + f (sourceFrequencyDilation (-t) (neg_ne_zero.mpr (by positivity)) q))
  have hg : ContDiff ℝ ∞ g := ((hf.comp (sourceFrequencyDilation t (by positivity)).contDiff).add
    (hf.comp (sourceFrequencyDilation (-t) (neg_ne_zero.mpr (by positivity))).contDiff)).const_smul _
  let c := fun x y ξ ↦ (reflectedSymbolAmplitude a J u Ω K (x, y, t • ξ) i j : ℂ)
  have he : (fun q : Variables n ↦ c q.1 q.2.1 q.2.2) = L ∘ g := by
    funext q
    change _ = ((g q) i j : ℂ)
    simp [c, g, f, sourceFrequencyDilation, frequencyDilationEquiv, scaleFrequency, reflectedSymbolAmplitude, t, mul_add]
  have hc : ContDiff ℝ ∞ (fun q : Variables n ↦ c q.1 q.2.1 q.2.2) :=
    he ▸ L.contDiff.comp hg
  have hcg (p : Variables n) (k : ℕ) (hk : k ≤ s) :
      ‖iteratedFDeriv ℝ k (fun q : Variables n ↦ c q.1 q.2.1 q.2.2) p‖ ≤ C₀ * A := by
    rw [he]
    apply (L.norm_iteratedFDeriv_comp_left hg.contDiffAt (by simp)).trans
    have hg' : ‖iteratedFDeriv ℝ k g p‖ ≤
        (4 * (2 * Real.pi) ^ n) * (2 ^ s * A * D ^ s) := by
      rw [show g = (2 * (2 * Real.pi) ^ n) •
          (f ∘ sourceFrequencyDilation t (by positivity) + f ∘ sourceFrequencyDilation (-t) (neg_ne_zero.mpr (by positivity))) from rfl,
        iteratedFDeriv_const_smul_apply (i := k)
          (f := f ∘ sourceFrequencyDilation t (by positivity) + f ∘ sourceFrequencyDilation (-t) (neg_ne_zero.mpr (by positivity)))
          (((hf.comp (sourceFrequencyDilation t (by positivity)).contDiff).add
            (hf.comp (sourceFrequencyDilation (-t) (neg_ne_zero.mpr (by positivity))).contDiff)).contDiffAt.of_le (by simp)),
        norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * (2 * Real.pi) ^ n),
        iteratedFDeriv_add_apply (i := k) (f := f ∘ sourceFrequencyDilation t (by positivity))
          (g := f ∘ sourceFrequencyDilation (-t) (neg_ne_zero.mpr (by positivity)))
          ((hf.comp (sourceFrequencyDilation t (by positivity)).contDiff).contDiffAt.of_le (by simp))
          ((hf.comp (sourceFrequencyDilation (-t) (neg_ne_zero.mpr (by positivity))).contDiff).contDiffAt.of_le (by simp))]
      have h₁ := hscale t (by positivity) ((le_max_left _ _).trans (le_max_right _ _)) p k hk
      have h₂ := hscale (-t) (neg_ne_zero.mpr (by positivity)) ((le_max_right _ _).trans (le_max_right _ _)) p k hk
      calc
        _ ≤ (2 * (2 * Real.pi) ^ n) *
            ((2 ^ s * A * D ^ s) + (2 ^ s * A * D ^ s)) :=
          mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h₁ h₂)) (by positivity)
        _ = _ := by ring
    exact (mul_le_mul_of_nonneg_left hg' (norm_nonneg _)).trans_eq (by dsimp [C₀]; ring)
  refine ⟨hc, fun p k hk ↦ (hcg p k hk).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hA

end JanetCartan.ContinuumRow.TransportKernel.SourceConvergence
