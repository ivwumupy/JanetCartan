module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.BoundaryGap

/-!
# A fixed smooth elapsed cutoff

The common collar in `app:ch_regular:lem:finite-chain` admits a scalar cutoff
with global bounds for every derivative. The cutoff and its bounds depend
only on the already chosen positive collar width. In particular they precede
the current coefficients, the external bases and the integration accuracy.
Consumer: the finite-family quantitative localization assembly.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open FiniteChain.Graph

variable {d : ℕ}

/-- A scalar elapsed cutoff, lifted to the actual joint variables, with
global all-order bounds and closed support separation. The complement starts
strictly inside the positive half-space, so no boundary jump is differentiated
in `app:ch_regular:eq:chain-tail`. -/
theorem exists_uniform_elapsed_collar_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∃ (χ : ℝ × JointVariables (Euclidean (d + 1)) → ℂ) (H : ℕ → ℝ),
      ContDiff ℝ ∞ χ ∧
      (∀ p, |p.1| ≤ ε / 4 → χ p = 1) ∧
      tsupport χ ⊆ {p | |p.1| ≤ ε / 2} ∧
      tsupport (1 - χ) ⊆ {p | ε / 4 ≤ |p.1|} ∧
      (∀ k, 0 ≤ H k) ∧
      (∀ k p, ‖iteratedFDeriv ℝ k χ p‖ ≤ H k) := by
  let f : ContDiffBump (0 : ℝ) :=
    { rIn := ε / 4
      rOut := ε / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let g : ℝ → ℂ := fun r ↦ (f r : ℂ)
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp f.contDiff
  have hgc : HasCompactSupport g :=
    f.hasCompactSupport.comp_left (g := fun r : ℝ ↦ (r : ℂ)) Complex.ofReal_zero
  choose H hH hbound using fun k ↦ hgc.exists_bound_iteratedFDeriv hg k
  let L : (ℝ × JointVariables (Euclidean (d + 1))) →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ _
  let χ := g ∘ L
  have hone : ∀ p, |p.1| ≤ ε / 4 → χ p = 1 := by
    intro p hp
    have hf := f.one_of_mem_closedBall (x := p.1) (by
      simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hp)
    change (f p.1 : ℂ) = 1
    rw [hf, Complex.ofReal_one]
  refine ⟨χ, fun k ↦ H k * ‖L‖ ^ k, hg.comp L.contDiff, hone, ?_, ?_,
    fun k ↦ mul_nonneg (hH k) (pow_nonneg (norm_nonneg _) _), ?_⟩
  · apply closure_minimal ?_ (isClosed_le continuous_fst.abs continuous_const)
    intro p hp
    by_contra hn
    have hz := f.zero_of_le_dist (x := p.1) (by
      simpa only [Real.dist_eq, sub_zero] using (le_of_not_ge hn))
    apply hp
    change (f p.1 : ℂ) = 0
    rw [hz, Complex.ofReal_zero]
  · apply closure_minimal ?_ (isClosed_le continuous_const continuous_fst.abs)
    intro p hp
    by_contra hn
    exact hp (by simp only [Pi.sub_apply, Pi.one_apply,
      hone p (le_of_not_ge hn), sub_self])
  · intro k p
    rw [show χ = g ∘ L from rfl, L.iteratedFDeriv_comp_right hg p (by simp)]
    exact ((iteratedFDeriv ℝ k g (L p)).norm_compContinuousLinearMap_le
      (fun _ ↦ L)).trans (by
        simpa using mul_le_mul_of_nonneg_right (hbound k k le_rfl (L p))
          (pow_nonneg (norm_nonneg L) k))

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
