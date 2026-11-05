module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Relations
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.ChartControls.Triangular

/-!
# Quantitative residuals of the elapsed phase

The interior gap for `app:ch_regular:eq:chain-tail` uses all five equations
of `app:ch_regular:eq:joint-stationary` and the elapsed source energy. Each
is bounded by the full derivative, with no coefficient-dependent constant.
-/

@[expose] public noncomputable section

open Set Metric
open scoped InnerProductSpace

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization FiniteChain.Graph

variable {d : ℕ}

private theorem norm_fderiv_slice_le {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {F : ℝ × V → ℝ} {r : ℝ} {p : V}
    (hF : DifferentiableAt ℝ F (r, p)) :
    ‖fderiv ℝ (fun v ↦ F (r, v)) p‖ ≤ ‖fderiv ℝ F (r, p)‖ := by
  have hd := (hF.hasFDerivAt.comp p (hasFDerivAt_prodMk_right (𝕜 := ℝ) r p)).fderiv
  simp only [Function.comp_def] at hd
  rw [hd]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  simpa using (fderiv ℝ F (r, p)).le_opNorm (0, v)

/-- The sixth residual is the original source energy, controlled by the
full derivative in either orientation (`app:ch_regular:lem:finite-chain`).
Consumer: correction to the zero-energy relation in the uniform interior gap. -/
theorem abs_source_energy_le_jointElapsedPhase_fderiv
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (backward : Bool) (x y : Euclidean (d + 1)) (r : ℝ)
    (p : JointVariables (Euclidean (d + 1)))
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r p.1.1 p.2.1))
      (elapsedChartPoint r p.1.1 p.2.1)) :
    |rootSuspension h (elapsedInputBase C r p.1.1 p.2.1, p.2.1)| ≤
      ‖fderiv ℝ (jointElapsedPhase backward (chartPhase C) x y) (r, p)‖ := by
  have hd := (differentiableAt_jointElapsedPhase backward x y (r, p) hphase).hasFDerivAt
    |>.comp_hasDerivAt r ((hasDerivAt_id r).prodMk (hasDerivAt_const r p))
  have hn := (fderiv ℝ (jointElapsedPhase backward (chartPhase C) x y) (r, p)).le_opNorm
    (1, 0)
  cases backward
  · have he := hd.unique (hasDerivAt_jointElapsedPhase_forward_elapsed x y r p hphase)
    simpa [he] using hn
  · have he := hd.unique (hasDerivAt_jointElapsedPhase_reverse_elapsed x y r p hphase)
    simpa [he] using hn

/-- The five forward residuals are bounded by the full elapsed derivative
(`app:ch_regular:eq:joint-stationary`). Consumer: the two endpoint corrections. -/
theorem forward_elapsed_residual_bounds
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (x y : Euclidean (d + 1)) (r : ℝ) (p : JointVariables (Euclidean (d + 1)))
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r p.1.1 p.2.1))
      (elapsedChartPoint r p.1.1 p.2.1)) :
    let G := ‖fderiv ℝ (jointElapsedPhase false (chartPhase C) x y) (r, p)‖
    ‖elapsedOutputCovector h Φ C r p.1.1 p.2.1 - p.2.2.2‖ ≤ G ∧
    ‖p.2.2.1 - p.2.1‖ ≤ G ∧
    ‖elapsedInputBase C r p.1.1 p.2.1 - p.1.2‖ ≤ G ∧
    ‖p.1.2 - y‖ ≤ G ∧ ‖x - p.1.1‖ ≤ G := by
  have hn := norm_fderiv_slice_le
    (differentiableAt_jointElapsedPhase false x y (r, p) hphase)
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := forward_joint_derivative_bounds
    (elapsedPhase (chartPhase C) r) x y p (differentiableAt_elapsedChartPhase_uncurry hphase)
  rw [(hasFDerivAt_elapsedChartPhase_output hphase).fderiv, ← map_sub,
    innerSL_apply_norm] at h₁
  rw [(hasFDerivAt_elapsedChartPhase_covector hphase).fderiv, ← map_sub,
    innerSL_apply_norm] at h₃
  exact ⟨h₁.trans hn, h₂.trans hn, h₃.trans hn, h₄.trans hn, h₅.trans hn⟩

/-- The same quantitative bounds for the literal adjoint, with its original
source and target exchanged (`app:ch_regular:eq:joint-stationary`).
Consumer: the reverse interior gap, without changing the elapsed segment. -/
theorem reverse_elapsed_residual_bounds
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (x y : Euclidean (d + 1)) (r : ℝ) (p : JointVariables (Euclidean (d + 1)))
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r p.1.1 p.2.1))
      (elapsedChartPoint r p.1.1 p.2.1)) :
    let G := ‖fderiv ℝ (jointElapsedPhase true (chartPhase C) x y) (r, p)‖
    ‖p.2.2.1 - elapsedOutputCovector h Φ C r p.1.1 p.2.1‖ ≤ G ∧
    ‖p.2.1 - p.2.2.2‖ ≤ G ∧
    ‖p.1.2 - elapsedInputBase C r p.1.1 p.2.1‖ ≤ G ∧
    ‖p.1.1 - y‖ ≤ G ∧ ‖x - p.1.2‖ ≤ G := by
  have hn := norm_fderiv_slice_le
    (differentiableAt_jointElapsedPhase true x y (r, p) hphase)
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := reverse_joint_derivative_bounds
    (elapsedPhase (chartPhase C) r) x y p (differentiableAt_elapsedChartPhase_uncurry hphase)
  rw [(hasFDerivAt_elapsedChartPhase_output hphase).fderiv, ← map_sub,
    innerSL_apply_norm] at h₁
  rw [(hasFDerivAt_elapsedChartPhase_covector hphase).fderiv, ← map_sub,
    innerSL_apply_norm] at h₃
  exact ⟨h₁.trans hn, h₂.trans hn, h₃.trans hn, h₄.trans hn, h₅.trans hn⟩

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
