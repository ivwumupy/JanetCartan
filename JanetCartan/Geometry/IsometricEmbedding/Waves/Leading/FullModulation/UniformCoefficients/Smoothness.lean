module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.UniformCoefficients.Formulas

/-!
# Smoothness of the six literal full-modulation coefficients

This instantiates the existing reduced-operator regularity theorem with the
independent parameter pair. The neighborhood producer supplies the actual
nonzero denominator (`app:ch_waves:thm:leading`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.LeadingWave.FullModulation.UniformCoefficients
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport NullTransport.CoefficientBounds

/-- All six named coefficients are smooth on the open full neighborhood once
its constructed denominator gap is supplied. Only primitive smooth immersion
is needed for the connection terms (`app:ch_waves:thm:leading`). -/
theorem smooth_full_coefficients {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold}) {F : Euclidean n → Euclidean N} (hF : ContDiffOn ℝ ∞ F U)
    (hi : IsImmersionOn F U) (r c : Fin n)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hsub : Ω ⊆ inputDomain T)
    (hd : ∀ w ∈ Ω, adaptedDenominator T Q r c w ≠ 0) :
    ContDiffOn ℝ ∞ (nullvector T Q c) Ω ∧
    ContDiffOn ℝ ∞ (conullvector T Q r) Ω ∧
    ContDiffOn ℝ ∞ (adaptedDenominator T Q r c) Ω ∧
    ContDiffOn ℝ ∞ (fun w ↦ (adaptedDenominator T Q r c w)⁻¹) Ω ∧
    ContDiffOn ℝ ∞ (transportDirection T Q r c) Ω ∧
    ContDiffOn ℝ ∞ (transportPotential T Q F r c) Ω := by
  have hxU {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ Ω) :
      w.1 ∈ U := (hsub hw).2
  have hQ (i j a : Fin n) : ContDiffOn ℝ ∞
      (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦ Q.1 w.1 i j a) Ω :=
    ((Matrix.entryLinearMap ℝ ℝ j a).toContinuousLinearMap.contDiff.comp_contDiffOn
      (contDiffOn_pi.mp Q.2.1 i)).comp contDiffOn_fst (fun _ hw ↦ hxU hw)
  have hξ := (phaseGradient_joint_smooth T Q).mono (hsub.trans inter_subset_left)
  have hk := contDiffOn_rightNullvector_reducedSymbol hQ hξ c
  have hl := contDiffOn_leftNullvector_reducedSymbol hQ hξ r
  have hke : ContDiffOn ℝ ∞ (nullvector T Q c) Ω :=
    (contDiffOn_piLp 2).mpr (contDiffOn_pi.mp hk)
  have hden : ContDiffOn ℝ ∞ (adaptedDenominator T Q r c) Ω := by
    rw [adaptedDenominator_eq_formula]
    exact (smooth_denominator T.data.adapted.normal r c).comp_contDiffOn
      ((smooth_fullInput T Q).mono hsub)
  have hdir : ContDiffOn ℝ ∞ (transportDirection T Q r c) Ω := by
    apply (contDiffOn_piLp 2).mpr
    intro a
    exact (contDiffOn_transportField hQ hl hk a).div hden hd
  have hpot : ContDiffOn ℝ ∞ (transportPotential T Q F r c) Ω := by
    apply ContDiffOn.div _ hden hd
    exact ContDiffOn.sum fun i _ ↦ (contDiffOn_pi.mp hl i).mul
      (contDiffOn_reducedOperator_joint hΩ
        (hF.comp contDiffOn_fst (fun _ hw ↦ hxU hw))
        (fun _ hw ↦ hi _ (hxU hw)) hQ hke i)
  exact ⟨hke, hl, hden, hden.inv hd, hdir, hpot⟩

end JanetCartan.LeadingWave.FullModulation.UniformCoefficients
