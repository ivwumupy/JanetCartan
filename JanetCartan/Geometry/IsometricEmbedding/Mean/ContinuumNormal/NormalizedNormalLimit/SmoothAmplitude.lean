module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.ComplexAmplitude

/-!
# Joint smoothness of the full physical amplitudes

The literal spectator amplitude is transferred to paired physical positions,
including the existing Fourier normalization and both reflected terms.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ContinuumNormalReduction TransportSymbol ContinuumRow.TransportKernel
open ContinuumRow.CarrierNormalRealization CarrierVariation Pseudodifferential

/-- Smooth spectator amplitudes give joint smoothness in the physical PDO
coordinates. This is a smoothness statement, with no oscillatory operator norm
continuity assertion (app:ch_background:eq:bg-full-complex-amplitude,
bg-real-symbol). Consumers: the source-family regularity and zero-limit absolute amplitude estimates. -/
theorem fullAmplitudes_contDiff_of_transportAmplitude
    {n N : ℕ} (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (ha : ContDiff ℝ ∞ (amplitude a J u Ω S)) :
    ContDiff ℝ ∞ (Function.uncurry (fullComplexMatrixAmplitude a J u Ω S)) ∧
      ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude a J u Ω S)) := by
  classical
  have hc (i j : Fin n) : ContDiff ℝ ∞
      (fun p : Euclidean n × Euclidean (2 * n) ↦ fullComplexMatrixAmplitude a J u Ω S p.1 p.2 i j) := by
    exact Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul (((realMatrixEntry i j).contDiff.comp ha).comp
        ((freezingOutputProjection.contDiff.comp contDiff_snd).prodMk
          ((freezingSourceProjection.contDiff.comp contDiff_snd).prodMk
            (contDiff_fst.const_smul (2 * Real.pi))))))
  have hfull : ContDiff ℝ ∞ (Function.uncurry (fullComplexMatrixAmplitude a J u Ω S)) := by
    have he : Function.uncurry (fullComplexMatrixAmplitude a J u Ω S) =
        fun p : Euclidean n × Euclidean (2 * n) ↦ ∑ i : Fin n, ∑ j : Fin n,
          fullComplexMatrixAmplitude a J u Ω S p.1 p.2 i j •
            (Matrix.single i j 1 : Matrix (Fin n) (Fin n) ℂ) := by
      funext p
      ext i j
      simp [Matrix.single, Matrix.sum_apply, ite_and, Function.uncurry_def]
    rw [he]
    exact ContDiff.sum fun i _ ↦ ContDiff.sum fun j _ ↦ (hc i j).smul contDiff_const
  refine ⟨hfull, ?_⟩
  have he : Function.uncurry (fullReflectedMatrixAmplitude a J u Ω S) =
      fun p : Euclidean n × Euclidean (2 * n) ↦ (2 : ℂ) •
        (fullComplexMatrixAmplitude a J u Ω S p.1 p.2 +
          fullComplexMatrixAmplitude a J u Ω S (-p.1) p.2) := by
    funext p
    exact fullReflectedMatrixAmplitude_eq_complex_add_reflection a J u Ω S p.1 p.2
  rw [he]
  exact (hfull.add (hfull.comp (contDiff_fst.neg.prodMk contDiff_snd))).const_smul (2 : ℂ)

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
