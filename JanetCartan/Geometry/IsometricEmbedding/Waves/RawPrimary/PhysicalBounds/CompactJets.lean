module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.CompactSynthesis
public import JanetCartan.Analysis.Operator.MeasureEnvelopes.Derivatives

/-!
# Compact Fourier synthesis of physical jets

Measurability of every differentiated atom and the finite-order synthesis
estimate used by `app:ch_waves:eq:raw-physical-bound`. The density is only
integrable; no derivatives or continuity of the Fourier datum are required.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.RawPrimary

variable {X P F : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set X} {V : Set P} {A : X × P → F}

/-- Joint regularity of the physical jets of a smooth atom. The consumer is
the measurability input of dominated synthesis in
`app:ch_waves:eq:raw-physical-bound`. -/
theorem contDiffOn_atomPhysicalJet (hU : IsOpen U) (hV : IsOpen V)
    (hA : ContDiffOn ℝ ∞ A (U ×ˢ V)) (j : ℕ) :
    ContDiffOn ℝ ∞ (fun p : X × P ↦ iteratedFDeriv ℝ j (fun x ↦ A (x, p.2)) p.1)
      (U ×ˢ V) := by
  induction j with
  | zero =>
    let L : F →L[ℝ] (X [×0]→L[ℝ] F) :=
      (continuousMultilinearCurryFin0 ℝ X F).symm.toContinuousLinearEquiv.toContinuousLinearMap
    exact L.contDiff.comp_contDiffOn hA
  | succ j ih =>
    let L : (X →L[ℝ] (X [×j]→L[ℝ] F)) →L[ℝ] (X [×(j + 1)]→L[ℝ] F) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ X)
        F).symm.toContinuousLinearEquiv.toContinuousLinearMap
    exact L.contDiff.comp_contDiffOn (contDiffOn_parameterFDeriv hU hV ih)

end JanetCartan.RawPrimary
