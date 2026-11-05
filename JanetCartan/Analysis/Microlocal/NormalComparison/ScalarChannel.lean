module

public import JanetCartan.Analysis.Microlocal.NormalComparison.OperatorBounds
public import JanetCartan.Analysis.Microlocal.NormalComparison.CutoffGeometry

/-!
# The bounded scalar cutoff channel

Instantiates Step 1 for the fixed enlarged cutoff geometry, supplying every
scalar-channel premise of Step 2 of `app:ch_osc:prop:osc-normal`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal
namespace JanetCartan.NormalComparison
open AmplitudeBound
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- Scalar cutoff input operator in Step 2 of `app:ch_osc:prop:osc-normal`.
It is the single coordinate of the actual rank-one oscillatory operator. -/
def ScalarNormalCutoffs.scalarChannel (χ : ScalarNormalCutoffs G C)
    (F : UniformNormalData G C) (K ε : ℝ) :
    Lp ℂ 2 (volume.restrict G.D) →L[ℂ] Lp (α := Euclidean n) ℂ 2 :=
  (PiLp.proj 2 (fun _ : Fin 1 ↦ Lp (α := Euclidean n) ℂ 2) 0).comp
    ((χ.toUniformNormalData F).uniformOscillatoryOperator K ε)

/-- Literal scalar input integral for the fixed cutoff channel
(`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem ScalarNormalCutoffs.scalarChannel_ae_integral (χ : ScalarNormalCutoffs G C)
    (F : UniformNormalData G C) (K : ℝ) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (f : Lp ℂ 2 (volume.restrict G.D)) :
    χ.scalarChannel F K ε f =ᵐ[volume] fun x ↦ ∫ u in G.D,
      normalizedOscillatoryKernel (normalOperatorScale n K) K (F.phase ε)
        (fun x u ↦ χ.amplitude (x, u) 0) x u * f u :=
  (χ.toUniformNormalData F).uniformOscillatoryOperator_ae_integral K hε f 0

/-- The scalar cutoff channel has a uniform norm bound depending only on
its fixed geometry and jets (`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem ScalarNormalCutoffs.exists_scalarChannel_bound (χ : ScalarNormalCutoffs G C) :
    ∃ S > 0, ∀ F : UniformNormalData G C, ∀ ε ∈ Icc 0 G.ε₀, ∀ K > 0,
      ‖χ.scalarChannel F K ε‖ ≤ S := by
  obtain ⟨S, hS, hb⟩ := (G.scalarCutoffGeometry C).exists_uniformOscillatoryOperator_bound
    χ.inputBounds
  refine ⟨S, hS, ?_⟩
  intro F ε hε K hK
  apply ContinuousLinearMap.opNorm_le_bound _ hS.le
  intro f
  calc
    ‖χ.scalarChannel F K ε f‖ ≤
        ‖(χ.toUniformNormalData F).uniformOscillatoryOperator K ε f‖ :=
      PiLp.norm_apply_le _ 0
    _ ≤ ‖(χ.toUniformNormalData F).uniformOscillatoryOperator K ε‖ * ‖f‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ S * ‖f‖ := mul_le_mul_of_nonneg_right (hb _ ε hε K hK) (norm_nonneg _)

end JanetCartan.NormalComparison
