module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.TransportExtension.Spatial
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.TransportExtension.PairedCoordinates
public import JanetCartan.Analysis.Microlocal.NormalComparison.ChannelBounds

/-!
# Global transport coefficients for the matrix normal estimate

The buffered, mask-free transport amplitudes in `app:ch_osc:prop:osc-normal`,
Step 2. Support, smoothness and quantitative bounds are derived from the original
input data, with constants chosen before the family.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.NormalComparison
open AmplitudeBound
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

local instance transportBoundsMatrixTopology (r : ℕ) : TopologicalSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- The actual buffered coefficient in the paired-position convention of
`app:ch_osc:lem:osc-amplitude`, used by the channels in
`app:ch_osc:prop:osc-normal`. No mask occurs in this definition. -/
def UniformNormalData.pairedTransportCoefficient (F : UniformNormalData G C)
    (ε : ℝ) (c : Option (Fin n)) :=
  pairedNormalAmplitude (F.extendedTransportCoefficient ε c)

/-- The matrix channel coefficient is exactly the literal transport coefficient
on the original boxes (`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem UniformNormalData.pairedTransportCoefficient_eq
    (F : UniformNormalData G C) (ε : ℝ) (c : Option (Fin n))
    {x y u : Euclidean n} (hx : x ∈ G.X) (hy : y ∈ G.X) (hu : u ∈ G.D) :
    F.pairedTransportCoefficient ε c u (pairedPosition x y) =
      F.normalTransportCoefficient ε c x y u := by
  rw [pairedTransportCoefficient, pairedNormalAmplitude_pairedPosition]
  exact F.extendedTransportCoefficient_eq_on ε c ⟨hx, hy, hu⟩

/-- Uniform positive support and derivative constants for every actual transport
coefficient, chosen using only the fixed geometry and input jet budgets before
the family. This supplies `MatrixNormalAmplitudeBounds` for Step 2 of
`app:ch_osc:prop:osc-normal` without extra coefficient hypotheses. -/
theorem UniformNormalGeometry.exists_pairedTransportCoefficient_bounds
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) :
    ∃ R > 0, ∃ A > 0, ∀ F : UniformNormalData G C,
      ∀ ε ∈ Icc 0 G.ε₀, ∀ c : Option (Fin n),
        MatrixNormalAmplitudeBounds (F.pairedTransportCoefficient ε c) R A := by
  obtain ⟨R, hR, hbox⟩ := G.compact_X₀.isBounded.exists_pos_norm_le
  obtain ⟨K, hK, hjet⟩ := G.exists_extendedTransportCoefficient_jet_bound C (2 * (n + 1))
    (by omega)
  refine ⟨R, hR, K * normalPositionJetFactor n (2 * (n + 1)),
    mul_pos hK (normalPositionJetFactor_pos _ _), ?_⟩
  intro F ε hε c
  have hf := F.extendedTransportCoefficient_contDiff hε c
  have hp := contDiff_pairedNormalAmplitude hf
  refine ⟨hp.continuous.stronglyMeasurable, ?_, ?_, ?_⟩
  · intro u
    exact hp.comp (contDiff_const.prodMk contDiff_id)
  · intro u i j
    apply pairedNormalAmplitude_supportedInCenteredBox hbox
    intro q hq
    have hs := F.extendedTransportCoefficient_support hε c hq
    exact ⟨hs.1, hs.2.1⟩
  · intro u is hi z
    exact pairedNormalAmplitude_derivative_bound hf (fun q k hk ↦ hjet F ε hε c q k hk)
      u is hi z

end JanetCartan.NormalComparison
