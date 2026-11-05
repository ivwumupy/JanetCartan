module

public import JanetCartan.Iteration.PhysicalSampling.SliceAmplitude
public import JanetCartan.Iteration.PhysicalScalarChannel.Comparison
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.UniformDyadicBound

/-!
# Annular support for the same scalar slice operators

Restrict only the certified input support, not the integration domain or actual
operator. The original radial masks vanish below radius one half. Together with
the actual transverse comparison, this supplies a uniform supported-gradient
gap for the full dyadic sum with no band-count factor.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace

namespace JanetCartan.PhysicalScalarChannel
open NormalComparison RawPrimary.SliceGeometry RawPrimary.MaskProfiles PhysicalSampling
open ActualCarriers.FrozenPhaseReference

variable {d r : ℕ}

/-- Retain every geometric datum except the certified input support, which is
intersected with the original lower radial bound. -/
def annularGeometry (G : UniformNormalGeometry d r) : UniformNormalGeometry d r := {
  G with
  D₀ := G.D₀ ∩ {η | (1 / 2 : ℝ) ≤ ‖η‖}
  compact_D₀ := G.compact_D₀.inter_right (isClosed_le continuous_const continuous_norm)
  input_buffer := by
    exact (cthickening_subset_of_subset G.inputBuffer inter_subset_left).trans G.input_buffer }

/-- Reinterpret the SAME phase and amplitude on their smaller certified
support. The input integration domain, inverse, output and all jets are unchanged. -/
def annularData {G : UniformNormalGeometry d r} {C : ℕ → ℝ}
    (F : UniformNormalData G C)
    (hs : ∀ ε ∈ Icc 0 G.ε₀, ∀ x η,
      F.amplitude ε x η ≠ 0 → (1 / 2 : ℝ) ≤ ‖η‖) :
    UniformNormalData (annularGeometry G) C := {
  F with
  amplitude_support := by
    intro ε hε w hw
    exact ⟨(F.amplitude_support ε hε hw).1,
      (F.amplitude_support ε hε hw).2, hs ε hε w.1 w.2 hw⟩
  image_buffer := by
    intro ε hε x hx y hy
    exact (cthickening_subset_of_subset G.inverseBuffer (image_mono inter_subset_left)).trans
      (F.image_buffer ε hε x hx y hy) }

/-- Changing a support certificate does not change the literal oscillatory
operator, for any frequency or epsilon (including its zero fallback). -/
@[simp] theorem annularData_operator {G : UniformNormalGeometry d r} {C : ℕ → ℝ}
    (F : UniformNormalData G C)
    (hs : ∀ ε ∈ Icc 0 G.ε₀, ∀ x η,
      F.amplitude ε x η ≠ 0 → (1 / 2 : ℝ) ≤ ‖η‖) (K ε : ℝ) :
    (annularData F hs).uniformOscillatoryOperator K ε =
      F.uniformOscillatoryOperator K ε := rfl

/-- The actual normalized scalar amplitude vanishes below the original radial
annulus; no lower-frequency support hypothesis is imposed on the parent. -/
theorem scalarSliceAmplitude_annular {n : ℕ} {ξ : Euclidean n} (sec : AdaptedSection ξ)
    (χ : ContDiffBump (0 : Euclidean n))
    (angular : Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ)
    (hn : 1 ≤ n) (j : ℕ) (t : ℝ) (y η : Euclidean (n - 1))
    (h : scalarSliceAmplitude sec χ angular H hn j (t, y, η) ≠ 0) :
    (1 / 2 : ℝ) ≤ ‖η‖ := by
  by_contra hη
  apply h
  ext i
  simp only [scalarSliceAmplitude, normalizedMask_eq_zero_of_le angular H j (le_of_not_ge hη),
    zero_mul, Pi.zero_apply]

/-- The fixed `1/4` actual phase comparison gives a genuine nonzero averaged
transverse gradient on the unchanged original normalized radial support. -/
theorem averagedGradient_gap_of_annular_comparison
    (φ : Euclidean d → Euclidean d → ℝ) (x y η : Euclidean d)
    (hη : (1 / 2 : ℝ) ≤ ‖η‖)
    (hc : ‖averagedGradient φ x y η - η‖ < (1 / 4 : ℝ)) :
    (1 / 4 : ℝ) ≤ ‖averagedGradient φ x y η‖ := by
  have hh : ‖η‖ ≤ ‖averagedGradient φ x y η - η‖ + ‖averagedGradient φ x y η‖ := by
    calc
      ‖η‖ = ‖(η - averagedGradient φ x y η) + averagedGradient φ x y η‖ := by rw [sub_add_cancel]
      _ ≤ ‖η - averagedGradient φ x y η‖ + ‖averagedGradient φ x y η‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev]
  linarith

end JanetCartan.PhysicalScalarChannel
