module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.FullSourceRoot
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.NormalizedSymbol.Transversality

/-!
# Regularity of the original full source covectors

The frozen Hamilton chart retains the energy parameter in addition to the
free source covector. Differentiating its literal eikonal identity in energy
proves determinant regularity at every original source parameter. This removes
the nonzero/characteristic/regularity premises from full-source chart selection
for `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu FrozenPhaseReference LeadingWave.FullModulation
variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
/-- Every frozen covector of the original full source is a nonzero regular
characteristic. The eikonal equation yields characteristicity; its energy
derivative is one, which excludes a zero determinant differential. These
facts come from the SAME retained Hamilton chart, throughout the original
covector ball (`app:lem:common-hamilton-phase`,
`app:ch_response:eq:response-exact-phase`). -/
theorem full_source_frozen_covector_regular {ζ : Euclidean d}
    (hζ : ζ ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius) :
    T.reference.covector (0, ζ) ≠ 0 ∧
      determinant (cubeStress (d + 1)) (T.reference.covector (0, ζ)) = 0 ∧
      fderiv ℝ (determinant (cubeStress (d + 1))) (T.reference.covector (0, ζ)) ≠ 0 := by
  let C := T.reference.chart
  have hq : ((0 : E), ((0 : ℝ), ζ)) ∈ C.target := by
    apply (LeadingWave.FullModulation.inclusion_mem_ball T
      (r := T.family.radius) (w := ((0 : E), ζ))).mpr
    simpa only [mem_ball, Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hζ
  have heq := chartMomentum_eq_of_phase_linear C T.reference.covector
    T.reference.phase_linear hq
  have hs := C.source_admissible _ (C.maps_to_source _ hq)
  have hm := T.reference.flow.state_mem _ hs.1 _ hs.2
  have hne : T.reference.covector (0, ζ) ≠ 0 := by
    have hh := (mem_frozenSymbol_domain _).mp hm
    change C.chartMomentum (0, (0, ζ)) ≠ 0 at hh
    rwa [heq] at hh
  have he := C.eikonal hq
  rw [C.gradient_phase_eq_chartMomentum hq, heq] at he
  change (frozenSymbol (d + 1)).h (0, T.reference.covector (0, ζ)) = 0 at he
  rw [frozenSymbol_h] at he
  have hdet : determinant (cubeStress (d + 1)) (T.reference.covector (0, ζ)) = 0 := by
    rw [determinant_cubeStress]
    exact (mul_eq_zero.mp he).resolve_left (zpow_ne_zero _ (norm_ne_zero_iff.mpr hne))
  refine ⟨hne, hdet, ?_⟩
  intro hzero
  let f : E → ℝ := fun η ↦ normalizedSymbol (fun _ ↦ cubeStress (d + 1)) (0, η)
  have hf : DifferentiableAt ℝ f (T.reference.covector (0, ζ)) := by
    exact (hasFDerivAt_determinant (cubeStress (d + 1)) _).differentiableAt.mul
      ((contDiffAt_determinantNormalization hne).differentiableAt (by simp))
  have hfzero : fderiv ℝ f (T.reference.covector (0, ζ)) = 0 := by
    rw [fderiv_covector_normalizedSymbol_of_determinant_eq_zero _ (0 : E) hne hdet, hzero,
      smul_zero]
  let m : ℝ → E := fun t ↦ C.chartMomentum (0, (t, ζ))
  have hc := (C.contDiffOn_chartMomentum T.reference.momentum_smooth
    T.reference.coordinates_smooth).contDiffAt (C.isOpen_target.mem_nhds hq)
  have hm : DifferentiableAt ℝ m 0 :=
    (hc.comp (0 : ℝ) (contDiffAt_const.prodMk
      (contDiffAt_id.prodMk contDiffAt_const))).differentiableAt (by simp)
  have hevent : (fun t : ℝ ↦ f (m t)) =ᶠ[𝓝 0] (fun t ↦ t) := by
    have ht := (continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousAt
      |>.preimage_mem_nhds (C.isOpen_target.mem_nhds hq)
    filter_upwards [ht] with t ht
    have he := C.eikonal ht
    rw [C.gradient_phase_eq_chartMomentum ht] at he
    exact he
  have hfm : HasFDerivAt f (0 : E →L[ℝ] ℝ) (m 0) := by
    simpa only [m, heq, hfzero] using hf.hasFDerivAt
  have hcomp := hfm.comp 0 hm.hasFDerivAt
  have hz := hcomp.unique ((hasFDerivAt_id (0 : ℝ)).congr_of_eventuallyEq hevent)
  have hbad := congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) hz
  simp at hbad
end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
