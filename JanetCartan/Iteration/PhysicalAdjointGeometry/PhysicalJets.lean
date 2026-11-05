module

public import JanetCartan.Iteration.PhysicalAdjointGeometry.PhysicalTransfer

/-!
# Original-support physical jets of the localized trade family

These are the exact inputs consumed by
`PhysicalMean.sampledAdjointMomentTemplate_physical_jet_le`: physical jets of
the actual direction applied to each fixed word direction, and normalized
physical phase jets for the two nonstationary branches. Joint localization
preserves the original coefficient jets; no derivative of the localization
cutoff and no band factor appears on the original compact support.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.PhysicalAdjointGeometry

variable {X Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] {m : ℕ}

/-- Applying a fixed word direction costs only its fixed norm, not an input
frequency power (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_jet_appliedDirection_le {L : X → Euclidean m →L[ℝ] Z}
    (hL : ContDiff ℝ ∞ L) (h : Euclidean m) (x : X) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y ↦ L y h) x‖ ≤ ‖h‖ * ‖iteratedFDeriv ℝ k L x‖ := by
  let P : (Euclidean m →L[ℝ] Z) →L[ℝ] Z := ContinuousLinearMap.apply ℝ Z h
  have hP : ‖P‖ ≤ ‖h‖ := by
    apply P.opNorm_le_bound (norm_nonneg _)
    intro A
    simpa only [P, ContinuousLinearMap.apply_apply, mul_comm] using A.le_opNorm h
  have hb := P.norm_iteratedFDeriv_comp_left (x := x) hL.contDiffAt (by simp : (k : ℕ∞ω) ≤ ∞)
  exact hb.trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))

/-- Physical-only operator jets of the localized family have exactly the
original reserve. The germ comes from the single joint localization, and the
right-hand side is bounded by `exists_primitive_trade_profiles`
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_jet_localized_physicalTrade_slice_le (e : X ≃ₗᵢ[ℝ] Z)
    {L L₀ : Point X m → Euclidean m →L[ℝ] X} (hL : ContDiff ℝ ∞ L)
    (q : Point Z m) (he : L =ᶠ[𝓝 (jointCoordinateEquiv e.symm q)] L₀) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun x ↦ physicalTrade e L (x, q.2)) q.1‖ ≤
      ‖iteratedFDeriv ℝ k L₀ (jointCoordinateEquiv e.symm q)‖ := by
  apply (RawPrimary.AmplitudeGrades.norm_iteratedFDeriv_physical_slice_le
    isOpen_univ (contDiff_physicalTrade e hL).contDiffOn (mem_univ q) k).trans
  apply (norm_jet_physicalTrade_le e hL q k).trans_eq
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]

/-- The actual fixed-word physical coefficient input to the mean adjoint
moment template. This includes every physical-time derivative and no η jet
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_jet_localized_physicalDirection_le (e : X ≃ₗᵢ[ℝ] Z)
    {L L₀ : Point X m → Euclidean m →L[ℝ] X} (hL : ContDiff ℝ ∞ L)
    (q : Point Z m) (he : L =ᶠ[𝓝 (jointCoordinateEquiv e.symm q)] L₀)
    (h : Euclidean m) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun x ↦ physicalTrade e L (x, q.2) h) q.1‖ ≤
      ‖h‖ * ‖iteratedFDeriv ℝ k L₀ (jointCoordinateEquiv e.symm q)‖ := by
  have hs : ContDiff ℝ ∞ (fun x ↦ physicalTrade e L (x, q.2)) :=
    (contDiff_physicalTrade e hL).comp (contDiff_id.prodMk contDiff_const)
  exact (norm_jet_appliedDirection_le hs h q.1 k).trans
    (mul_le_mul_of_nonneg_left (norm_jet_localized_physicalTrade_slice_le e hL q he k) (norm_nonneg h))

/-- The normalized literal phase has physical jets bounded by the same
original averaged covector jets, uniformly for every nonzero input frequency.
This supplies the existing binary mean-phase branch interface without η loss
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_jet_localized_normalized_phase_le (e : X ≃ₗᵢ[ℝ] Z)
    {Y Y₀ : Point X m → Euclidean m} (hY : ContDiff ℝ ∞ Y)
    (q : Point Z m) (he : Y =ᶠ[𝓝 (jointCoordinateEquiv e.symm q)] Y₀)
    {η : Euclidean m} (hη : η ≠ 0) (k : ℕ) :
    ‖iteratedFDeriv ℝ k
      (fun x ↦ inner ℝ (physicalCovector e Y (x, q.2)) η / ‖η‖) q.1‖ ≤
      ‖iteratedFDeriv ℝ k Y₀ (jointCoordinateEquiv e.symm q)‖ := by
  have hs := contDiff_physicalCovector e hY
  have hφ : ContDiff ℝ ∞ (fun p ↦ inner ℝ (physicalCovector e Y p) η / ‖η‖) :=
    (hs.inner ℝ contDiff_const).div_const _
  apply (RawPrimary.AmplitudeGrades.norm_iteratedFDeriv_physical_slice_le
    isOpen_univ hφ.contDiffOn (mem_univ q) k).trans
  apply (norm_jet_normalized_phase_le hs.contDiffAt hη k).trans
  rw [norm_jet_physicalCovector, (he.iteratedFDeriv ℝ k).eq_of_nhds]

end JanetCartan.PhysicalAdjointGeometry
