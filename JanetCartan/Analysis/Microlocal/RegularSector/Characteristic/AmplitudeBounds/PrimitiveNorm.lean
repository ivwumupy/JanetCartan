module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.TransportedPrimitives
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.PhysicalAction
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.RowPullback

/-!
# The additive primitive quantity for the literal amplitudes

The six summands are measured on four explicitly specified compact domains.
This is the primitive right side of `app:ch_regular_base:lem:characteristic-kernel`
and `app:ch_regular_base:eq:energy-complete-residual`, not an amplitude assumption.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds

variable {n d : ℕ}

/-- One additive high quantity for the actual characteristic amplitudes.
`KQ` is the physical coefficient domain, `Kz` the root-state domain, `KΦ`
the initial-state/elapsed-time domain, and `KC` the physical two-time domain
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def pencilPrimitiveNorm (KQ : Set (Euclidean n)) (Kz : Set (RootState (Euclidean d)))
    (KΦ : Set (RootState (Euclidean d) × ℝ)) (KC : Set (TwoTimePoint (Euclidean d)))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (h σ : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (Y : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) (m : ℕ) : ℝ :=
  1 + cNorm KQ m Q + cNorm KQ m B + cNorm Kz m h + cNorm Kz m σ +
    cNorm KΦ m Φ + cNorm KC m Y

/-- Smoothness and the original gaps already imply smoothness of the literal
signed datum on the interior root ball; no datum regularity is assumed
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffOn_pencilSignedDatum_ball
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean n)} {D : Set (RootState (Euclidean d))}
    {Q : Euclidean n → Fin n → MetricTensor n} {h σ : RootState (Euclidean d) → ℝ}
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hh : ContDiffOn ℝ ∞ h D) (hσ : ContDiffOn ℝ ∞ σ D)
    (hphys : MapsTo (rootPhysicalPosition e) D Ω)
    (z : RootState (Euclidean d)) (L : ℝ) (hK : closedBall z L ⊆ D)
    (r c : Fin n) (hgaps : ∀ w ∈ closedBall z L,
      (rootPencil e Q h w).adjugate r c ≠ 0 ∧
      minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c ≠ 0) :
    ContDiffOn ℝ ∞ (pencilSignedDatum e Q h r c σ) (ball z L) := by
  have hsub : ball z L ⊆ D := ball_subset_closedBall.trans hK
  have hpair : ContDiffOn ℝ ∞ (fun w ↦ (rootPencil e Q h w,
      rootTimeCoefficient e Q w)) (ball z L) :=
    ((contDiffOn_rootPencil e hQ hh hphys).prodMk
    (contDiffOn_rootTimeCoefficient e hQ hphys)).mono hsub
  have hmap : MapsTo (fun w ↦ (rootPencil e Q h w, rootTimeCoefficient e Q w))
      (ball z L) (minorNullvectorDomain r c) :=
    fun w hw ↦ hgaps w (ball_subset_closedBall hw)
  have hl := (minorNullvectorDomain_regular r c (m := ∞)).2.2.comp hpair hmap
  change ContDiffOn ℝ ∞ (fun w ↦ σ w • minorLeftNullvector (rootPencil e Q h w)
    (rootTimeCoefficient e Q w) r c) (ball z L)
  exact (hσ.mono hsub).smul hl

/-- Restricting a smooth primitive to a smaller compact domain preserves its
joint norm. Used to reconcile the nested transport and amplitude boxes in
`app:ch_regular_base:lem:characteristic-kernel`. -/
theorem cNorm_restrict_of_smooth {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {K J U : Set E}
    (hKJ : K ⊆ J) (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (m : ℕ) : cNorm K m f ≤ cNorm J m f :=
  cNorm_mono_set_of_contDiffAt hKJ hJ
    (fun y hy ↦ (hf.contDiffAt (hU.mem_nhds (hJU hy))).of_le (by simp))

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds
