module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PencilNullvectors

/-!
# The actual two-time chart on a fixed minor patch

In `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`, the
nullvectors and the Hamilton phase must use the same root neighborhood.
We first restrict the constructed pencil root to its nonvanishing minor
patch, then construct the flow there. Thus its whole local flowout stays in
that patch. Smoothness of the transported state is retained for the actual
potential `lᵀPk`, which differentiates the nullvector after substitution of
the phase covector. No phase, flow, inverse or normalized nullvector is an
input to this construction. Uniformity over a coefficient neighborhood and
normalized symbol estimates remain separate obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Matrix
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic

open ActualCarriers

variable {n d : ℕ}

/-- Construct a root and choose its fixed minor before constructing the flow.
Every kernel and normalization assertion is proved for the actual pencil
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_pencilRoot_minor_domain
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    {Q : Euclidean n → Fin n → MetricTensor n} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (z : RootState (Euclidean d)) (τ : ℝ) (hx : e.symm (z.1, z.2.1) ∈ Ω)
    (hξ : e.symm (τ, z.2.2) ≠ 0)
    (hp : determinant (Q (e.symm (z.1, z.2.1))) (e.symm (τ, z.2.2)) = 0)
    (hgap : fderiv ℝ (determinant (Q (e.symm (z.1, z.2.1))))
      (e.symm (τ, z.2.2)) (e.symm (1, 0)) ≠ 0) :
    ∃ D : Set (RootState (Euclidean d)), ∃ h : RootState (Euclidean d) → ℝ,
      ∃ r c : Fin n,
      IsOpen D ∧ z ∈ D ∧ h z = τ ∧ ContDiffOn ℝ ∞ h D ∧
      (∀ w ∈ D, ∀ᶠ a : ℝ in 𝓝 1, h (w.1, (w.2.1, a • w.2.2)) = a * h w) ∧
      ContDiffOn ℝ ∞ (fun w ↦ minorRightNullvector (rootPencil e Q h w) r c) D ∧
      ContDiffOn ℝ ∞ (fun w ↦ minorLeftNullvector (rootPencil e Q h w)
        (rootTimeCoefficient e Q w) r c) D ∧
      ∀ w ∈ D,
        e.symm (w.1, w.2.1) ∈ Ω ∧ w.2.2 ≠ 0 ∧
        (rootPencil e Q h w).det = 0 ∧
        fderiv ℝ Matrix.det (rootPencil e Q h w) (rootTimeCoefficient e Q w) ≠ 0 ∧
        (rootPencil e Q h w).adjugate r c ≠ 0 ∧
        minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c ≠ 0 ∧
        rootPencil e Q h w *ᵥ minorRightNullvector (rootPencil e Q h w) r c = 0 ∧
        minorLeftNullvector (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c
          ᵥ* rootPencil e Q h w = 0 ∧
        minorLeftNullvector (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c ⬝ᵥ
          (rootTimeCoefficient e Q w *ᵥ minorRightNullvector (rootPencil e Q h w) r c) = 1 := by
  obtain ⟨D, h, hD, hz, hbase, hh, hroot, hscale⟩ :=
    exists_pencilRoot_domain e hΩ hQ z τ hx hξ hp hgap
  obtain ⟨r, c, V, hV, hzV, hVD, hk, hl, hminor⟩ :=
    exists_rootPencil_minor_neighborhood e hQ hD hh (fun w hw ↦ (hroot w hw).1)
      (fun w hw ↦ (hroot w hw).2.2.1) hz (by simpa only [hbase] using hgap)
  refine ⟨V, h, r, c, hV, hzV, hbase, hh.mono hVD, ?_, hk, hl, ?_⟩
  · intro w hw
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with a ha
    exact (hscale w (hVD hw) a ha).2
  · intro w hw
    obtain ⟨hphys, hη, hdet, hder⟩ := hroot w (hVD hw)
    obtain ⟨hm, ht, hkr, hlr, hn, _⟩ := hminor w hw
    exact ⟨hphys, hη, hdet, by rwa [rootPencil_time_derivative], hm, ht, hkr, hlr, hn⟩

/-- Construct the two-time Hamilton chart entirely inside the selected
actual minor patch. In particular the smooth transported state needed to
form `lᵀPk` uses this same inverse chart, and both time identities come from
the retained full phase differential
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_pencil_minor_twoTimeChart
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    {Q : Euclidean n → Fin n → MetricTensor n} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (z : RootState (Euclidean d)) (τ : ℝ) (hx : e.symm (z.1, z.2.1) ∈ Ω)
    (hξ : e.symm (τ, z.2.2) ≠ 0)
    (hp : determinant (Q (e.symm (z.1, z.2.1))) (e.symm (τ, z.2.2)) = 0)
    (hgap : fderiv ℝ (determinant (Q (e.symm (z.1, z.2.1))))
      (e.symm (τ, z.2.2)) (e.symm (1, 0)) ≠ 0) :
    ∃ D : Set (RootState (Euclidean d)), ∃ h : RootState (Euclidean d) → ℝ,
      ∃ r c : Fin n, ∃ Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d),
      ∃ C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)),
      ∃ δ > (0 : ℝ),
      IsOpen D ∧ z ∈ D ∧ h z = τ ∧ ContDiffOn ℝ ∞ h D ∧
      ContDiffOn ℝ ∞ (fun w ↦ minorRightNullvector (rootPencil e Q h w) r c) D ∧
      ContDiffOn ℝ ∞ (fun w ↦ minorLeftNullvector (rootPencil e Q h w)
        (rootTimeCoefficient e Q w) r c) D ∧
      (∀ w ∈ D, e.symm (w.1, w.2.1) ∈ Ω ∧ w.2.2 ≠ 0 ∧
        (rootPencil e Q h w).det = 0 ∧
        fderiv ℝ Matrix.det (rootPencil e Q h w) (rootTimeCoefficient e Q w) ≠ 0 ∧
        (rootPencil e Q h w).adjugate r c ≠ 0 ∧
        minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c ≠ 0) ∧
      (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ ∧
      ContDiffOn ℝ ∞ C C.source ∧ ContDiffOn ℝ ∞ C.symm C.target ∧
      ContDiffOn ℝ ∞ (fun q ↦ twoTimeState Φ (C.symm q)) C.target ∧
      (∀ q ∈ C.target, twoTimeState Φ (C.symm q) ∈ D ∧
        (twoTimeState Φ (C.symm q)).1 = q.1) ∧
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧
      (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) ∧
      ball z.1 δ ×ˢ (ball z.1 δ ×ˢ ball z.2 δ) ⊆ C.source ∧
      (∀ w ∈ ball z.1 δ ×ˢ ball z.2 δ, Φ (w, 0) = w ∧ w ∈ D) ∧
      (∀ q ∈ ball z.1 δ ×ˢ (ball z.1 δ ×ˢ ball z.2 δ),
        HasDerivAt (fun u ↦ Φ (q.2, u))
          (rootHamiltonField h (twoTimeState Φ q)) (q.1 - q.2.1)) := by
  obtain ⟨D, h, r, c, hD, hz, hbase, hh, hhom, hk, hl, hroot⟩ :=
    exists_pencilRoot_minor_domain e hΩ hQ z τ hx hξ hp hgap
  obtain ⟨R, _, ε, _, Φ, C, _, hi, hd, hm, hs, hclock, hC, hsource, hzC, _,
    hCf, hCs, hphase, hdiff, _⟩ := exists_localTwoTimeHamiltonPhase hD hh hhom hz
  obtain ⟨δ, hδ, hbox⟩ := exists_twoTime_transport_box hzC
  refine ⟨D, h, r, c, Φ, C, δ, hδ, hD, hz, hbase, hh, hk, hl, ?_, hC,
    hCf, hCs, hs.comp hCs (fun _ hq ↦ hsource (C.map_target hq)), ?_,
    hphase, hdiff, hbox, ?_, ?_⟩
  · intro w hw
    obtain ⟨hx, hη, hdet, hder, hm, ht, _⟩ := hroot w hw
    exact ⟨hx, hη, hdet, hder, hm, ht⟩
  · intro q hq
    have hs := hsource (C.map_target hq)
    exact ⟨hm _ hs.1 _ hs.2,
      (hclock _ hs).trans (twoTimeChart_inverse_coordinates hC hq).1⟩
  · intro w hw
    have hws := hsource (hbox (show (w.1, w) ∈ _ from ⟨hw.1, hw⟩))
    have hwi := hi w hws.1
    refine ⟨hwi, ?_⟩
    simpa only [twoTimeState, sub_self, hwi] using hm w hws.1 0 (by simpa using hws.2)
  · intro q hq
    have hs := hsource (hbox hq)
    exact hd q.2 hs.1 (q.1 - q.2.1) hs.2

end JanetCartan.RegularSector.Characteristic
