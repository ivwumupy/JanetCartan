module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.RadialRefinement
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.RadialSegments

/-!
# Finite initial buffers for a fixed radial copy

The source is the image of the actual closed source ball. Compactness chooses
finitely many smaller initial balls inside the image of the original open
flow ball. The common segment buffer is the image of the original closed
range ball. All choices precede the coefficient field.

Consumer: the expanded family in `exists_uniform_nested_physicalDirectLocalizers`
and its independently proved radial flow transport, for
`app:ch_regular:lem:finite-chain` and `app:ch_regular:thm:no-return`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped Topology

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior

open RegularSector.Characteristic

variable {d : ℕ}

/-- Cover the actual dilated source closure by finitely many compact pieces.
Each initial closed ball pulls back strictly inside the original flow ball;
each containing ball contains the entire dilated segment buffer. No root,
coefficient field, or replacement source cover is an input
(`app:ch_regular:lem:finite-chain`). -/
theorem exists_finite_radial_initial_buffers
    {a : ℝ} (ha : 0 < a) (z : RootState (Euclidean d))
    {σ r R : ℝ} (hσr : σ < r) (hσR : σ ≤ R) :
    let S := rootRadialEquiv (d := d) a ha.ne'
    ∃ (N : ℕ) (zj : Fin N → RootState (Euclidean d))
      (rj Rj : Fin N → ℝ) (Uj : Fin N → Set (RootState (Euclidean d))),
      IsCompact (S '' closedBall z R) ∧
      (S '' closedBall z σ = ⋃ j, Uj j) ∧
      ∀ j,
        zj j ∈ S '' closedBall z σ ∧ 0 < rj j ∧ rj j < Rj j ∧
        Uj j = (S '' closedBall z σ) ∩ closedBall (zj j) (rj j) ∧
        IsCompact (Uj j) ∧ Uj j ⊆ closedBall (zj j) (rj j) ∧
        Uj j ⊆ S '' closedBall z σ ∧ Uj j ⊆ S '' closedBall z R ∧
        S.symm '' closedBall (zj j) (rj j) ⊆ closedBall z r ∧
        S.symm '' ball (zj j) (rj j) ⊆ ball z r ∧
        S '' closedBall z R ⊆ closedBall (zj j) (Rj j) := by
  classical
  dsimp only
  let S := rootRadialEquiv (d := d) a ha.ne'
  let K₀ := S '' closedBall z σ
  let K := S '' closedBall z R
  have hK₀ : IsCompact K₀ := (isCompact_closedBall z σ).image S.continuous
  have hK : IsCompact K := (isCompact_closedBall z R).image S.continuous
  have hsmall (w : K₀) : ∃ δ > 0, closedBall (w : RootState (Euclidean d)) δ ⊆
      S.symm ⁻¹' ball z r := by
    apply Metric.nhds_basis_closedBall.mem_iff.mp
    apply (isOpen_ball.preimage S.symm.continuous).mem_nhds
    obtain ⟨v, hv, he⟩ := w.property
    change S.symm w.val ∈ ball z r
    rw [← he, S.symm_apply_apply]
    exact closedBall_subset_ball hσr hv
  choose δ hδ hδsub using hsmall
  have hcover : K₀ ⊆ ⋃ w : K₀, ball w.val (δ w) := by
    intro w hw
    exact mem_iUnion.mpr ⟨⟨w, hw⟩, mem_ball_self (hδ ⟨w, hw⟩)⟩
  obtain ⟨J, hJ⟩ := hK₀.elim_finite_subcover (fun w : K₀ ↦ ball w.val (δ w))
    (fun _ ↦ isOpen_ball) hcover
  let e := (Fintype.equivFin J).symm
  have hlarge (j : J) : ∃ R' > δ j.val, K ⊆ closedBall j.val.val R' :=
    hK.isBounded.subset_closedBall_lt (δ j.val) j.val.val
  choose R' hR' hR'sub using hlarge
  refine ⟨Fintype.card J, (fun j ↦ (e j).val.val), (fun j ↦ δ (e j).val),
    (fun j ↦ R' (e j)), (fun j ↦ K₀ ∩ closedBall (e j).val.val (δ (e j).val)), hK, ?_, ?_⟩
  · apply Subset.antisymm
    · intro w hw
      obtain ⟨v, hv, hwv⟩ := mem_iUnion₂.mp (hJ hw)
      refine mem_iUnion.mpr ⟨e.symm ⟨v, hv⟩, ?_⟩
      simpa only [Equiv.apply_symm_apply] using
        (show w ∈ K₀ ∩ closedBall v.val (δ v) from ⟨hw, ball_subset_closedBall hwv⟩)
    · exact iUnion_subset fun _ ↦ inter_subset_left
  · intro j
    refine ⟨(e j).val.property, hδ _, hR' _, rfl,
      hK₀.inter_right isClosed_closedBall, inter_subset_right, inter_subset_left,
      inter_subset_left.trans (image_mono (closedBall_subset_closedBall hσR)), ?_, ?_, hR'sub _⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact ball_subset_closedBall (hδsub _ hv)
    · rintro _ ⟨v, hv, rfl⟩
      exact hδsub _ (ball_subset_closedBall hv)

/-- The constructor's actual radii satisfy the strict nesting required above:
`R = 3ρ`, `r = 3ρ/2`, and `2σ ≤ 3ρ/4`. This is the numerical input exported by
`UniformGeometry.exists_uniform_fieldRoot_twoTimeHamiltonPhase` and retained
by `exists_uniform_fieldRoot_conicGeometry`
(`app:ch_regular:lem:finite-chain`). -/
theorem constructor_source_radius_nesting {ρ σ : ℝ} (hρ : 0 < ρ)
    (hσ : 2 * σ ≤ (3 * ρ) / 4) : σ < (3 * ρ) / 2 ∧ σ ≤ 3 * ρ := by
  constructor <;> linarith

end JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior
