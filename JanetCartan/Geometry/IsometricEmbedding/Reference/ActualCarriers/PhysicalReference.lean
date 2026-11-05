module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference

/-!
# Frozen references inside the physical construction ball

The current frame is only controlled on the construction neighborhood in
`app:ch_seed:setup:seed-current`. Refine the state buffer before constructing
its Hamilton family, then carry the physical containment through the decorated
finite-cover construction. This supplies the domain input of
`FrozenPatchData.exists_current_chart_of_frame_closeness` without asking for
control of the immersion outside its prescribed ball.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers
open HamiltonPhase FrozenMenu FrozenPhaseReference

/-- Construct the reference in any prescribed positive physical ball. The
scalar-root uniqueness buffer is shrunk before calling the Hamilton producer;
the resulting chart retains its affine identity and full perturbation sidecar
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem exists_localFrozenReference_in_physical_ball {n : ℕ} {ξ : Euclidean n}
    (hξ : ξ ≠ 0) (hchar : cubeDeterminant ξ = 0) (a : AdaptedSection ξ)
    {b : ℝ} (hb : 0 < b) :
    ∃ N : LocalFrozenReference a,
      ∀ q ∈ N.stateDomain, q.1 ∈ ball (0 : Euclidean n) b := by
  obtain ⟨D, R, hD, hDH, hR, hRD, hinj⟩ := exists_frozenRootBuffer hξ hchar a
  let D' := D ∩ Prod.fst ⁻¹' ball (0 : Euclidean n) b
  let R' := min R (b / 2)
  have hR' : 0 < R' := lt_min hR (half_pos hb)
  have hD' : IsOpen D' := hD.inter (isOpen_ball.preimage continuous_fst)
  have hRD' : closedBall (0, ξ) R' ⊆ D' := by
    intro q hq
    refine ⟨hRD (closedBall_subset_closedBall (min_le_left _ _) hq), ?_⟩
    have hfst : dist q.1 0 ≤ R' := (le_max_left _ _).trans
      (show max (dist q.1 0) (dist q.2 ξ) ≤ R' from hq)
    exact hfst.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hb))
  have hinj' := hinj.mono (closedBall_subset_closedBall (min_le_left R (b / 2)))
  obtain ⟨F⟩ := exists_frozenHamiltonFamily_of_adapted hξ hchar a hD'
    (fun _ hq ↦ hDH hq.1) hR' hRD'
  obtain ⟨V, c, ρ, hV, hξV, hVR, hVzero, hc, hgap, hρ, htarget, hsource⟩ :=
    exists_frozenReferenceNeighborhoods hξ a hR' F
  let N : LocalFrozenReference a := {
    stateDomain := D'
    stateRadius := R'
    state_open := hD'
    state_subset := fun _ hq ↦ hDH hq.1
    stateRadius_pos := hR'
    stateBall_subset := by simpa only [a.baseState_eq] using hRD'
    family := F
    covectorSet := V
    covectorSet_open := hV
    covectorSet_base := hξV
    covectorSet_nonzero := hVzero
    determinantGap := c
    determinantGap_pos := hc
    determinant_gap := hgap
    radius := ρ
    radius_pos := hρ
    covector := F.canonicalMomentum
    phase_linear := fun _ hq ↦ F.phase_eq_canonicalMomentum hinj' hq
    covector_inverse := fun p hp hpchar ↦
      F.canonicalMomentum_eq_of_characteristic hinj' (hVR hp) hpchar
        (F.canonicalDatum_mem (htarget 0 (mem_ball_self hρ) p hp))
    target_contains := htarget
    section_source := hsource }
  exact ⟨N, fun _ hq ↦ hq.2⟩

/-- The finite detecting menu can be chosen with every retained state domain
inside the prescribed physical construction ball. This is unconditional apart
from `5 ≤ n` and positivity of that ball's radius; no phase, root or detector
is assumed. The doubled patch data and full frozen detector survive the final
shrinking (`app:ch_seed:prop:seed-frozen-menu`, Steps 3–4;
`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem exists_frozenReference_coverData_in_physical_ball {n : ℕ} (hn : 5 ≤ n)
    {b : ℝ} (hb : 0 < b) :
    ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∃ d : (a : (i : Fin D.chartCount) × Fin (D.patchCount i)) →
          FrozenPatchData (D.patches a.1 a.2),
        ∀ a, ∀ q ∈ (d a).localReference.stateDomain,
          q.1 ∈ ball (0 : Euclidean n) b := by
  let Decoration := fun P : Patch n ↦
    {d : FrozenPatchData P // ∀ q ∈ d.localReference.stateDomain,
      q.1 ∈ ball (0 : Euclidean n) b}
  have hlocal (k s ξ : Euclidean n) (hseed : CarrierSeed k s ξ) :
      ∃ (P : Patch n) (c C : ℝ), P.IsValid c C ∧ P.toFun 0 = ξ ∧
        (∀ z ∈ parameterCube P.radius,
          c ≤ |fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z
            (EuclideanSpace.single 0 1)|) ∧ Nonempty (Decoration P) := by
    obtain ⟨a⟩ := exists_adaptedSection_of_carrierSeed hn hseed
    have hξ : ξ ≠ 0 := by
      intro hzero
      exact hseed.coordinates_ne_zero ⟨0, by omega⟩ (by simp [hzero])
    obtain ⟨N, hphysical⟩ :=
      exists_localFrozenReference_in_physical_ball hξ hseed.characteristic a hb
    obtain ⟨P, c, C, hP, hcenter, hinc, hbuffer⟩ :=
      exists_valid_patch_in_open hn hseed N.covectorSet_open N.covectorSet_base
    let d : FrozenPatchData P := ⟨ξ, a, N, hcenter, fun z hz ↦ (hbuffer z hz).1,
      fun z hz ↦ (hbuffer z hz).2.1, c, C, hP.2.1,
      fun z hz ↦ (hbuffer z hz).2.2.2⟩
    exact ⟨P, c, C, hP, hcenter, hinc, ⟨⟨d, hphysical⟩⟩⟩
  obtain ⟨D, c, C, hD, hd⟩ := exists_decorated_coverData_of_local_patches hn Decoration hlocal
  let d (a : (i : Fin D.chartCount) × Fin (D.patchCount i)) := Classical.choice (hd a.1 a.2)
  exact ⟨D, c, C, hD, fun a ↦ (d a).val, fun a ↦ (d a).property⟩

end JanetCartan.ActualCarriers
