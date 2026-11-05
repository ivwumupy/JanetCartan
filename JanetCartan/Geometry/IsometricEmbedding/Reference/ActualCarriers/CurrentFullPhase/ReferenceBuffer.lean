module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PhysicalReference
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.TransverseCompatibility

/-!
# Retaining a transverse state buffer for the concrete reference

The root/ODE/inverse uniqueness argument for the current full phase needs a
transverse gap on the whole state ball, not just on the characteristic patch.
Construct that gap before the frozen Hamilton family and before the final
patch shrinking in `app:ch_seed:prop:seed-actual-menu`, Step 1. The consumer is
identification of the current low-order charts with the tame continuous family.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase
open HamiltonPhase FrozenMenu FrozenPhaseReference

/-- The local frozen reference can be constructed inside any prescribed
physical ball with a transverse gap on its entire closed state ball. The
energy/tangential-momentum injectivity witness is retained as well. All these
properties are proved before the patch and incidence-cover shrinking
(`app:ch_seed:prop:seed-actual-menu`, Step 1; `app:lem:common-hamilton-phase`). -/
theorem exists_transverse_localFrozenReference_in_physical_ball {n : ℕ} {ξ : Euclidean n}
    (hξ : ξ ≠ 0) (hchar : cubeDeterminant ξ = 0) (a : AdaptedSection ξ)
    {b : ℝ} (hb : 0 < b) :
    ∃ N : LocalFrozenReference a,
      (∀ q ∈ N.stateDomain, q.1 ∈ ball (0 : Euclidean n) b) ∧
      Set.InjOn (fun p : Euclidean n ↦
        ((frozenSymbol n).h (0, p), a.embedding.toContinuousLinearMap.adjoint p))
        (closedBall ξ N.stateRadius) ∧
      ∃ c > 0, ∀ q ∈ closedBall (0, ξ) N.stateRadius,
        c ≤ |⟪(frozenSymbol n).hp q, a.normal⟫_ℝ| := by
  obtain ⟨D, R, hD, hDH, hR, hRD, hinj⟩ := exists_frozenRootBuffer hξ hchar a
  let D' := D ∩ Prod.fst ⁻¹' ball (0 : Euclidean n) b
  let R' := min R (b / 2)
  have hR' : 0 < R' := lt_min hR (half_pos hb)
  have hD' : IsOpen D' := hD.inter (isOpen_ball.preimage continuous_fst)
  have hDH' : D' ⊆ (frozenSymbol n).domain := fun _ hq ↦ hDH hq.1
  have hRD' : closedBall (0, ξ) R' ⊆ D' := by
    intro q hq
    refine ⟨hRD (closedBall_subset_closedBall (min_le_left _ _) hq), ?_⟩
    have hfst : dist q.1 0 ≤ R' := (le_max_left _ _).trans
      (show max (dist q.1 0) (dist q.2 ξ) ≤ R' from hq)
    exact hfst.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hb))
  obtain ⟨r, δ, c, hr, hrR, hδ, hc, hrD, hgap⟩ :=
    exists_uniform_transverse_stateBall (frozenSymbol n) hD' hDH'
      ((frozenSymbol_smooth n).mono hDH') hR' hRD' a.normal
        (frozenSymbol_transverse_pos hξ hchar a.determinant_positive).ne'
  have hinj' := hinj.mono (closedBall_subset_closedBall
    (hrR.le.trans (min_le_left R (b / 2))))
  have hgap₀ : ∀ q ∈ closedBall (0, ξ) r,
      c ≤ |⟪(frozenSymbol n).hp q, a.normal⟫_ℝ| := by
    apply hgap (frozenSymbol n) hDH' ((frozenSymbol_smooth n).mono hDH')
    have hz : cNorm (closedBall (0, ξ) R') 3
        (fun z ↦ (frozenSymbol n).h z - (frozenSymbol n).h z) = 0 := by
      have heq : (fun z : Euclidean n × Euclidean n ↦
          (frozenSymbol n).h z - (frozenSymbol n).h z) =
          (0 : Euclidean n × Euclidean n → ℝ) := by
        funext z
        simp
      rw [heq]
      exact cNorm_zero _ _
    exact hz.le.trans hδ.le
  obtain ⟨F⟩ := exists_frozenHamiltonFamily_of_adapted hξ hchar a hD' hDH' hr hrD
  obtain ⟨V, cV, ρ, hV, hξV, hVR, hVzero, hcV, hdet, hρ, htarget, hsource⟩ :=
    exists_frozenReferenceNeighborhoods hξ a hr F
  let N : LocalFrozenReference a := {
    stateDomain := D'
    stateRadius := r
    state_open := hD'
    state_subset := hDH'
    stateRadius_pos := hr
    stateBall_subset := by simpa only [a.baseState_eq] using hrD
    family := F
    covectorSet := V
    covectorSet_open := hV
    covectorSet_base := hξV
    covectorSet_nonzero := hVzero
    determinantGap := cV
    determinantGap_pos := hcV
    determinant_gap := hdet
    radius := ρ
    radius_pos := hρ
    covector := F.canonicalMomentum
    phase_linear := fun _ hq ↦ F.phase_eq_canonicalMomentum hinj' hq
    covector_inverse := fun p hp hpchar ↦
      F.canonicalMomentum_eq_of_characteristic hinj' (hVR hp) hpchar
        (F.canonicalDatum_mem (htarget 0 (mem_ball_self hρ) p hp))
    target_contains := htarget
    section_source := hsource }
  exact ⟨N, fun _ hq ↦ hq.2, hinj', c, hc, hgap₀⟩

/-- The retained whole-ball gap persists under an explicit scalar `C³`
threshold on that same ball. This is the primitive hypothesis used by
`ProjectionChart.coordinates_eq_on_transverse_overlap`; it does not assume
any equality or comparison of charts (`app:lem:common-hamilton-phase`). -/
theorem transverse_gap_of_localFrozenReference_closeness {n : ℕ} {ξ : Euclidean n}
    {a : AdaptedSection ξ} (N : LocalFrozenReference a) {c : ℝ} (_hc : 0 < c)
    (hgap : ∀ q ∈ closedBall (0, ξ) N.stateRadius,
      c ≤ |⟪(frozenSymbol n).hp q, a.normal⟫_ℝ|)
    (H : HomogeneousSymbol (Euclidean n)) (hDH : N.stateDomain ⊆ H.domain)
    (hH : ContDiffOn ℝ ∞ H.h N.stateDomain)
    (hclose : cNorm (closedBall (0, ξ) N.stateRadius) 3
      (fun q ↦ H.h q - (frozenSymbol n).h q) ≤ c / 2) :
    ∀ q ∈ closedBall (0, ξ) N.stateRadius, c / 2 ≤ |⟪H.hp q, a.normal⟫_ℝ| := by
  have hball : closedBall (0, ξ) N.stateRadius ⊆ N.stateDomain := by
    simpa only [a.baseState_eq] using N.stateBall_subset
  intro q hq
  have hdiff := abs_normal_velocity_sub_le_cNorm_three H (frozenSymbol n)
    N.state_open hDH N.state_subset (hH.of_le (by simp))
    (((frozenSymbol_smooth n).mono N.state_subset).of_le (by simp))
    (isCompact_closedBall _ _) hball a.normal hq
  rw [a.normal_unit, mul_one] at hdiff
  have hdiff' := hdiff.trans hclose
  have habs := abs_sub_abs_le_abs_sub ⟪(frozenSymbol n).hp q, a.normal⟫_ℝ
    ⟪H.hp q, a.normal⟫_ℝ
  rw [abs_sub_comm] at habs
  linarith [hgap q hq]

/-- Carry the constructed whole-state-ball transverse and root witnesses
through the final patch shrinking, centered incidence sections and finite
detecting cover. The full detector inequality and the doubled closed patch
conditions are retained by the existing decorated-cover construction
(`app:ch_seed:prop:seed-frozen-menu`, Steps 3–4;
`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem exists_transverse_frozenReference_coverData_in_physical_ball {n : ℕ}
    (hn : 5 ≤ n) {b : ℝ} (hb : 0 < b) :
    ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∃ d : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          FrozenPatchData (D.patches i.1 i.2),
        ∀ i,
          (∀ q ∈ (d i).localReference.stateDomain, q.1 ∈ ball (0 : Euclidean n) b) ∧
          Set.InjOn (fun p : Euclidean n ↦
            ((frozenSymbol n).h (0, p),
              (d i).adapted.embedding.toContinuousLinearMap.adjoint p))
            (closedBall (d i).center (d i).localReference.stateRadius) ∧
          ∃ γ > 0, ∀ q ∈ closedBall (0, (d i).center) (d i).localReference.stateRadius,
            γ ≤ |⟪(frozenSymbol n).hp q, (d i).adapted.normal⟫_ℝ| := by
  let Decoration (P : Patch n) := {d : FrozenPatchData P //
    (∀ q ∈ d.localReference.stateDomain, q.1 ∈ ball (0 : Euclidean n) b) ∧
    Set.InjOn (fun p : Euclidean n ↦
      ((frozenSymbol n).h (0, p), d.adapted.embedding.toContinuousLinearMap.adjoint p))
      (closedBall d.center d.localReference.stateRadius) ∧
    ∃ γ > 0, ∀ q ∈ closedBall (0, d.center) d.localReference.stateRadius,
      γ ≤ |⟪(frozenSymbol n).hp q, d.adapted.normal⟫_ℝ|}
  have hlocal : ∀ (k s ξ : Euclidean n), CarrierSeed k s ξ →
      ∃ (P : Patch n) (c C : ℝ), P.IsValid c C ∧ P.toFun 0 = ξ ∧
        (∀ z ∈ parameterCube P.radius,
          c ≤ |fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z (EuclideanSpace.single 0 1)|) ∧
        Nonempty (Decoration P) := by
    intro k s ξ hseed
    obtain ⟨a⟩ := exists_adaptedSection_of_carrierSeed hn hseed
    have hξ : ξ ≠ 0 := by
      intro hzero
      exact hseed.coordinates_ne_zero ⟨0, by omega⟩ (by simp [hzero])
    obtain ⟨N, hphysical, hinj, hgap⟩ :=
      exists_transverse_localFrozenReference_in_physical_ball hξ hseed.characteristic a hb
    obtain ⟨P, c, C, hP, hcenter, hinc, hbuffer⟩ :=
      exists_valid_patch_in_open hn hseed N.covectorSet_open N.covectorSet_base
    let d : FrozenPatchData P := ⟨ξ, a, N, hcenter,
      fun z hz ↦ (hbuffer z hz).1, fun z hz ↦ (hbuffer z hz).2.1,
      c, C, hP.2.1, fun z hz ↦ (hbuffer z hz).2.2.2⟩
    exact ⟨P, c, C, hP, hcenter, hinc, ⟨⟨d, hphysical, hinj, hgap⟩⟩⟩
  obtain ⟨D, c, C, hD, hd⟩ :=
    exists_decorated_coverData_of_local_patches hn Decoration hlocal
  let d (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) := Classical.choice (hd i.1 i.2)
  exact ⟨D, c, C, hD, fun i ↦ (d i).val, fun i ↦ (d i).property⟩

end JanetCartan.ActualCarriers.CurrentFullPhase
