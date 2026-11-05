module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.IncidenceCover.Bounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.IncidenceCover.Roots.Transversality

/-!
# Centered incidence-root continuation

The scalar implicit-function construction in Step 4 of
`app:ch_seed:prop:seed-frozen-menu`. The patch is fixed, and every field of the
incidence-section specification is proved, including uniform transversality on
the full closed parameter cube.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace JanetCartan.FrozenMenu

open CharacteristicRoot

/-- Continue a centered transverse incidence root by varying only coordinate
zero, keeping the patch fixed. The resulting section is smooth on one open
covector neighborhood, stays in the parameter interior, and retains a positive
uniform derivative bound on the entire closed cube
(`app:ch_seed:prop:seed-frozen-menu`, Step 4). -/
theorem Patch.exists_centered_incidenceSection {n : ℕ} (P : Patch n) (k : Euclidean n) (c C : ℝ)
    (hP : P.IsValid c C) (hinc : incidence k (P.toFun 0) = 0)
    (hb : ∀ z ∈ parameterCube P.radius,
      c ≤ |fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z (EuclideanSpace.single 0 1)|) :
    ∃ (U : Set (Euclidean n)) (root : Euclidean n → Euclidean 3) (d : ℝ),
      IsOpen U ∧ k ∈ U ∧ root k = 0 ∧ 0 < d ∧ P.IsIncidenceSection U root d := by
  let e : Euclidean 3 := EuclideanSpace.single 0 1
  let f : Euclidean n × ℝ → ℝ := fun p ↦ incidence p.1 (P.toFun (p.2 • e))
  have hzero : (0 : ℝ) • e ∈ parameterCube P.radius := by
    simpa using zero_mem_parameterCube hP.1.le
  have hf : ContDiffAt ℝ ∞ f (k, 0) := Patch.contDiffAt_scalar_incidence hP k hzero
  have hd : scalarDerivative f (k, 0) ≠ 0 := by
    have he := Patch.scalarDerivative_incidence_eq hP k hzero
    have hb0 := hb 0 (zero_mem_parameterCube hP.1.le)
    apply abs_pos.mp
    change 0 < |scalarDerivative (fun p : Euclidean n × ℝ ↦
      incidence p.1 (P.toFun (p.2 • EuclideanSpace.single 0 1))) (k, 0)|
    rw [he]
    simpa using hP.2.1.trans_le hb0
  have hf0 : f (k, 0) = 0 := by simpa [f] using hinc
  let H := localRoot hf hd
  let root := fun q ↦ H q • e
  have hH0 : H k = 0 := localRoot_base hf hd
  have hroot0 : root k = 0 := by simp [root, hH0]
  have hH : ContDiffAt ℝ ∞ H k := contDiffAt_localRoot hf hd
  have hroot : ContinuousAt root k := hH.continuousAt.smul continuousAt_const
  have hinterior : ∀ᶠ q in 𝓝 k, root q ∈ parameterInterior P.radius := by
    apply hroot.preimage_mem_nhds
    rw [hroot0]
    exact parameterInterior_mem_nhds hP.1
  have hevent : ∀ᶠ q in 𝓝 k,
      ContDiffAt ℝ 1 H q ∧ root q ∈ parameterInterior P.radius ∧ f (q, H q) = 0 ∧
      ∀ z ∈ parameterCube P.radius,
        c / 2 ≤ |fderiv ℝ (fun w ↦ incidence q (P.toFun w)) z e| := by
    filter_upwards [(hH.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).eventually (by simp),
      hinterior, localRoot_eventually_zero hf hd hf0,
      Patch.eventually_uniform_incidence_bound hP hb]
      with q hq hi hz hg
    exact ⟨hq, hi, hz, hg⟩
  obtain ⟨U, hUsub, hU, hkU⟩ := mem_nhds_iff.mp hevent
  -- Recover smoothness at every point of this fixed neighborhood from the
  -- equation, continuity of the branch, and the uniform nonzero partial.
  have hHU : ContDiffOn ℝ ∞ H U := by
    intro q hq
    have hp := hUsub hq
    have ht : H q • EuclideanSpace.single 0 1 ∈ parameterCube P.radius :=
      fun i ↦ (hp.2.1 i).le
    apply ContDiffAt.contDiffWithinAt
    apply contDiffAt_of_continuous_root (Patch.contDiffAt_scalar_incidence hP q ht)
    · rw [Patch.scalarDerivative_incidence_eq hP q ht]
      exact abs_pos.mp ((half_pos hP.2.1).trans_le (hp.2.2.2 _ ht))
    · exact hp.1.continuousAt
    · filter_upwards [hU.mem_nhds hq] with p hp
      exact (hUsub hp).2.2.1
  refine ⟨U, root, c / 2, hU, hkU, hroot0, half_pos hP.2.1,
    hHU.smul contDiffOn_const, ?_, ?_⟩
  · intro q hq
    have hp := hUsub hq
    refine ⟨hp.2.1, ?_, ?_, hp.2.2.1⟩
    · simp [root, e]
    · simp [root, e]
  · intro q hq
    exact (hUsub hq).2.2.2

end JanetCartan.FrozenMenu
