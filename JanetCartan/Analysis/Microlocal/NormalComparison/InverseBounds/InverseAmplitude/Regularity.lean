module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InverseAmplitude.Support
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InverseAmplitude.Determinant

/-!
# Smooth zero extensions of the inverse normal amplitude

Local ambient extensions, including parameter endpoints, justify both zero
extensions in Step 1 of `app:ch_osc:prop:osc-normal`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.NormalComparison
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- Smooth local parameter extensions of the full inverse amplitude on the
physical boxes and the entire output space, including the boundary of the
output chart (`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem UniformNormalData.maskFreeInverseAmplitude_exists_contDiffAt_extension
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {x y : Euclidean n} (hx : x ∈ G.X) (hy : y ∈ G.X) (v : Euclidean n) :
    ∃ b : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) → Matrix (Fin r) (Fin r) ℂ,
      ContDiffAt ℝ ∞ b (ε, (x, (y, v))) ∧
      b (ε, (x, (y, v))) = F.maskFreeInverseAmplitude ε x y v ∧
      ∀ᶠ q in 𝓝 (ε, (x, (y, v))),
        q.1 ∈ Icc 0 G.ε₀ → q.2.1 ∈ G.X → q.2.2.1 ∈ G.X →
          b q = F.maskFreeInverseAmplitude q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  classical
  let P := ℝ × (Euclidean n × (Euclidean n × Euclidean n))
  let p : P := (ε, (x, (y, v)))
  by_cases hv : v ∈ G.V
  · obtain ⟨g, hg, he, hev⟩ := F.inverseChart_exists_contDiffAt_extension hε hx hy hv
    let u := F.inverseChart ε x y v
    have hu : u ∈ G.D := F.inverseChart_mem hε hx hy hv
    let T : P → P := fun q ↦ (q.1, (q.2.1, (q.2.2.1, g q)))
    let a : P → Matrix (Fin r) (Fin r) ℂ := fun q ↦
      |(fderiv ℝ (averagedGradient (F.phase q.1) q.2.1 q.2.2.1) q.2.2.2).det|⁻¹ •
        normalAmplitude (F.amplitude q.1) q.2.1 q.2.2.1 q.2.2.2
    have ha : ContDiffAt ℝ ∞ a (ε, (x, (y, u))) :=
      (F.reciprocalAbsJacobian_contDiffAt ⟨hε, hx, hy, hu⟩).smul
        (F.normalAmplitude_contDiffOn_joint.contDiffAt
          ((F.isOpen_parameterDomain.prod (G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D))).mem_nhds
            ⟨F.parameter_subset hε, hx, hy, hu⟩))
    have hT : ContDiffAt ℝ ∞ T p :=
      contDiffAt_fst.prodMk (contDiffAt_snd.fst.prodMk (contDiffAt_snd.snd.fst.prodMk hg))
    have hTp : T p = (ε, (x, (y, u))) := by simp [T, p, u, he]
    refine ⟨a ∘ T, (hTp.symm ▸ ha).comp p hT, ?_, ?_⟩
    · simp [a, T, he, maskFreeInverseAmplitude, hv,
        inverseJacobianAmplitude]
    · have hvN : ∀ᶠ q : P in 𝓝 p, q.2.2.2 ∈ G.V :=
        continuousAt_snd.snd.snd (G.isOpen_V.mem_nhds hv)
      filter_upwards [hev, hvN] with q hq hqV
      intro hqε hqx hqy
      change q.2.2.2 ∈ G.V at hqV
      simp [a, T, hq hqε hqx hqy,
        maskFreeInverseAmplitude, hqV, inverseJacobianAmplitude]
  · refine ⟨fun _ ↦ 0, contDiffAt_const, ?_, ?_⟩
    · simp [maskFreeInverseAmplitude, hv]
    · have hvN : ∀ᶠ q : P in 𝓝 p, q.2.2.2 ∈ ball v G.inverseBuffer :=
        continuousAt_snd.snd.snd (isOpen_ball.mem_nhds (mem_ball_self G.inverseBuffer_pos))
      filter_upwards [hvN] with q hq
      intro hqε hqx hqy
      exact (F.maskFreeInverseAmplitude_eq_zero_near_chart_compl hqε hqx hqy hv
        (by
          have hd : dist q.2.2.2 v < G.inverseBuffer := hq
          simpa only [dist_comm] using hd.le)).symm

/-- Joint smoothness on the admissible interval and the full output space
(`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem UniformNormalData.maskFreeInverseAmplitude_contDiffOn
    (F : UniformNormalData G C) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) ↦
      F.maskFreeInverseAmplitude q.1 q.2.1 q.2.2.1 q.2.2.2)
      (Icc 0 G.ε₀ ×ˢ (G.X ×ˢ (G.X ×ˢ univ))) := by
  intro p hp
  obtain ⟨b, hb, he, hev⟩ :=
    F.maskFreeInverseAmplitude_exists_contDiffAt_extension hp.1 hp.2.1 hp.2.2.1 p.2.2.2
  apply hb.contDiffWithinAt.congr_of_eventuallyEq _ he.symm
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hqs
  exact (hq hqs.1 hqs.2.1 hqs.2.2.1).symm

/-- Smooth local parameter extensions of the physical zero extension at
all spatial points (`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem UniformNormalData.extendedInverseAmplitude_exists_contDiffAt_extension
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (z : Euclidean n × (Euclidean n × Euclidean n)) :
    ∃ b : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) → Matrix (Fin r) (Fin r) ℂ,
      ContDiffAt ℝ ∞ b (ε, z) ∧ b (ε, z) = F.extendedInverseAmplitude ε z ∧
      ∀ᶠ q in 𝓝 (ε, z), q.1 ∈ Icc 0 G.ε₀ → b q = F.extendedInverseAmplitude q.1 q.2 := by
  classical
  let P := ℝ × (Euclidean n × (Euclidean n × Euclidean n))
  by_cases hz : z.1 ∈ G.X₀ ∧ z.2.1 ∈ G.X₀
  · have hx := G.X₀_subset hz.1
    have hy := G.X₀_subset hz.2
    obtain ⟨b, hb, he, hev⟩ :=
      F.maskFreeInverseAmplitude_exists_contDiffAt_extension hε hx hy z.2.2
    refine ⟨b, hb, he.trans (F.extendedInverseAmplitude_eq_maskFree hε z).symm, ?_⟩
    have hxN : ∀ᶠ q : P in 𝓝 (ε, z), q.2.1 ∈ G.X :=
      continuousAt_snd.fst (G.isOpen_X.mem_nhds hx)
    have hyN : ∀ᶠ q : P in 𝓝 (ε, z), q.2.2.1 ∈ G.X :=
      continuousAt_snd.snd.fst (G.isOpen_X.mem_nhds hy)
    filter_upwards [hev, hxN, hyN] with q hq hqx hqy
    intro hqε
    exact (hq hqε hqx hqy).trans (F.extendedInverseAmplitude_eq_maskFree hqε q.2).symm
  · have hz' := not_and_or.mp hz
    have hz0 : F.extendedInverseAmplitude ε z = 0 := by
      rw [F.extendedInverseAmplitude_eq_maskFree hε]
      exact F.maskFreeInverseAmplitude_eq_zero_of_not_mem_physical hε hz' z.2.2
    refine ⟨fun _ ↦ 0, contDiffAt_const, hz0.symm, ?_⟩
    have hN : ∀ᶠ q : P in 𝓝 (ε, z), q.2.1 ∉ G.X₀ ∨ q.2.2.1 ∉ G.X₀ := by
      rcases hz' with hx | hy
      · filter_upwards [continuousAt_snd.fst (G.compact_X₀.isClosed.isOpen_compl.mem_nhds hx)] with q hq
        exact Or.inl hq
      · filter_upwards [continuousAt_snd.snd.fst (G.compact_X₀.isClosed.isOpen_compl.mem_nhds hy)] with q hq
        exact Or.inr hq
    filter_upwards [hN] with q hq
    intro hqε
    rw [F.extendedInverseAmplitude_eq_maskFree hqε,
      F.maskFreeInverseAmplitude_eq_zero_of_not_mem_physical hqε hq]

/-- The physical zero extension is globally smooth in all spatial variables
for every admissible parameter (`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem UniformNormalData.extendedInverseAmplitude_contDiff
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) :
    ContDiff ℝ ∞ (F.extendedInverseAmplitude ε) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  obtain ⟨b, hb, _, hev⟩ := F.extendedInverseAmplitude_exists_contDiffAt_extension hε z
  have hi : ContinuousAt (fun w : Euclidean n × (Euclidean n × Euclidean n) ↦ (ε, w)) z :=
    continuousAt_const.prodMk continuousAt_id
  apply (hb.comp z (contDiffAt_const.prodMk contDiffAt_id)).congr_of_eventuallyEq
  filter_upwards [hi hev] with w hw
  exact (hw hε).symm

/-- Outside the open spatial chart, the physical extension is identically
zero locally. This transfers chart jet bounds to global bounds in Step 1
of `app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.extendedInverseAmplitude_eventuallyEq_zero
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {z : Euclidean n × (Euclidean n × Euclidean n)}
    (hz : z ∉ G.X ×ˢ (G.X ×ˢ G.V)) :
    F.extendedInverseAmplitude ε =ᶠ[𝓝 z] (fun _ ↦ 0) := by
  classical
  by_cases hxy : z.1 ∈ G.X₀ ∧ z.2.1 ∈ G.X₀
  · have hv : z.2.2 ∉ G.V := fun hv ↦ hz ⟨G.X₀_subset hxy.1, G.X₀_subset hxy.2, hv⟩
    have hN : ∀ᶠ q : Euclidean n × (Euclidean n × Euclidean n) in 𝓝 z,
        q.2.2 ∈ ball z.2.2 G.inverseBuffer :=
      continuousAt_snd.snd (isOpen_ball.mem_nhds (mem_ball_self G.inverseBuffer_pos))
    filter_upwards [hN] with q hq
    by_cases hqxy : q.1 ∈ G.X ∧ q.2.1 ∈ G.X
    · rw [F.extendedInverseAmplitude_eq ε hqxy.1 hqxy.2]
      exact F.maskFreeInverseAmplitude_eq_zero_near_chart_compl hε hqxy.1 hqxy.2 hv
        (by
          have hd : dist q.2.2 z.2.2 < G.inverseBuffer := hq
          simpa only [dist_comm] using hd.le)
    · simp [extendedInverseAmplitude, hqxy]
  · have hN : ∀ᶠ q : Euclidean n × (Euclidean n × Euclidean n) in 𝓝 z,
        q.1 ∉ G.X₀ ∨ q.2.1 ∉ G.X₀ := by
      rcases not_and_or.mp hxy with hx | hy
      · filter_upwards [continuousAt_fst (G.compact_X₀.isClosed.isOpen_compl.mem_nhds hx)] with q hq
        exact Or.inl hq
      · filter_upwards [continuousAt_snd.fst (G.compact_X₀.isClosed.isOpen_compl.mem_nhds hy)] with q hq
        exact Or.inr hq
    filter_upwards [hN] with q hq
    rw [F.extendedInverseAmplitude_eq_maskFree hε]
    exact F.maskFreeInverseAmplitude_eq_zero_of_not_mem_physical hε hq q.2.2

/-- Joint within-domain smoothness of the globally supported amplitude on
the closed admissible interval (`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem UniformNormalData.extendedInverseAmplitude_contDiffOn
    (F : UniformNormalData G C) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) ↦
      F.extendedInverseAmplitude q.1 q.2) (Icc 0 G.ε₀ ×ˢ univ) := by
  intro p hp
  obtain ⟨b, hb, he, hev⟩ := F.extendedInverseAmplitude_exists_contDiffAt_extension hp.1 p.2
  apply hb.contDiffWithinAt.congr_of_eventuallyEq _ he.symm
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hqs
  exact (hq hqs.1).symm

end JanetCartan.NormalComparison
