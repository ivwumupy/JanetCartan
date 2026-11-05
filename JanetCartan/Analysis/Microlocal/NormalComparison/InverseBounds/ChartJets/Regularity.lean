module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.PhaseTransport
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Regularity of the actual normal inverse chart

Local smooth extensions for `app:ch_osc:setup:osc-normal` and Step 1 of
`app:ch_osc:prop:osc-normal`. The chosen inverse is identified with a smooth
implicit function only on the admissible parameter interval.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.NormalComparison
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- Smooth local extensions of the actual inverse chart, including at both
parameter endpoints (`app:ch_osc:setup:osc-normal`). Equality with the chosen
inverse is asserted only for admissible parameters and physical positions. -/
theorem UniformNormalData.inverseChart_exists_contDiffAt_extension
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {x y v : Euclidean n} (hx : x ∈ G.X) (hy : y ∈ G.X) (hv : v ∈ G.V) :
    ∃ g : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) → Euclidean n,
      ContDiffAt ℝ ∞ g (ε, (x, (y, v))) ∧
      g (ε, (x, (y, v))) = F.inverseChart ε x y v ∧
      ∀ᶠ q in 𝓝 (ε, (x, (y, v))),
        q.1 ∈ Icc 0 G.ε₀ → q.2.1 ∈ G.X → q.2.2.1 ∈ G.X →
          g q = F.inverseChart q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  let P := ℝ × (Euclidean n × (Euclidean n × Euclidean n))
  let p : P := (ε, (x, (y, v)))
  let u := F.inverseChart ε x y v
  let H : P × Euclidean n → Euclidean n := fun z ↦
    averagedGradient (F.phase z.1.1) z.1.2.1 z.1.2.2.1 z.2 - z.1.2.2.2
  have hu : u ∈ G.D := F.inverseChart_mem hε hx hy hv
  have he : averagedGradient (F.phase ε) x y u = v :=
    F.averagedGradient_inverseChart hε hx hy hv
  have hforward := F.averagedGradient_contDiffOn.contDiffAt (x := (ε, (x, (y, u))))
    ((F.isOpen_parameterDomain.prod (G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D))).mem_nhds
      ⟨F.parameter_subset hε, hx, hy, hu⟩)
  have hH : ContDiffAt ℝ ∞ H (p, u) := by
    apply (hforward.comp (p, u)
      (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.fst.prodMk
        (contDiffAt_fst.snd.snd.fst.prodMk contDiffAt_snd)))).sub
      contDiffAt_fst.snd.snd.snd
  have hj : fderiv ℝ H (p, u) ∘L ContinuousLinearMap.inr ℝ P (Euclidean n) =
      fderiv ℝ (averagedGradient (F.phase ε) x y) u := by
    have hd := ((hH.differentiableAt (by simp)).hasFDerivAt.comp u
      (hasFDerivAt_prodMk_right p u)).fderiv
    simpa [H, p, Function.comp_def, fderiv_sub_const] using hd.symm
  have hi : (fderiv ℝ H (p, u) ∘L ContinuousLinearMap.inr ℝ P (Euclidean n)).IsInvertible := by
    rw [hj]
    exact F.jacobian_isInvertible hε hx hy hu
  let g := hH.implicitFunction (by simp) hi
  have hg : ContDiffAt ℝ ∞ g p := hH.contDiffAt_implicitFunction (by simp) hi
  have hgu : g p = u := hH.implicitFunction_apply_self (by simp) hi
  refine ⟨g, hg, hgu, ?_⟩
  have hmem : ∀ᶠ q in 𝓝 p, g q ∈ G.D :=
    hg.continuousAt (G.isOpen_D.mem_nhds (hgu.symm ▸ hu))
  filter_upwards [hmem, hH.eventually_apply_implicitFunction (by simp) hi] with q hq hEq
  intro hqε hqx hqy
  have hgrad : averagedGradient (F.phase q.1) q.2.1 q.2.2.1 (g q) = q.2.2.2 := by
    have hz : H (p, u) = 0 := sub_eq_zero.mpr he
    exact sub_eq_zero.mp (hEq.trans hz)
  rw [← hgrad]
  exact (F.inverseChart_averagedGradient hqε hqx hqy hq).symm

/-- Joint smoothness on the closed admissible parameter interval, in the
within-domain sense (`app:ch_osc:prop:osc-normal`). The stronger extension
statement above records actual ambient smoothness at the endpoints. -/
theorem UniformNormalData.inverseChart_contDiffOn (F : UniformNormalData G C) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) ↦
      F.inverseChart q.1 q.2.1 q.2.2.1 q.2.2.2)
      (Icc 0 G.ε₀ ×ˢ (G.X ×ˢ (G.X ×ˢ G.V))) := by
  intro p hp
  obtain ⟨g, hg, he, hevent⟩ :=
    F.inverseChart_exists_contDiffAt_extension hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  apply hg.contDiffWithinAt.congr_of_eventuallyEq _ he.symm
  filter_upwards [hevent.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hqs
  exact (hq hqs.1 hqs.2.1 hqs.2.2.1).symm

/-- At each admissible parameter, all spatial inverse derivatives exist on
the open chart (`app:ch_osc:prop:osc-normal`). -/
theorem UniformNormalData.inverseChart_spatial_contDiffOn (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) :
    ContDiffOn ℝ ∞ (fun z : Euclidean n × (Euclidean n × Euclidean n) ↦
      F.inverseChart ε z.1 z.2.1 z.2.2) (G.X ×ˢ (G.X ×ˢ G.V)) :=
  F.inverseChart_contDiffOn.comp (contDiffOn_const.prodMk contDiffOn_id)
    (fun _ hz ↦ ⟨hε, hz⟩)

/-- The bounded input box controls the zeroth inverse jet uniformly before
choosing a phase family (`app:ch_osc:prop:osc-normal`). -/
theorem UniformNormalGeometry.exists_inverseChart_norm_bound
    (G : UniformNormalGeometry n r) :
    ∃ A > 0, ∀ {C : ℕ → ℝ} (F : UniformNormalData G C),
      ∀ ε ∈ Icc 0 G.ε₀, ∀ x ∈ G.X, ∀ y ∈ G.X, ∀ v ∈ G.V,
        ‖F.inverseChart ε x y v‖ ≤ A := by
  obtain ⟨A, hA, hbound⟩ := G.bounded_D.exists_pos_norm_le
  exact ⟨A, hA, fun F _ hε _ hx _ hy _ hv ↦
    hbound _ (F.inverseChart_mem hε hx hy hv)⟩

end JanetCartan.NormalComparison
