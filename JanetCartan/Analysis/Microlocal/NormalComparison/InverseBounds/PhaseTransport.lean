module
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.Coefficients
public import JanetCartan.Analysis.ODE.PositiveTransport.ParametricIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus
/-!
# Joint gradient regularity and exact phase transport

The exact identities in Step 2 of `app:ch_osc:prop:osc-normal` in `paper.tex`.
Smoothness of the averaged gradient is derived by differentiation under the
compact segment integral. The parameter and both physical positions remain
independent. No quantitative derivative bound is asserted in this module.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.NormalComparison
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}
/-- Joint smoothness of the actual averaged gradient, on the full open
parameter extension including both endpoints (`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.averagedGradient_contDiffOn (F : UniformNormalData G C) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) ↦
      averagedGradient (F.phase q.1) q.2.1 q.2.2.1 q.2.2.2)
      (F.parameterDomain ×ˢ (G.X ×ˢ (G.X ×ˢ G.D))) := by
  let P := ℝ × (Euclidean n × (Euclidean n × Euclidean n))
  let U : Set P := F.parameterDomain ×ˢ (G.X ×ˢ (G.X ×ˢ G.D))
  have hU : IsOpen U := F.isOpen_parameterDomain.prod
    (G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D))
  let H : ℝ × P → Euclidean n →L[ℝ] ℝ := fun z ↦
    fderiv ℝ (fun x ↦ F.phase z.2.1 x z.2.2.2.2)
      (z.2.2.2.1 + z.1 • (z.2.2.1 - z.2.2.2.1))
  have hH : ∀ z ∈ uIcc (0 : ℝ) 1 ×ˢ U, ContDiffAt ℝ ∞ H z := by
    intro z hz
    have ht : z.1 ∈ Icc (0 : ℝ) 1 := by simpa using hz.1
    have hp := F.phase_contDiffAt hz.2.1
      (G.convex_X.add_smul_sub_mem hz.2.2.2.1 hz.2.2.1 ht) hz.2.2.2.2
    have haux : ContDiffAt ℝ ∞
        (fun w : (ℝ × P) × Euclidean n ↦ F.phase w.1.2.1 w.2 w.1.2.2.2.2)
        (z, z.2.2.2.1 + z.1 • (z.2.2.1 - z.2.2.2.1)) :=
      ContDiffAt.comp (g := fun q : ℝ × (Euclidean n × Euclidean n) ↦
        F.phase q.1 q.2.1 q.2.2)
        (f := fun w : (ℝ × P) × Euclidean n ↦ (w.1.2.1, (w.2, w.1.2.2.2.2)))
        (z, z.2.2.2.1 + z.1 • (z.2.2.1 - z.2.2.2.1)) hp (contDiffAt_fst.snd.fst.prodMk
        (contDiffAt_snd.prodMk contDiffAt_fst.snd.snd.snd.snd))
    exact haux.fderiv
      (contDiffAt_snd.snd.snd.fst.add (contDiffAt_fst.smul
        (contDiffAt_snd.snd.fst.sub contDiffAt_snd.snd.snd.fst))) (by simp)
  have hi := contDiffOn_fixedIntervalIntegral hU hH
  exact (InnerProductSpace.toDual ℝ (Euclidean n)).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn hi

/-- The exact transport identity from Step 2 of
`app:ch_osc:prop:osc-normal`. The velocity is the actual inverse input
Jacobian applied to the actual parameter derivative of the averaged gradient. -/
theorem UniformNormalData.phase_transport_identity (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) {x y u : Euclidean n}
    (hx : x ∈ G.X) (hy : y ∈ G.X) (hu : u ∈ G.D) :
    deriv (fun t ↦ F.phase t x u - F.phase t y u) ε =
      fderiv ℝ (fun v ↦ F.phase ε x v - F.phase ε y v) u
        (F.transportVelocity ε x y u) := by
  have hε' := F.parameter_subset hε
  have hq := F.averagedGradient_contDiffOn.contDiffAt (x := (ε, (x, (y, u))))
    ((F.isOpen_parameterDomain.prod (G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D))).mem_nhds
      ⟨hε', hx, hy, hu⟩)
  have he : DifferentiableAt ℝ (fun t ↦ averagedGradient (F.phase t) x y u) ε :=
    (hq.comp (f := fun t : ℝ ↦ (t, (x, (y, u)))) ε
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hd : DifferentiableAt ℝ (averagedGradient (F.phase ε) x y) u :=
    (hq.comp (f := fun v : Euclidean n ↦ (ε, (x, (y, v)))) u
      (contDiffAt_const.prodMk (contDiffAt_const.prodMk
        (contDiffAt_const.prodMk contDiffAt_id)))).differentiableAt (by simp)
  let L := (InnerProductSpace.toDual ℝ (Euclidean n)) (x - y)
  have heqε : (fun t ↦ F.phase t x u - F.phase t y u) =ᶠ[𝓝 ε]
      (fun t ↦ L (averagedGradient (F.phase t) x y u)) := by
    filter_upwards [F.isOpen_parameterDomain.mem_nhds hε'] with t ht
    exact F.phase_sub_eq_inner ht hx hy hu
  have hequ : (fun v ↦ F.phase ε x v - F.phase ε y v) =ᶠ[𝓝 u]
      (fun v ↦ L (averagedGradient (F.phase ε) x y v)) := by
    filter_upwards [G.isOpen_D.mem_nhds hu] with v hv
    exact F.phase_sub_eq_inner hε' hx hy hv
  have heDer : deriv (fun t ↦ F.phase t x u - F.phase t y u) ε =
      L (deriv (fun t ↦ averagedGradient (F.phase t) x y u) ε) :=
    heqε.deriv_eq.trans (L.hasFDerivAt.comp_hasDerivAt ε he.hasDerivAt).deriv
  have huDer : fderiv ℝ (fun v ↦ F.phase ε x v - F.phase ε y v) u =
      L.comp (fderiv ℝ (averagedGradient (F.phase ε) x y) u) :=
    hequ.fderiv_eq.trans (L.hasFDerivAt.comp u hd.hasFDerivAt).fderiv
  rw [heDer, huDer, ContinuousLinearMap.comp_apply,
    F.jacobian_transportVelocity hε hx hy hu]
end JanetCartan.NormalComparison
