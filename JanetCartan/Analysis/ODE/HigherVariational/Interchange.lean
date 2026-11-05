module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.ParameterJets.Interchange

/-!
# Time differentiation of spatial jets of a smooth ODE solution

The differential interchange needed by `HasJetEvolutionOn` for
`app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase` in `paper.tex`. Joint smoothness and the original
ODE imply the time evolution of every spatial iterated Fréchet derivative,
including order zero. The parameter space and the initial section are arbitrary.

We reuse the general mixed-derivative lemmas from `NormalComparison`; their
proofs apply to arbitrary real normed spaces. No regularity of the vector field
away from the given solution is required for this interchange.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ODE

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`: time differentiation commutes with every spatial
jet of a jointly smooth solution of the original ODE. This supplies the temporal
derivative for the buffered `HasJetEvolutionOn` assembly, before decomposing the
right-hand side into its top variational term and lower-jet forcing.

The order `j` may be zero. Neither completeness of the normed spaces, smoothness
of `V`, nor a prescribed initial section is assumed. -/
theorem hasDerivAt_iteratedFDeriv_of_ode
    {U : Set P} (hU : IsOpen U) {c d : ℝ} {Φ : P × ℝ → E}
    (hΦ : ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo c d)) {V : E → E}
    (hode : ∀ x ∈ U, ∀ t ∈ Ioo c d,
      HasDerivAt (fun τ ↦ Φ (x, τ)) (V (Φ (x, t))) t)
    (j : ℕ) {x : P} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo c d) :
    HasDerivAt (fun τ ↦ iteratedFDeriv ℝ j (fun y ↦ Φ (y, τ)) x)
      (iteratedFDeriv ℝ j (fun y ↦ V (Φ (y, t))) x) t := by
  have hswap : ContDiffOn ℝ ∞ (fun q : ℝ × P ↦ Φ (q.2, q.1)) (Ioo c d ×ˢ U) :=
    hΦ.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hq ↦ ⟨hq.2, hq.1⟩)
  have hlocal : ContDiffAt ℝ ∞ (fun q : ℝ × P ↦ Φ (q.2, q.1)) (t, x) :=
    hswap.contDiffAt ((isOpen_Ioo.prod hU).mem_nhds ⟨ht, hx⟩)
  have hjet := NormalComparison.contDiffAt_spatial_iteratedFDeriv hlocal j
  have hd : DifferentiableAt ℝ
      (fun τ ↦ iteratedFDeriv ℝ j (fun y ↦ Φ (y, τ)) x) t :=
    (hjet.comp t (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have heq : (fun y ↦ deriv (fun τ ↦ Φ (y, τ)) t) =ᶠ[𝓝 x]
      (fun y ↦ V (Φ (y, t))) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hode y hy t ht).deriv
  have hi := NormalComparison.iteratedFDeriv_deriv_parameter
    isOpen_Ioo hU hswap ht hx j
  rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds] at hi
  rw [hi]
  exact hd.hasDerivAt

end JanetCartan.ODE
