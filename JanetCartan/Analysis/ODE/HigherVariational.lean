module

public import JanetCartan.Analysis.ODE.HigherVariational.Partitions
public import JanetCartan.Analysis.ODE.HigherVariational.Interchange
public import JanetCartan.Analysis.ODE.DerivativeBounds

/-!
# Higher spatial-jet variational equations

The higher variational equations used in
`app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase` of `paper.tex`. Joint smoothness and the original
ODE imply time differentiation of every spatial jet. The Faà di Bruno formula
then isolates the linearized vector field applied to the actual top jet, leaving
an explicit partition sum involving only strictly lower spatial jets.

`hasJetEvolutionOn_of_ode` supplies the equations and endpoint continuity needed
by the Gronwall estimates in `DerivativeBounds`, on closed inner time intervals
with explicit outer buffers. It includes order zero, arbitrary parameter spaces
and arbitrary initial sections. The lower-jet partition formula and its norm
bound are provided by `HigherVariational.Partitions`; the quantitative induction
is the responsibility of `HamiltonPhase.FlowJetBounds`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ODE

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`: the actual spatial jets of a jointly smooth ODE
solution satisfy the coefficient-plus-forcing equation at every order, including
zero. This is the pointwise input to `hasJetEvolutionOn_of_ode`. The coefficient
is `DV(Φ)` at positive orders and zero at order zero; the forcing is the explicit
lower-jet partition sum at positive orders and the original vector field at zero.
-/
theorem hasDerivAt_iteratedFDeriv_jetEvolution
    {U : Set P} (hU : IsOpen U) {c d : ℝ} {Φ : P × ℝ → E}
    (hΦ : ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo c d)) {V : E → E}
    (hode : ∀ x ∈ U, ∀ t ∈ Ioo c d,
      HasDerivAt (fun τ ↦ Φ (x, τ)) (V (Φ (x, t))) t)
    (j : ℕ) {x : P} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo c d)
    (hV : ContDiffAt ℝ j V (Φ (x, t))) :
    HasDerivAt (fun τ ↦ iteratedFDeriv ℝ j (fun y ↦ Φ (y, τ)) x)
      ((jetEvolutionCoefficient j V (Φ (x, t))).compContinuousMultilinearMap
        (iteratedFDeriv ℝ j (fun y ↦ Φ (y, t)) x) +
          jetEvolutionForcing j V (fun y ↦ Φ (y, t)) x) t := by
  have hf : ContDiffAt ℝ j (fun y ↦ Φ (y, t)) x :=
    ((hΦ.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds ⟨hx, ht⟩)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp)
  exact (hasDerivAt_iteratedFDeriv_of_ode hU hΦ hode j hx ht).congr_deriv
    (iteratedFDeriv_comp_eq_jetEvolution hV hf)

/-- `app:ch_regular_base:lem:buffered-interpolation`: at positive order the top
variational term is `DV(Φ) DʲΦ`. Every inner flow derivative in the remaining
explicit partition sum has order strictly below `j`, by
`partSize_lt_of_two_le_length`, and `norm_jetPartitionRemainder_le` bounds its norm.
These are the algebraic inputs for the induction in `HamiltonPhase.FlowJetBounds`.
-/
theorem hasDerivAt_iteratedFDeriv_top_add_jetPartitionRemainder
    {U : Set P} (hU : IsOpen U) {c d : ℝ} {Φ : P × ℝ → E}
    (hΦ : ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo c d)) {V : E → E}
    (hode : ∀ x ∈ U, ∀ t ∈ Ioo c d,
      HasDerivAt (fun τ ↦ Φ (x, τ)) (V (Φ (x, t))) t)
    {j : ℕ} (hj : 0 < j) {x : P} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo c d)
    (hV : ContDiffAt ℝ j V (Φ (x, t))) :
    HasDerivAt (fun τ ↦ iteratedFDeriv ℝ j (fun y ↦ Φ (y, τ)) x)
      ((fderiv ℝ V (Φ (x, t))).compContinuousMultilinearMap
        (iteratedFDeriv ℝ j (fun y ↦ Φ (y, t)) x) +
          jetPartitionRemainder j V (fun y ↦ Φ (y, t)) x) t := by
  simpa only [jetEvolutionCoefficient, jetEvolutionForcing, hj.ne', ite_false] using
    hasDerivAt_iteratedFDeriv_jetEvolution hU hΦ hode j hx ht hV

/-- `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`: a genuine jointly smooth ODE solution supplies
`HasJetEvolutionOn` on every closed inner interval `Icc a b` with strict buffers
`c < a` and `b < d`. Any working parameter set contained in the open domain is
allowed, and no condition on the initial section is needed.

Both fields of `HasJetEvolutionOn` are derived from smoothness and the original
ODE, including continuity at both endpoints and the order-zero equation. This
discharges the variational-equation premise of
`HasJetEvolutionOn.norm_iteratedFDeriv_le_oneHigh`; quantitative coefficient and
forcing bounds remain separate inputs to that estimate. -/
theorem hasJetEvolutionOn_of_ode
    {U : Set P} (hU : IsOpen U) {Ω : Set E} (hΩ : IsOpen Ω)
    {c a b d : ℝ} (hca : c < a) (hbd : b < d)
    {Φ : P × ℝ → E} (hΦ : ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo c d))
    {V : E → E} (hV : ContDiffOn ℝ ∞ V Ω)
    (hrange : MapsTo Φ (U ×ˢ Ioo c d) Ω)
    (hode : ∀ x ∈ U, ∀ t ∈ Ioo c d,
      HasDerivAt (fun τ ↦ Φ (x, τ)) (V (Φ (x, t))) t)
    {s : Set P} (hs : s ⊆ U) (n : ℕ) :
    HasJetEvolutionOn (fun t x ↦ Φ (x, t)) s n a b
      (fun j t x ↦ jetEvolutionCoefficient j V (Φ (x, t)))
      (fun j t x ↦ jetEvolutionForcing j V (fun y ↦ Φ (y, t)) x) := by
  have htime : Icc a b ⊆ Ioo c d := fun _ ht ↦
    ⟨hca.trans_le ht.1, ht.2.trans_lt hbd⟩
  constructor
  · intro j _ x hx t ht
    exact (hasDerivAt_iteratedFDeriv_of_ode hU hΦ hode j (hs hx)
      (htime ht)).continuousAt.continuousWithinAt
  · intro j _ x hx t ht
    have ht' := htime (Ico_subset_Icc_self ht)
    exact (hasDerivAt_iteratedFDeriv_jetEvolution hU hΦ hode j (hs hx) ht'
      ((hV.contDiffAt (hΩ.mem_nhds (hrange ⟨hs hx, ht'⟩))).of_le
        (by simp))).hasDerivWithinAt

end JanetCartan.ODE
