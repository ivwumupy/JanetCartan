module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.TwoTimePhase
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Radial homogeneity from the actual phase differential

The explicit footpoint phase and its proved differential give an Euler
identity. Integrating its radial quotient proves the joint local homogeneity
needed by the supported integer graph calculus. This does not assert a global
conic extension of the local inverse chart.
Source: `app:ch_regular_base:lem:characteristic-kernel` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace JanetCartan.RegularSector.Characteristic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem hasDerivAt_phase_radial_quotient {h : RootState E → ℝ} {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (q : TwoTimePoint E) {a : ℝ} (ha : a ≠ 0)
    (hd : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (q.1, (q.2.1, (q.2.2.1, a • q.2.2.2))))
      (q.1, (q.2.1, (q.2.2.1, a • q.2.2.2)))) :
    HasDerivAt (fun b : ℝ ↦ twoTimePhase C (q.1, (q.2.1, (q.2.2.1, b • q.2.2.2))) / b) 0 a := by
  have hx : HasDerivAt (fun b : ℝ ↦ (q.1, (q.2.1, (q.2.2.1, b • q.2.2.2))))
      (0, (0, (0, q.2.2.2))) a := by
    simpa only [one_smul, id_eq] using
      (hasDerivAt_const a q.1).prodMk ((hasDerivAt_const a q.2.1).prodMk
      ((hasDerivAt_const a q.2.2.1).prodMk ((hasDerivAt_id a).smul_const q.2.2.2)))
  have he := (hd.comp_hasDerivAt a hx).div (hasDerivAt_id a) ha
  convert! he using 1
  simp [twoTimePhaseDifferential, twoTimePhase, inner_smul_right, mul_comm]

/-- The full differential of the constructed phase proves degree-one radial
homogeneity on a joint neighborhood. This follows by differentiating Ψ(aη)/a:
its covector derivative is the same footpoint used to define Ψ. No separate
flow-scaling or phase-homogeneity premise is required. The actual producer is
`exists_physical_pencil_kernel` and its retained `hdiff` conclusion.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem twoTimePhase_radial_germ {h : RootState E → ℝ} {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (hphase : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    {q : TwoTimePoint E} (hq : q ∈ C.target) :
    ∀ᶠ a : ℝ in 𝓝 1,
      (fun w : TwoTimePoint E ↦ twoTimePhase C (w.1, (w.2.1, (w.2.2.1, a • w.2.2.2))))
        =ᶠ[𝓝 q] (fun w ↦ a * twoTimePhase C w) := by
  let R : ℝ × TwoTimePoint E → TwoTimePoint E :=
    fun p ↦ (p.2.1, (p.2.2.1, (p.2.2.2.1, p.1 • p.2.2.2.2)))
  have hR : Continuous R := by fun_prop
  have hopen : IsOpen ({p : ℝ × TwoTimePoint E | 0 < p.1} ∩ R ⁻¹' C.target) :=
    (isOpen_lt continuous_const continuous_fst).inter (C.open_target.preimage hR)
  have hbase : ((1 : ℝ), q) ∈ {p : ℝ × TwoTimePoint E | 0 < p.1} ∩ R ⁻¹' C.target :=
    ⟨by norm_num, by simpa [R] using hq⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen (1, q) hbase
  filter_upwards [Metric.ball_mem_nhds (1 : ℝ) hδ] with a ha
  filter_upwards [Metric.ball_mem_nhds q hδ] with w hw
  have hall (b : ℝ) (hb : b ∈ ball 1 δ) : 0 < b ∧ R (b, w) ∈ C.target :=
    hball (a := (b, w)) (by simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using And.intro hb hw)
  have hd (b : ℝ) (hb : b ∈ ball 1 δ) :
      HasDerivAt (fun c : ℝ ↦ twoTimePhase C (w.1, (w.2.1, (w.2.2.1, c • w.2.2.2))) / c) 0 b := by
    exact hasDerivAt_phase_radial_quotient w (hall b hb).1.ne' (hphase _ (hall b hb).2)
  have hid := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (1 : ℝ) δ).isPreconnected
    (fun b hb ↦ (hd b hb).differentiableAt.differentiableWithinAt)
    (fun b hb ↦ (hd b hb).deriv) ha (mem_ball_self hδ)
  simp only [one_smul, div_one, Prod.mk.eta] at hid
  exact (div_eq_iff (hall a ha).1.ne').mp hid |>.trans (mul_comm _ _)

end JanetCartan.RegularSector.Characteristic
