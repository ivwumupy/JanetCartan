module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.Differential
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Epsilon derivatives on the fixed inverse domains

For `app:ch_seed:prop:seed-phase-charts`, epsilon is the first coordinate of
`(ℝ × P) × E`. `P` retains all physical and spectator coordinates and `E`
retains the output data covector. Differentiating in epsilon costs exactly one
joint derivative, including at zero in the open extension of the fixed boxes.
This order shift is independent of the requested differentiating order.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff

namespace JanetCartan.FullPhaseCharts.InverseEstimates

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Epsilon differentiation is evaluation of the actual joint differential,
with the normalized output data held fixed (`app:ch_seed:prop:seed-phase-charts`). -/
theorem deriv_epsilon_eq_fderiv {g : (ℝ × P) × E → E} {q : (ℝ × P) × E}
    (hg : DifferentiableAt ℝ g q) :
    deriv (fun ε ↦ g ((ε, q.1.2), q.2)) q.1.1 = fderiv ℝ g q ((1, 0), 0) := by
  exact (hg.hasFDerivAt.comp_hasDerivAt q.1.1
    (((hasDerivAt_id q.1.1).prodMk (hasDerivAt_const q.1.1 q.1.2)).prodMk
      (hasDerivAt_const q.1.1 q.2))).deriv

/-- The exact identity `∂ε inv = -(Dᵤ Ψ)⁻¹ ∂ε Ψ`, derived from the
fixed inverse equation of `app:ch_seed:prop:seed-phase-charts`. Both epsilon
derivatives here are actual one-variable derivatives, also at epsilon zero. -/
theorem deriv_epsilon_inverse_eq
    {f g : (ℝ × P) × E → E} {U W : Set ((ℝ × P) × E)}
    (hU : IsOpen U) (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ f W) (hg : ContDiffOn ℝ ∞ g U)
    (hmap : MapsTo (inverseGraph g) U W)
    (heq : ∀ q ∈ U, f (inverseGraph g q) = q.2)
    {q : (ℝ × P) × E} (hq : q ∈ U)
    (hinv : (fderiv ℝ (fun u ↦ f (q.1, u)) (g q)).IsInvertible) :
    deriv (fun ε ↦ g ((ε, q.1.2), q.2)) q.1.1 =
      -(fderiv ℝ (fun u ↦ f (q.1, u)) (g q)).inverse
        (deriv (fun ε ↦ f ((ε, q.1.2), g q)) q.1.1) := by
  rw [deriv_epsilon_eq_fderiv
    ((hg.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))]
  rw [fderiv_inverse_parameter_eq hU hW hf hg hmap heq hq hinv]
  have hd := deriv_epsilon_eq_fderiv (q := inverseGraph g q)
    ((hf.contDiffAt (hW.mem_nhds (hmap hq))).differentiableAt (by simp))
  dsimp only [inverseGraph] at hd
  rw [hd]
  rfl

/-- The first epsilon derivative bound from the fixed normalized input gap
in `app:ch_seed:prop:seed-phase-charts`. The constant is independent of epsilon,
the phase, and all high norms; no inverse derivative bound is an input. -/
theorem norm_deriv_epsilon_inverse_le [FiniteDimensional ℝ E]
    (G : E ≃L[ℝ] E)
    {f g : (ℝ × P) × E → E} {U W : Set ((ℝ × P) × E)}
    (hU : IsOpen U) (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ f W) (hg : ContDiffOn ℝ ∞ g U)
    (hmap : MapsTo (inverseGraph g) U W)
    (heq : ∀ q ∈ U, f (inverseGraph g q) = q.2)
    {q : (ℝ × P) × E} (hq : q ∈ U)
    (hgap : ‖(G.symm : E →L[ℝ] E) ∘L
      fderiv ℝ (fun u ↦ f (q.1, u)) (g q) - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) :
    ‖deriv (fun ε ↦ g ((ε, q.1.2), q.2)) q.1.1‖ ≤
      (2 * ‖(G.symm : E →L[ℝ] E)‖) * ‖fderiv ℝ f (inverseGraph g q)‖ := by
  rw [deriv_epsilon_eq_fderiv
    ((hg.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))]
  simpa using norm_fderiv_inverse_parameter_le G hU hW hf hg hmap heq hq hgap (1, 0)

/-- Joint smoothness of the first epsilon derivative on the same fixed open
inverse domain (`app:ch_seed:prop:seed-phase-charts`). -/
theorem contDiffOn_deriv_epsilon {g : (ℝ × P) × E → E} {U : Set ((ℝ × P) × E)}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (fun q : (ℝ × P) × E ↦
      deriv (fun ε ↦ g ((ε, q.1.2), q.2)) q.1.1) U := by
  apply ((hg.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply
    (contDiffOn_const (c := (((1 : ℝ), (0 : P)), (0 : E))))).congr
  intro q hq
  exact deriv_epsilon_eq_fderiv ((hg.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))

/-- Exactly one joint derivative controls the first epsilon derivative at
every order (`app:ch_seed:prop:seed-phase-charts`). This is a differential
inequality, not an assumed inverse-jet bound. -/
theorem norm_iteratedFDeriv_deriv_epsilon_le
    {g : (ℝ × P) × E → E} {U : Set ((ℝ × P) × E)}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    {q : (ℝ × P) × E} (hq : q ∈ U) (r : ℕ) :
    ‖iteratedFDeriv ℝ r (fun q : (ℝ × P) × E ↦
      deriv (fun ε ↦ g ((ε, q.1.2), q.2)) q.1.1) q‖ ≤
      ‖iteratedFDeriv ℝ (r + 1) g q‖ := by
  let v : (ℝ × P) × E := ((1, 0), 0)
  let R : (((ℝ × P) × E) →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E v
  have hR : ‖R‖ ≤ 1 := by
    apply R.opNorm_le_bound zero_le_one
    intro A
    simpa [R, v] using A.le_opNorm v
  have heq : EqOn (fun q : (ℝ × P) × E ↦
      deriv (fun ε ↦ g ((ε, q.1.2), q.2)) q.1.1) (R ∘ fderiv ℝ g) U := by
    intro z hz
    exact deriv_epsilon_eq_fderiv ((hg.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
  have hj := iteratedFDerivWithin_congr (𝕜 := ℝ) heq hq r
  rw [iteratedFDerivWithin_of_isOpen _ hU hq,
    iteratedFDerivWithin_of_isOpen _ hU hq] at hj
  rw [hj]
  have hd := (hg.fderiv_of_isOpen hU (m := ∞) (by simp)).contDiffAt (hU.mem_nhds hq)
  calc
    _ ≤ ‖R‖ * ‖iteratedFDeriv ℝ r (fderiv ℝ g) q‖ :=
      R.norm_iteratedFDeriv_comp_left hd (by simp)
    _ ≤ 1 * ‖iteratedFDeriv ℝ r (fderiv ℝ g) q‖ :=
      mul_le_mul_of_nonneg_right hR (norm_nonneg _)
    _ = _ := by rw [one_mul, norm_iteratedFDeriv_fderiv]

/-- The `C^r` seminorm of the actual epsilon derivative is bounded by the
joint `C^(r+1)` seminorm, with constant one and the same compact set. This
retains every data, physical and spectator derivative in
`app:ch_seed:prop:seed-phase-charts`. It does not assert the inverse one-high
bound, which must be proved from forward phase jets separately. -/
theorem cNorm_deriv_epsilon_le
    {g : (ℝ × P) × E → E} {U K : Set ((ℝ × P) × E)}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hK : IsCompact K) (hKU : K ⊆ U) (r : ℕ) :
    cNorm K r (fun q : (ℝ × P) × E ↦
      deriv (fun ε ↦ g ((ε, q.1.2), q.2)) q.1.1) ≤ cNorm K (r + 1) g := by
  let B : ℕ → ℝ := fun j ↦ sSup ((fun q ↦ ‖iteratedFDeriv ℝ j g q‖) '' K)
  have hB (j : ℕ) : 0 ≤ B j := sSup_norm_iteratedFDeriv_nonneg K j g
  have hb (j : ℕ) : BddAbove ((fun q ↦ ‖iteratedFDeriv ℝ j g q‖) '' K) :=
    bddAbove_norm_iteratedFDeriv_of_contDiffAt hK
      (fun q hq ↦ (hg.contDiffAt (hU.mem_nhds (hKU hq))).of_le (by simp)) le_rfl
  apply (cNorm_le_sum_of_bounds (C := fun j ↦ B (j + 1))
    (fun j _ ↦ hB (j + 1)) ?_).trans
  · change (∑ j ∈ Finset.range (r + 1), B (j + 1)) ≤ ∑ j ∈ Finset.range (r + 1 + 1), B j
    rw [Finset.sum_range_succ' B (r + 1)]
    exact le_add_of_nonneg_right (hB 0)
  · intro j _ q hq
    exact (norm_iteratedFDeriv_deriv_epsilon_le hU hg (hKU hq) j).trans
      (le_csSup (hb (j + 1)) (mem_image_of_mem _ hq))

end JanetCartan.FullPhaseCharts.InverseEstimates
