module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.LatticeRemainder.Series.Bounds

/-!
# Convergence and differentiation of the Bessel lattice remainder

The two analytic inputs below are precisely smoothness of the heat kernel
integral off zero and rapid decay of its jets away from zero. From these we
prove actual convergence, differentiation at every finite order, and smoothness
on the open comparison cube of `app:ch_background:prop:bg-frame`, Step 1.
Instantiating the two kernel inputs is the responsibility of the heat-integral
construction; no convergence or remainder regularity is assumed here.
-/

@[expose] public noncomputable section
open scoped ContDiff Topology
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem exists_comparison_ball {p : E × E}
    (hp : p ∈ imageBesselComparisonDomain d) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 / 2 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ q ∈ Metric.ball p ε, (∀ i, |q.1 i| ≤ r) ∧ ∀ i, |q.2 i| ≤ r := by
  have h1 : ‖WithLp.ofLp p.1‖ < (1 / 2 : ℝ) :=
    (pi_norm_lt_iff (by norm_num)).mpr (by simpa only [Real.norm_eq_abs] using hp.1)
  have h2 : ‖WithLp.ofLp p.2‖ < (1 / 2 : ℝ) :=
    (pi_norm_lt_iff (by norm_num)).mpr (by simpa only [Real.norm_eq_abs] using hp.2)
  obtain ⟨r, hpr, hr⟩ := exists_between (max_lt h1 h2)
  have hr₀ : 0 ≤ r := (norm_nonneg _).trans ((le_max_left _ _).trans hpr.le)
  have hc : Continuous (fun q : E × E ↦ max ‖WithLp.ofLp q.1‖ ‖WithLp.ofLp q.2‖) := by
    fun_prop
  have hu : {q : E × E | max ‖WithLp.ofLp q.1‖ ‖WithLp.ofLp q.2‖ < r} ∈ 𝓝 p :=
    (isOpen_lt hc continuous_const).mem_nhds hpr
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨r, hr₀, hr, ε, hε, fun q hq ↦ ⟨fun i ↦ ?_, fun i ↦ ?_⟩⟩
  · exact (norm_le_pi_norm (WithLp.ofLp q.1) i).trans
      ((le_max_left _ _).trans (hb hq).le)
  · exact (norm_le_pi_norm (WithLp.ofLp q.2) i).trans
      ((le_max_right _ _).trans (hb hq).le)

variable
    (hK : ContDiffOn ℝ ∞ (imageBesselKernel (d := d)) {x | x ≠ 0})
    (hdecay : ∀ δ : ℝ, 0 < δ → ∀ n m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : EuclideanSpace ℝ (Fin d), δ ≤ ‖x‖ →
        (1 + ‖x‖)^m * ‖iteratedFDeriv ℝ n imageBesselKernel x‖ ≤ C)
include hK hdecay

/-- Absolute convergence in multilinear operator norm of every derivative
series, from the off-diagonal estimates (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem summable_norm_iteratedFDeriv_imageBesselLatticeTerm_of_offDiagonalBounds
    (n : ℕ) {p : E × E} (hp : p ∈ imageBesselComparisonDomain d) :
    Summable (fun k : Fin d → ℤ ↦ ‖iteratedFDeriv ℝ n (imageBesselLatticeTerm k) p‖) := by
  obtain ⟨r, hr₀, hr, ε, hε, hb⟩ := exists_comparison_ball hp
  obtain ⟨u, hu, _, hbound⟩ :=
    exists_summable_imageBesselLatticeTerm_jet_majorant hK hdecay hr₀ hr n
  have hc := hb p (Metric.mem_ball_self hε)
  exact hu.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ hbound n le_rfl k p hc.1 hc.2)

/-- The original scalar series defining the remainder actually converges
absolutely (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem summable_norm_imageBesselLatticeTerm_of_offDiagonalBounds
    {p : E × E} (hp : p ∈ imageBesselComparisonDomain d) :
    Summable (fun k : Fin d → ℤ ↦ ‖imageBesselLatticeTerm k p‖) := by
  simpa only [norm_iteratedFDeriv_zero] using
    summable_norm_iteratedFDeriv_imageBesselLatticeTerm_of_offDiagonalBounds hK hdecay 0 hp

/-- Convergence of the literal terms of the image remainder, rather than
merely a totalized sum (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem summable_imageBesselLatticeTerm_of_offDiagonalBounds
    {p : E × E} (hp : p ∈ imageBesselComparisonDomain d) :
    Summable (fun k : Fin d → ℤ ↦ imageBesselLatticeTerm k p) :=
  (summable_norm_imageBesselLatticeTerm_of_offDiagonalBounds hK hdecay hp).of_norm

/-- The series of jets has as its derivative the series of next derivatives.
Local uniform majorants justify this passage in
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem hasFDerivAt_tsum_iteratedFDeriv_imageBesselLatticeTerm_of_offDiagonalBounds
    (n : ℕ) {p : E × E} (hp : p ∈ imageBesselComparisonDomain d) :
    HasFDerivAt (fun q : E × E ↦ ∑' k : Fin d → ℤ,
      iteratedFDeriv ℝ n (imageBesselLatticeTerm k) q)
      (∑' k : Fin d → ℤ, fderiv ℝ (iteratedFDeriv ℝ n (imageBesselLatticeTerm k)) p) p := by
  obtain ⟨r, hr₀, hr, ε, hε, hb⟩ := exists_comparison_ball hp
  obtain ⟨u, hu, _, hbound⟩ :=
    exists_summable_imageBesselLatticeTerm_jet_majorant hK hdecay hr₀ hr (n + 1)
  have hdom (q : E × E) (hq : q ∈ Metric.ball p ε) : q ∈ imageBesselComparisonDomain d :=
    ⟨fun i ↦ ((hb q hq).1 i).trans_lt hr, fun i ↦ ((hb q hq).2 i).trans_lt hr⟩
  refine hasFDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball p ε).isPreconnected (fun k q hq ↦ ?_) (fun k q hq ↦ ?_)
    (Metric.mem_ball_self hε)
    (summable_norm_iteratedFDeriv_imageBesselLatticeTerm_of_offDiagonalBounds hK hdecay n hp).of_norm
    (Metric.mem_ball_self hε)
  · exact ((contDiffOn_imageBesselLatticeTerm hK k).contDiffAt
      (isOpen_imageBesselComparisonDomain.mem_nhds (hdom q hq))).differentiableAt_iteratedFDeriv
      (by exact_mod_cast ENat.natCast_lt_top n) |>.hasFDerivAt
  · rw [fderiv_iteratedFDeriv, Function.comp_apply, LinearIsometryEquiv.norm_map]
    exact hbound (n + 1) le_rfl k q (hb q hq).1 (hb q hq).2

/-- Every finite joint derivative of the actual remainder is obtained by
termwise differentiation of its lattice series
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem iteratedFDeriv_imageBesselLatticeRemainder_of_offDiagonalBounds
    (n : ℕ) {p : E × E} (hp : p ∈ imageBesselComparisonDomain d) :
    iteratedFDeriv ℝ n (fun q : E × E ↦ imageBesselLatticeRemainder q.1 q.2) p =
      ∑' k : Fin d → ℤ, iteratedFDeriv ℝ n (imageBesselLatticeTerm k) p := by
  induction n generalizing p with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, imageBesselLatticeRemainder,
      imageBesselLatticeTerm, Function.comp_apply]
    exact (continuousMultilinearCurryFin0 ℝ (E × E) ℝ).symm.toContinuousLinearEquiv.map_tsum
  | succ n ih =>
    have heq : iteratedFDeriv ℝ n (fun q : E × E ↦ imageBesselLatticeRemainder q.1 q.2) =ᶠ[𝓝 p]
        (fun q : E × E ↦ ∑' k : Fin d → ℤ, iteratedFDeriv ℝ n (imageBesselLatticeTerm k) q) :=
      Filter.eventually_of_mem (isOpen_imageBesselComparisonDomain.mem_nhds hp) (fun q hq ↦ ih hq)
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, heq.fderiv_eq,
      (hasFDerivAt_tsum_iteratedFDeriv_imageBesselLatticeTerm_of_offDiagonalBounds hK hdecay n hp).fderiv]
    calc
      _ = ∑' k : Fin d → ℤ, (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (n + 1) ↦ E × E) ℝ).symm
          (fderiv ℝ (iteratedFDeriv ℝ n (imageBesselLatticeTerm k)) p) :=
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E × E) ℝ).symm.toContinuousLinearEquiv.map_tsum
      _ = _ := tsum_congr fun k ↦ congrFun iteratedFDeriv_succ_eq_comp_left.symm p

/-- The Bessel lattice remainder is smooth on the open comparison cube,
assuming exactly off-origin kernel smoothness and rapid decay of its jets.
This supplies the series deduction for `app:ch_background:prop:bg-frame`, Step 1;
the heat-integral construction must instantiate both explicit inputs. -/
theorem contDiffOn_imageBesselLatticeRemainder_of_offDiagonalBounds :
    ContDiffOn ℝ ∞ (fun p : E × E ↦ imageBesselLatticeRemainder p.1 p.2)
      (imageBesselComparisonDomain d) := by
  have hd (n : ℕ) : DifferentiableOn ℝ
      (iteratedFDerivWithin ℝ n (fun p : E × E ↦ imageBesselLatticeRemainder p.1 p.2)
        (imageBesselComparisonDomain d)) (imageBesselComparisonDomain d) := by
    have heq : Set.EqOn
        (iteratedFDerivWithin ℝ n (fun p : E × E ↦ imageBesselLatticeRemainder p.1 p.2)
          (imageBesselComparisonDomain d))
        (fun p : E × E ↦ ∑' k : Fin d → ℤ, iteratedFDeriv ℝ n (imageBesselLatticeTerm k) p)
        (imageBesselComparisonDomain d) := by
      intro p hp
      rw [iteratedFDerivWithin_of_isOpen n isOpen_imageBesselComparisonDomain hp]
      exact iteratedFDeriv_imageBesselLatticeRemainder_of_offDiagonalBounds hK hdecay n hp
    apply DifferentiableOn.congr (f := fun p : E × E ↦
      ∑' k : Fin d → ℤ, iteratedFDeriv ℝ n (imageBesselLatticeTerm k) p) _ heq
    intro p hp
    exact (hasFDerivAt_tsum_iteratedFDeriv_imageBesselLatticeTerm_of_offDiagonalBounds
      hK hdecay n hp).differentiableAt.differentiableWithinAt
  exact (contDiffOn_iff_continuousOn_differentiableOn
    isOpen_imageBesselComparisonDomain.uniqueDiffOn).mpr
    ⟨fun n _ ↦ (hd n).continuousOn, fun n _ ↦ hd n⟩

end JanetCartan.ContinuumNormalReduction.ImageNormal
