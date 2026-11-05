module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.LatticeRemainder.HeatJets.Regularity
public import JanetCartan.Analysis.Operator.MeasureEnvelopes.Derivatives

/-!
# The dominated-integration deduction for the Bessel kernel

This separates the calculus in `app:ch_background:prop:bg-frame`, Step 1,
from the quantitative estimates on the explicit heat jets. The hypothesis
below concerns the actual integrand, and still has to be proved before the
unconditional kernel smoothness and rapid decay results can be asserted.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The dominated-integration step of `app:ch_background:prop:bg-frame`, Step 1.
The parent `HeatJets` construction must supply the integrable bounds for the
actual heat jets; this conditional deduction is not itself that construction. -/
theorem imageBesselKernel_offDiagonal_of_integrable_jet_bounds
    (hbound : ∀ δ : ℝ, 0 < δ → ∀ n m : ℕ, ∃ B : ℝ → ℝ,
      IntegrableOn B (Ioi 0) ∧ ∀ t : ℝ, 0 < t → ∀ x : E, δ ≤ ‖x‖ →
        (1 + ‖x‖) ^ m * ‖iteratedFDeriv ℝ n
          (fun y : E ↦ t ^ (-(1 : ℝ) / 2) * Real.exp (-t) * imageBesselHeatKernel t y) x‖
          ≤ B t) :
    ContDiffOn ℝ ∞ (imageBesselKernel (d := d)) {x : E | x ≠ 0} ∧
      ∀ δ : ℝ, 0 < δ → ∀ n m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, δ ≤ ‖x‖ →
        (1 + ‖x‖) ^ m * ‖iteratedFDeriv ℝ n imageBesselKernel x‖ ≤ C := by
  let A : ℝ → E → ℝ := fun t x ↦
    t ^ (-(1 : ℝ) / 2) * Real.exp (-t) * imageBesselHeatKernel t x
  let F : E → ℝ := fun x ↦ ∫ t in Ioi (0 : ℝ), A t x
  have hA (t : ℝ) : ContDiff ℝ ∞ (A t) :=
    contDiff_const.mul (contDiff_imageBesselHeatKernel t)
  have hm (n : ℕ) (x : E) : AEStronglyMeasurable
      (fun t ↦ iteratedFDeriv ℝ n (A t) x) (volume.restrict (Ioi 0)) :=
    aestronglyMeasurable_imageBesselKernel_integrand_jet n x
  have hlocal (δ : ℝ) (hδ : 0 < δ) :
      ContDiffOn ℝ ∞ F {x : E | δ < ‖x‖} ∧
      ∀ n : ℕ, ∀ x : E, δ < ‖x‖ → iteratedFDeriv ℝ n F x =
        ∫ t in Ioi (0 : ℝ), iteratedFDeriv ℝ n (A t) x := by
    let s : Set E := {x | δ < ‖x‖}
    have hs : IsOpen s := isOpen_lt continuous_const continuous_norm
    choose B hi hb using fun n ↦ hbound δ hδ n 0
    simp only [pow_zero, one_mul] at hb
    have hint (n : ℕ) (x : E) (hx : x ∈ s) : Integrable
        (fun t ↦ iteratedFDeriv ℝ n (A t) x) (volume.restrict (Ioi 0)) := by
      refine (hi n).mono' (hm n x) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hb n t ht x hx.le
    have hid (n : ℕ) (x : E) (hx : x ∈ s) : iteratedFDeriv ℝ n F x =
        ∫ t in Ioi (0 : ℝ), iteratedFDeriv ℝ n (A t) x := by
      apply MeasureEnvelopes.iteratedFDeriv_integral_of_dominated
        (b := B) (r := n) hs
      · exact ae_of_all _ fun t y _ ↦ ((hA t).of_le (by simp)).contDiffAt
      · exact fun j _ y _ ↦ hm j y
      · exact fun j _ ↦ hi j
      · intro j _
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht y hy
        exact hb j t ht y hy.le
      · exact le_rfl
      · exact hx
    have hd (n : ℕ) : DifferentiableOn ℝ
        (fun x ↦ ∫ t in Ioi (0 : ℝ), iteratedFDeriv ℝ n (A t) x) s := by
      intro x hx
      apply DifferentiableAt.differentiableWithinAt
      apply HasFDerivAt.differentiableAt
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F' := fun y t ↦ fderiv ℝ (iteratedFDeriv ℝ n (A t)) y)
        (bound := B (n + 1)) (hs.mem_nhds hx)
      · exact Eventually.of_forall (hm n)
      · exact hint n x hx
      · exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) ℝ).continuous.comp_aestronglyMeasurable (hm (n + 1) x)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht y hy
        simpa only [norm_fderiv_iteratedFDeriv] using hb (n + 1) t ht y hy.le
      · exact hi (n + 1)
      · exact ae_of_all _ fun t y _ ↦
          ((hA t).contDiffAt.differentiableAt_iteratedFDeriv (m := n)
            (by exact_mod_cast ENat.natCast_lt_top n)).hasFDerivAt
    refine ⟨?_, hid⟩
    apply contDiffOn_of_differentiableOn
    intro n _
    apply (hd n).congr
    intro x hx
    have he : iteratedFDerivWithin ℝ n F s x = iteratedFDeriv ℝ n F x := by
      simpa only [univ_inter, iteratedFDerivWithin_univ] using
        (iteratedFDerivWithin_inter_open (f := F) (s := univ) (n := n) hs hx)
    exact he.trans (hid n x hx)
  have hF (x : E) (hx : x ≠ 0) : ContDiffAt ℝ ∞ F x := by
    have hp : 0 < ‖x‖ / 2 := half_pos (norm_pos_iff.mpr hx)
    exact (hlocal (‖x‖ / 2) hp).1.contDiffAt
      ((isOpen_lt continuous_const continuous_norm).mem_nhds (by dsimp; linarith))
  have hid (n : ℕ) (x : E) (hx : x ≠ 0) : iteratedFDeriv ℝ n F x =
      ∫ t in Ioi (0 : ℝ), iteratedFDeriv ℝ n (A t) x := by
    have hp : 0 < ‖x‖ / 2 := half_pos (norm_pos_iff.mpr hx)
    exact (hlocal (‖x‖ / 2) hp).2 n x (by linarith)
  refine ⟨fun x hx ↦ ((hF x hx).const_smul (Real.sqrt Real.pi)⁻¹).contDiffWithinAt, ?_⟩
  intro δ hδ n m
  obtain ⟨B, hi, hb⟩ := hbound δ hδ n m
  let c : ℝ := (Real.sqrt Real.pi)⁻¹
  refine ⟨c * |∫ t in Ioi (0 : ℝ), B t|, by dsimp [c]; positivity, fun x hx ↦ ?_⟩
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hδ.trans_le hx)
  have hnorm : ‖iteratedFDeriv ℝ n imageBesselKernel x‖ =
      c * ‖∫ t in Ioi (0 : ℝ), iteratedFDeriv ℝ n (A t) x‖ := by
    change ‖iteratedFDeriv ℝ n (fun y ↦ c • F y) x‖ = _
    rw [iteratedFDeriv_const_smul_apply' ((hF x hx0).of_le (by simp)), norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (by dsimp [c]; positivity), hid n x hx0]
  have hw : (1 + ‖x‖) ^ m *
      ‖∫ t in Ioi (0 : ℝ), iteratedFDeriv ℝ n (A t) x‖ ≤ ∫ t in Ioi (0 : ℝ), B t := by
    have he : (1 + ‖x‖) ^ m *
        ‖∫ t in Ioi (0 : ℝ), iteratedFDeriv ℝ n (A t) x‖ =
        ‖∫ t in Ioi (0 : ℝ), (1 + ‖x‖) ^ m • iteratedFDeriv ℝ n (A t) x‖ := by
      rw [integral_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [he]
    apply norm_integral_le_of_norm_le hi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hb t ht x hx
  rw [hnorm, ← mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hw.trans (le_abs_self _)) (by dsimp [c]; positivity)

end JanetCartan.ContinuumNormalReduction.ImageNormal
