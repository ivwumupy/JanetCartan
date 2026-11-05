module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.PrimitiveRealization.RetardedTests
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.Basic
public import JanetCartan.Analysis.Microlocal.SingleChannel.TimeIntegration
public import JanetCartan.Analysis.Operator.Retarded

/-!
# Euclidean vector L² bounds for the characteristic integral

The scalar strip estimate is transported by the existing measure-preserving
coordinate split and summed over the finite complex fiber. These are the low
bounds needed to realize the SAME graph tests in Euclidean Lebesgue L².
Source: `app:ch_osc:prop:osc-retarded-tube`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.FourierIntegral.RetardedRealization

open RegularSector.Characteristic
variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Y" => Euclidean d
local notation "V" => EuclideanSpace ℂ (Fin r)

/-- Coordinates in the transverse/time order used by the scalar Fubini estimate.
Consumer: `graphRetardedTest_energy_le`; source: `app:ch_osc:prop:osc-retarded-tube`. -/
def retardedCoordinates (t : Fin (d + 1)) : (Y × ℝ) ≃L[ℝ] E :=
  (ContinuousLinearEquiv.prodComm ℝ Y ℝ).trans (coordinateSplit t).symm

/-- No Jacobian factor is lost on passing from Euclidean volume to the product
measure in the retarded bound (`app:ch_osc:prop:osc-retarded-tube`). -/
theorem measurePreserving_retardedCoordinates (t : Fin (d + 1)) :
    MeasurePreserving (retardedCoordinates t) (volume.prod volume) volume := by
  exact ((ResidualCoordinates.measurePreserving_coordinateSplit t).symm
    (coordinateSplit t).toHomeomorph.toMeasurableEquiv).comp
      Measure.measurePreserving_swap

/-- The strip estimate extends to ambient measure because the actual exterior
cutoff vanishes off the strip. Consumer: the vector graph-test estimate below;
source: `app:ch_osc:prop:osc-retarded-tube`. -/
theorem scalar_lower_ambient_bound (a b : ℝ) (hab : a ≤ b)
    (χin χout : ℝ × Y → ℝ) (hin : Continuous χin) (hout : Continuous χout)
    (hsout : ∀ p, p.1 ∉ Icc a b → χout p = 0)
    {Cin Cout : ℝ} (hCin : 0 ≤ Cin) (hCout : 0 ≤ Cout)
    (hbi : ∀ p, |χin p| ≤ Cin) (hbo : ∀ p, |χout p| ≤ Cout)
    (f : ℝ × Y → ℂ)
    (hf : MemLp (fun p : Y × ℝ ↦ f (p.2, p.1)) 2 (volume.prod volume)) :
    (∫ p : Y × ℝ, ‖Retarded.lower a χin χout f (p.2, p.1)‖ ^ 2
      ∂volume.prod volume) ≤
      (Cout * Cin) ^ 2 * (b - a) ^ 2 *
        ∫ p : Y × ℝ, ‖f (p.2, p.1)‖ ^ 2 ∂volume.prod volume := by
  have hle : (volume : Measure Y).prod (volume.restrict (Icc a b)) ≤
      volume.prod volume := Measure.prod_mono le_rfl Measure.restrict_le_self
  have hb := (Retarded.lower_l2_bound volume a b hab χin χout f hCin hCout
    (fun y s _ ↦ hbi (s, y)) (fun y s _ ↦ hbo (s, y))
    (Complex.continuous_ofReal.comp (hin.comp continuous_swap)).aestronglyMeasurable
    (Complex.continuous_ofReal.comp (hout.comp continuous_swap)).aestronglyMeasurable
    (hf.mono_measure hle)).2
  have he : (∫ p : Y × ℝ, ‖Retarded.lower a χin χout f (p.2, p.1)‖ ^ 2
      ∂volume.prod (volume.restrict (Icc a b))) =
      ∫ p : Y × ℝ, ‖Retarded.lower a χin χout f (p.2, p.1)‖ ^ 2
        ∂volume.prod volume := by
    have hμ : ((volume : Measure Y).prod volume).restrict (univ ×ˢ Icc a b) =
        volume.prod (volume.restrict (Icc a b)) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [← hμ]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    have hpt : p.2 ∉ Icc a b := fun h ↦ hp ⟨mem_univ _, h⟩
    simp [Retarded.lower, hsout (p.2, p.1) hpt]
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (integral_mono_measure hle (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))
      (hf.integrable_norm_pow (by norm_num)))
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)))

/-- The finite-fiber energy is exactly the sum of scalar coordinate energies.
Consumer: `graphRetardedTest_energy_le`, with the Euclidean fiber norm required
by `app:ch_osc:prop:osc-retarded-tube`. -/
theorem graphTest_energy_eq_sum (u : graphTestSpace (d + 1) r) :
    (∫ x : E, ‖u.val x‖ ^ 2) = ∑ k : Fin r, ∫ x : E, ‖u.val x k‖ ^ 2 := by
  simp_rw [PiLp.norm_sq_eq_of_L2]
  apply integral_finsetSum
  intro k _
  exact ((graphTest_memLp u).continuousLinearMap_comp
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) k)).integrable_norm_pow (by norm_num)

/-- Actual vector characteristic integration satisfies the scalar energy bound
without a dimension loss. The constant depends only on the two cutoff bounds
and the interval. Consumer: the bounded Euclidean L² realization;
source: `app:ch_osc:prop:osc-retarded-tube`. -/
theorem graphRetardedTest_energy_le (t : Fin (d + 1)) (a b : ℝ) (hab : a ≤ b)
    (χin χout : E → ℝ) (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hK : HasCompactSupport χout)
    (hsout : tsupport χout ⊆ {x | x t ∈ Icc a b})
    {Cin Cout : ℝ} (hCin : 0 ≤ Cin) (hCout : 0 ≤ Cout)
    (hbi : ∀ x, |χin x| ≤ Cin) (hbo : ∀ x, |χout x| ≤ Cout)
    (u : graphTestSpace (d + 1) r) :
    ‖graphTestToLp (graphRetardedTest t a χin χout hin hout hK u)‖ ^ 2 ≤
      (Cout * Cin) ^ 2 * (b - a) ^ 2 * ‖graphTestToLp u‖ ^ 2 := by
  let e := coordinateSplit t
  have hc := measurePreserving_retardedCoordinates t
  have hm := (retardedCoordinates t).toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hb (k : Fin r) :
      (∫ x : E, ‖(graphRetardedTest t a χin χout hin hout hK u).val x k‖ ^ 2) ≤
        (Cout * Cin) ^ 2 * (b - a) ^ 2 * ∫ x : E, ‖u.val x k‖ ^ 2 := by
    rw [← hc.integral_comp hm (fun x ↦
      ‖(graphRetardedTest t a χin χout hin hout hK u).val x k‖ ^ 2),
      ← hc.integral_comp hm (fun x ↦ ‖u.val x k‖ ^ 2)]
    have hid (p : Y × ℝ) :
        ‖(graphRetardedTest t a χin χout hin hout hK u).val
          (retardedCoordinates t p) k‖ ^ 2 =
        ‖Retarded.lower a (χin ∘ e.symm) (χout ∘ e.symm)
          (fun q ↦ u.val (e.symm q) k) (p.2, p.1)‖ ^ 2 := by
      change ‖graphRetardedIntegral t a χin χout u.val (e.symm (p.2, p.1)) k‖ ^ 2 = _
      rw [graphRetardedIntegral_coordinate t a χout hin.continuous u.property.1.continuous]
      simp only [e, ContinuousLinearEquiv.apply_symm_apply, norm_mul,
        Complex.norm_I, one_mul]
    simp_rw [hid]
    refine scalar_lower_ambient_bound a b hab _ _
      (hin.continuous.comp e.symm.continuous) (hout.continuous.comp e.symm.continuous)
      ?_ hCin hCout (fun p ↦ hbi (e.symm p)) (fun p ↦ hbo (e.symm p)) _ ?_
    · intro p hp
      change χout (e.symm p) = 0
      apply image_eq_zero_of_notMem_tsupport
      intro hx
      exact hp (by simpa [e] using hsout hx)
    · exact ((graphTest_memLp u).continuousLinearMap_comp
        (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) k)).comp_measurePreserving hc
  change ‖(graphTest_memLp _).toLp _‖ ^ 2 ≤ _ * ‖(graphTest_memLp u).toLp _‖ ^ 2
  rw [← SingleChannel.integral_norm_sq_eq_toLp_norm_sq,
    ← SingleChannel.integral_norm_sq_eq_toLp_norm_sq,
    graphTest_energy_eq_sum, graphTest_energy_eq_sum, Finset.mul_sum]
  exact Finset.sum_le_sum (fun k _ ↦ hb k)

end JanetCartan.FourierIntegral.RetardedRealization
