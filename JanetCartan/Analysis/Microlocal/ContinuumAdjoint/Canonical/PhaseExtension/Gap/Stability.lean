module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Gap.Frozen

/-!
# Stability estimates for the affine extension

These are conditional calculus estimates for the actual rank-gap construction.
The current-frame comparison must supply the value and derivative errors, and
the fixed cutoff construction must supply the reference error. They are not
existence assertions for those analytic inputs.

Source: `app:ch_background:eq:bg-derivative-trade`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
open ContinuumRow ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts

variable {n : ℕ}

/-- The derivative of the literal affine extension. The derivative of the
cutoff is retained, as required for the global gap construction
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem fderiv_affineExtension
    (A : Euclidean n →L[ℝ] Euclidean (n - 1))
    {χ : Euclidean n × CarrierParameter → ℝ}
    {Y : Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {x : Euclidean n} {z : CarrierParameter}
    (hχ : DifferentiableAt ℝ (fun y ↦ χ (y, z)) x)
    (hY : DifferentiableAt ℝ (fun y ↦ Y (y, z)) x) :
    fderiv ℝ (fun y ↦ affineExtension A χ Y (y, z)) x =
      A + χ (x, z) • (fderiv ℝ (fun y ↦ Y (y, z)) x - A) +
        (fderiv ℝ (fun y ↦ χ (y, z)) x).smulRight (Y (x, z) - A x) := by
  have he : (fun y ↦ affineExtension A χ Y (y, z)) =
      (A + (fun y ↦ χ (y, z)) • ((fun y ↦ Y (y, z)) - A)) := by
    funext y
    rfl
  rw [he]
  simpa only [Pi.sub_apply, add_assoc] using
    (A.hasFDerivAt.add (hχ.hasFDerivAt.smul (hY.hasFDerivAt.sub A.hasFDerivAt))).fderiv

/-- A fixed cutoff transfers a value and spatial-derivative comparison to
the extended derivatives. Its producer in the actual construction is
`ActualPhase.exists_current_comparison_threshold`; this estimate alone is
conditional (`app:ch_background:eq:bg-derivative-trade`). -/
theorem norm_fderiv_affineExtension_sub_le
    (A : Euclidean n →L[ℝ] Euclidean (n - 1))
    {χ : Euclidean n × CarrierParameter → ℝ}
    {Y Z : Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {x : Euclidean n} {z : CarrierParameter}
    (hχ : DifferentiableAt ℝ (fun y ↦ χ (y, z)) x)
    (hY : DifferentiableAt ℝ (fun y ↦ Y (y, z)) x)
    (hZ : DifferentiableAt ℝ (fun y ↦ Z (y, z)) x) :
    ‖fderiv ℝ (fun y ↦ affineExtension A χ Y (y, z)) x -
      fderiv ℝ (fun y ↦ affineExtension A χ Z (y, z)) x‖ ≤
      |χ (x, z)| * ‖fderiv ℝ (fun y ↦ Y (y, z)) x -
        fderiv ℝ (fun y ↦ Z (y, z)) x‖ +
      ‖fderiv ℝ (fun y ↦ χ (y, z)) x‖ * ‖Y (x, z) - Z (x, z)‖ := by
  rw [fderiv_affineExtension A hχ hY, fderiv_affineExtension A hχ hZ]
  have he :
      A + χ (x, z) • (fderiv ℝ (fun y ↦ Y (y, z)) x - A) +
        (fderiv ℝ (fun y ↦ χ (y, z)) x).smulRight (Y (x, z) - A x) -
      (A + χ (x, z) • (fderiv ℝ (fun y ↦ Z (y, z)) x - A) +
        (fderiv ℝ (fun y ↦ χ (y, z)) x).smulRight (Z (x, z) - A x)) =
      χ (x, z) • (fderiv ℝ (fun y ↦ Y (y, z)) x -
        fderiv ℝ (fun y ↦ Z (y, z)) x) +
      (fderiv ℝ (fun y ↦ χ (y, z)) x).smulRight (Y (x, z) - Z (x, z)) := by
    ext v j
    simp only [_root_.add_apply, _root_.sub_apply,
      _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
      PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul,
    ContinuousLinearMap.norm_smulRight_apply, Real.norm_eq_abs])

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- A spatial derivative within `1/2` of the actual frozen reference has
squared transverse gap `1/4`. The final construction must produce this
closeness from a fixed primitive frame threshold
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem transverseGap_of_spatialDerivative_close
    (z₀ : CarrierParameter)
    {Y : Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {x : Euclidean n} {z : CarrierParameter}
    (hclose : ‖fderiv ℝ (fun y ↦ Y (y, z)) x - frozenSpatialReference T z₀‖ ≤ 1 / 2) :
    TransverseGap (1 / 4) (spatialMatrix Y z x) := by
  intro v
  let w : Euclidean (n - 1) := WithLp.toLp 2 v
  let B := fderiv ℝ (fun y ↦ Y (y, z)) x
  let A := frozenSpatialReference T z₀
  have he : ‖B.adjoint w - A.adjoint w‖ ≤ (1 / 2 : ℝ) * ‖w‖ := by
    calc
      _ = ‖(B - A).adjoint w‖ := by rw [map_sub]; rfl
      _ ≤ ‖(B - A).adjoint‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖B - A‖ * ‖w‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ _ := mul_le_mul_of_nonneg_right hclose (norm_nonneg _)
  have hn := norm_le_frozenSpatialReference_adjoint T z₀ w
  have ht := norm_sub_norm_le (A.adjoint w) (B.adjoint w)
  rw [norm_sub_rev] at ht
  have hl : (1 / 2 : ℝ) * ‖w‖ ≤ ‖B.adjoint w‖ := by linarith
  have hs : (1 / 4 : ℝ) * ‖w‖ ^ 2 ≤ ‖B.adjoint w‖ ^ 2 := by
    nlinarith [sq_nonneg (‖B.adjoint w‖ - (1 / 2 : ℝ) * ‖w‖), norm_nonneg w,
      norm_nonneg (B.adjoint w)]
  change (1 / 4 : ℝ) * ‖w‖ ^ 2 ≤
    ‖(fderiv ℝ (fun y ↦ Y (y, z)) x).adjoint w‖ ^ 2 at hs
  rw [← spatialMatrix_mulVec_eq_adjoint Y z x w,
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at hs
  simpa [dotProduct, pow_two, w] using hs

/-- The global assembly estimate, including all carrier labels outside the
cutoff. The two independent producers must supply the frozen cutoff error
and the current-versus-frozen comparison on its compact support; the final
actual construction discharges both from fixed data
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem transverseGap_affineExtension_of_comparison
    (z₀ : CarrierParameter)
    {χ : Euclidean n × CarrierParameter → ℝ}
    {Y : Euclidean n × CarrierParameter → Euclidean (n - 1)}
    (hχ : ContDiff ℝ ∞ χ) (hrange : ∀ p, χ p ∈ Icc (0 : ℝ) 1)
    {M ε : ℝ} (hM : 0 ≤ M) (hsmall : (1 + M) * ε ≤ 1 / 4)
    (hχderiv : ∀ p ∈ tsupport χ, ‖fderiv ℝ (fun y ↦ χ (y, p.2)) p.1‖ ≤ M)
    (hfrozen : ∀ x z,
      ‖fderiv ℝ (fun y ↦ affineExtension (frozenSpatialReference T z₀) χ
          (fun p ↦ frozenSpatialReference T p.2 p.1) (y, z)) x -
        frozenSpatialReference T z₀‖ ≤ 1 / 4)
    (hY : ∀ p ∈ tsupport χ, DifferentiableAt ℝ (fun y ↦ Y (y, p.2)) p.1)
    (hcomparison : ∀ p ∈ tsupport χ,
      ‖Y p - frozenSpatialReference T p.2 p.1‖ ≤ ε ∧
      ‖fderiv ℝ (fun y ↦ Y (y, p.2)) p.1 - frozenSpatialReference T p.2‖ ≤ ε) :
    ∀ x z, TransverseGap (1 / 4)
      (spatialMatrix (affineExtension (frozenSpatialReference T z₀) χ Y) z x) := by
  intro x z
  apply transverseGap_of_spatialDerivative_close T z₀
  by_cases hp : (x, z) ∈ tsupport χ
  · have hc : DifferentiableAt ℝ (fun y ↦ χ (y, z)) x :=
      (hχ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) |>.differentiableAt
    have hb := norm_fderiv_affineExtension_sub_le (frozenSpatialReference T z₀)
      (Z := fun p ↦ frozenSpatialReference T p.2 p.1)
      hc (hY (x, z) hp) (frozenSpatialReference T z).differentiableAt
    have he := hcomparison (x, z) hp
    have hχabs : |χ (x, z)| ≤ 1 := by
      rw [abs_of_nonneg (hrange (x, z)).1]
      exact (hrange (x, z)).2
    have hcut :
        ‖fderiv ℝ (fun y ↦ affineExtension (frozenSpatialReference T z₀) χ Y (y, z)) x -
          fderiv ℝ (fun y ↦ affineExtension (frozenSpatialReference T z₀) χ
            (fun p ↦ frozenSpatialReference T p.2 p.1) (y, z)) x‖ ≤ 1 / 4 := by
      apply hb.trans
      change |χ (x, z)| * ‖fderiv ℝ (fun y ↦ Y (y, z)) x -
          fderiv ℝ (frozenSpatialReference T z) x‖ +
        ‖fderiv ℝ (fun y ↦ χ (y, z)) x‖ * ‖Y (x, z) - frozenSpatialReference T z x‖ ≤ _
      rw [ContinuousLinearMap.fderiv]
      calc
        _ ≤ 1 * ε + M * ε := add_le_add
          (mul_le_mul hχabs he.2 (norm_nonneg _) zero_le_one)
          (mul_le_mul (hχderiv (x, z) hp) he.1 (norm_nonneg _) hM)
        _ = (1 + M) * ε := by ring
        _ ≤ _ := hsmall
    have ht := norm_sub_le_norm_sub_add_norm_sub
      (fderiv ℝ (fun y ↦ affineExtension (frozenSpatialReference T z₀) χ Y (y, z)) x)
      (fderiv ℝ (fun y ↦ affineExtension (frozenSpatialReference T z₀) χ
        (fun p ↦ frozenSpatialReference T p.2 p.1) (y, z)) x)
      (frozenSpatialReference T z₀)
    linarith [hfrozen x z]
  · rw [fderiv_affineExtension_outside _ Y hp, sub_self, norm_zero]
    norm_num

end JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
