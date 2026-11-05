module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.EuclideanKernel.Fourier
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.FourierAction
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.Measure

/-!
# Full lattice periodization of the image Bessel kernel

For `app:ch_background:defn:bg-row` and `app:ch_background:prop:bg-frame`, Step 1,
periodize the literal integrable heat kernel over all integer lattice points.
The centered representative gives a measurable torus realization. Tonelli
controls its absolute convergence and mass; unfolding gives the exact complex
Fourier coefficients with the unit-frequency `2π` convention. The consumer is
the Bessel kernel assembly and its subsequent local periodic comparison.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform
open JanetCartan.AmplitudeBound

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Measurability of the literal heat integral, used for the singular-kernel
periodization in `app:ch_background:prop:bg-frame`, Step 1. -/
theorem measurable_imageBesselKernel : Measurable (imageBesselKernel (d := d)) := by
  have hm : Measurable (fun p : ℝ × E ↦ p.1 ^ (-(1 : ℝ) / 2) * Real.exp (-p.1) *
      imageBesselHeatKernel p.1 p.2) :=
    (Measurable.mul (by fun_prop) (by fun_prop)).mul measurable_imageBesselHeatKernel
  exact (hm.stronglyMeasurable.integral_prod_left'.const_mul _).measurable

private theorem lattice_tsum_add_int {G : Type*} [AddCommMonoid G] [TopologicalSpace G]
    (f : E → G) (x : E) (m : Fin d → ℤ) :
    (∑' k : Fin d → ℤ, f (x + WithLp.toLp 2 (fun i ↦ (m i : ℝ)) +
      WithLp.toLp 2 (fun i ↦ (k i : ℝ)))) =
      ∑' k : Fin d → ℤ, f (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ))) := by
  convert (Equiv.addLeft m).tsum_eq
    (fun k : Fin d → ℤ ↦ f (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))) using 1
  congr 1
  funext k
  congr 1
  ext i
  change x i + (m i : ℝ) + (k i : ℝ) = x i + ((m i + k i : ℤ) : ℝ)
  push_cast
  ring

private theorem lattice_tsum_eq_of_quotient_eq {G : Type*}
    [AddCommMonoid G] [TopologicalSpace G] (f : E → G) {x y : E}
    (h : torusQuotient x = torusQuotient y) :
    (∑' k : Fin d → ℤ, f (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))) =
      ∑' k : Fin d → ℤ, f (y + WithLp.toLp 2 (fun i ↦ (k i : ℝ))) := by
  have hi (i : Fin d) : ∃ k : ℤ, (k : ℝ) = x i - y i := by
    have he : ((x i - y i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub, show (x i : AddCircle (1 : ℝ)) = (y i : AddCircle (1 : ℝ))
        from congrFun h i, sub_self]
    simpa using (AddCircle.coe_eq_zero_iff 1).mp he
  choose m hm using hi
  have hx : x = y + WithLp.toLp 2 (fun i ↦ (m i : ℝ)) := by
    ext i
    change x i = y i + (m i : ℝ)
    rw [hm i]
    ring
  rw [hx, lattice_tsum_add_int]

/-- The full integer-lattice sum of the actual image kernel
(`app:ch_background:prop:bg-frame`, Step 1). -/
def imageBesselLatticePeriodization (x : E) : ℝ :=
  ∑' k : Fin d → ℤ, imageBesselKernel (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))

/-- The centered-representative torus realization of the full lattice sum
(`app:ch_background:defn:bg-row`). -/
def imageBesselTorusKernel (z : Torus d) : ℝ :=
  imageBesselLatticePeriodization (centeredTorusRepresentative z)

/-- The literal lattice sum is integer-periodic, including at points where the
series is totalized (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageBesselLatticePeriodization_add_int (x : E) (m : Fin d → ℤ) :
    imageBesselLatticePeriodization (x + WithLp.toLp 2 (fun i ↦ (m i : ℝ))) =
      imageBesselLatticePeriodization x :=
  lattice_tsum_add_int imageBesselKernel x m

/-- The torus realization agrees with the full lattice sum at every lift
(`app:ch_background:prop:bg-frame`, Step 1). -/
@[simp] theorem imageBesselTorusKernel_torusQuotient (x : E) :
    imageBesselTorusKernel (torusQuotient x) = imageBesselLatticePeriodization x :=
  lattice_tsum_eq_of_quotient_eq imageBesselKernel
    (torusQuotient_centeredTorusRepresentative _)

/-- Measurability suffices for the singular torus kernel in
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem measurable_imageBesselLatticePeriodization :
    Measurable (imageBesselLatticePeriodization (d := d)) :=
  Measurable.tsum (fun _ ↦ measurable_imageBesselKernel.comp (measurable_id.add_const _))

/-- The centered-representative torus kernel is measurable
(`app:ch_background:defn:bg-row`). -/
theorem measurable_imageBesselTorusKernel : Measurable (imageBesselTorusKernel (d := d)) :=
  measurable_imageBesselLatticePeriodization.comp measurable_centeredTorusRepresentative

/-- Nonnegativity survives full lattice periodization
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageBesselTorusKernel_nonneg (z : Torus d) : 0 ≤ imageBesselTorusKernel z :=
  tsum_nonneg (fun _ ↦ imageBesselKernel_nonneg _)

/-- Absolute convergence on the fundamental cube follows from the actual
Euclidean integrability (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem ae_summable_norm_imageBesselKernel_unitCube :
    ∀ᵐ x ∂volume.restrict (unitLatticeIocCube d),
      Summable (fun k : Fin d → ℤ ↦
        ‖imageBesselKernel (WithLp.toLp 2 x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))‖) :=
  ae_summable_norm_unitLattice_translates imageBesselKernel integrable_imageBesselKernel

private theorem lintegral_torus_lattice_enorm :
    (∫⁻ z : Torus d, ∑' k : Fin d → ℤ,
      ‖imageBesselKernel (centeredTorusRepresentative z +
        WithLp.toLp 2 (fun i ↦ (k i : ℝ)))‖ₑ) = ∫⁻ x : E, ‖imageBesselKernel x‖ₑ := by
  rw [torus_volume_eq_pi_haarAddCircle]
  have he := UnitAddTorus.lintegral_preimage (fun z : Torus d ↦ ∑' k : Fin d → ℤ,
    ‖imageBesselKernel (centeredTorusRepresentative z +
      WithLp.toLp 2 (fun i ↦ (k i : ℝ)))‖ₑ) (0 : Fin d → ℝ)
  change (∫⁻ z : Torus d, _ ∂Measure.pi
    (fun _ : Fin d ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle))) = _ at he
  rw [he]
  simp only [Pi.zero_apply, zero_add]
  change (∫⁻ x in unitLatticeIocCube d, ∑' k : Fin d → ℤ,
    ‖imageBesselKernel (centeredTorusRepresentative (torusQuotient (WithLp.toLp 2 x)) +
      WithLp.toLp 2 (fun i ↦ (k i : ℝ)))‖ₑ) = _
  have he (x : Fin d → ℝ) := lattice_tsum_eq_of_quotient_eq
    (fun y : E ↦ ‖imageBesselKernel y‖ₑ)
    (torusQuotient_centeredTorusRepresentative (torusQuotient (WithLp.toLp 2 x)))
  simp_rw [he]
  exact lintegral_unitLatticeIocCube_tsum_enorm imageBesselKernel integrable_imageBesselKernel

/-- The full lattice series converges absolutely for almost every torus point
with normalized volume (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem ae_summable_norm_imageBesselKernel_torus :
    ∀ᵐ z : Torus d, Summable (fun k : Fin d → ℤ ↦
      ‖imageBesselKernel (centeredTorusRepresentative z +
        WithLp.toLp 2 (fun i ↦ (k i : ℝ)))‖) := by
  have hm : Measurable (fun z : Torus d ↦ ∑' k : Fin d → ℤ,
      ‖imageBesselKernel (centeredTorusRepresentative z +
        WithLp.toLp 2 (fun i ↦ (k i : ℝ)))‖ₑ) :=
    Measurable.tsum (fun _ ↦ (measurable_imageBesselKernel.comp
      (measurable_centeredTorusRepresentative.add_const _)).enorm)
  have hfin : (∫⁻ z : Torus d, ∑' k : Fin d → ℤ,
      ‖imageBesselKernel (centeredTorusRepresentative z +
        WithLp.toLp 2 (fun i ↦ (k i : ℝ)))‖ₑ) ≠ ∞ := by
    rw [lintegral_torus_lattice_enorm]
    exact integrable_imageBesselKernel.hasFiniteIntegral.ne
  filter_upwards [ae_lt_top' hm.aemeasurable hfin] with z hz
  exact tsum_enorm_ne_top_iff_summable_norm.mp hz.ne

/-- The actual lattice series has the stated torus value almost everywhere
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem ae_hasSum_imageBesselKernel_torus :
    ∀ᵐ z : Torus d, HasSum (fun k : Fin d → ℤ ↦
      imageBesselKernel (centeredTorusRepresentative z +
        WithLp.toLp 2 (fun i ↦ (k i : ℝ)))) (imageBesselTorusKernel z) := by
  filter_upwards [ae_summable_norm_imageBesselKernel_torus (d := d)] with z hz
  exact hz.of_norm.hasSum

/-- The singular torus kernel is integrable, without any continuity assumption
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integrable_imageBesselTorusKernel : Integrable (imageBesselTorusKernel (d := d)) := by
  refine ⟨measurable_imageBesselTorusKernel.aestronglyMeasurable, ?_⟩
  apply lt_of_le_of_lt (lintegral_mono (fun z : Torus d ↦
    enorm_tsum_le_tsum_enorm (f := fun k : Fin d → ℤ ↦
      imageBesselKernel (centeredTorusRepresentative z +
        WithLp.toLp 2 (fun i ↦ (k i : ℝ))))))
  rw [lintegral_torus_lattice_enorm]
  exact integrable_imageBesselKernel.hasFiniteIntegral

/-- The full periodization preserves unit mass under normalized torus volume
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integral_imageBesselTorusKernel : (∫ z : Torus d, imageBesselTorusKernel z) = 1 := by
  rw [torus_volume_eq_pi_haarAddCircle]
  have he := UnitAddTorus.integral_preimage (imageBesselTorusKernel (d := d)) (0 : Fin d → ℝ)
  change (∫ z : Torus d, imageBesselTorusKernel z ∂Measure.pi
    (fun _ : Fin d ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle))) = _ at he
  rw [he]
  simp only [Pi.zero_apply, zero_add]
  change (∫ x in unitLatticeIocCube d,
    imageBesselTorusKernel (torusQuotient (WithLp.toLp 2 x))) = 1
  simp_rw [imageBesselTorusKernel_torusQuotient, imageBesselLatticePeriodization]
  rw [integral_unitLatticeIocCube_tsum imageBesselKernel integrable_imageBesselKernel,
    integral_imageBesselKernel]

/-- The complex Fourier coefficients of the actual full periodization are
exactly the row's periodic Bessel symbol. Normalized unit-torus volume and the
physical factor `2π` agree (`app:ch_background:defn:bg-row`,
`app:ch_background:prop:bg-frame`, Step 1). -/
theorem mFourierCoeff_imageBesselTorusKernel (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun z : Torus d ↦ (imageBesselTorusKernel z : ℂ)) k =
      (ContinuumRow.periodicBesselSymbol k : ℂ) := by
  let g : E → ℂ := fun x ↦
    UnitAddTorus.mFourier (-k) (torusQuotient x) * (imageBesselKernel x : ℂ)
  have hg : Integrable g := by
    simp only [g, mFourier_neg_torusQuotient_eq_fourierChar,
      ← smul_eq_mul, ← Circle.smul_def]
    exact (Real.fourierIntegral_convergent_iff _).mpr integrable_imageBesselKernel.ofReal
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ _ (0 : Fin d → ℝ)]
  simp only [Pi.zero_apply, zero_add]
  change (∫ x in unitLatticeIocCube d,
    UnitAddTorus.mFourier (-k) (torusQuotient (WithLp.toLp 2 x)) *
      (imageBesselTorusKernel (torusQuotient (WithLp.toLp 2 x)) : ℂ)) = _
  calc
    _ = ∫ x in unitLatticeIocCube d, ∑' m : Fin d → ℤ,
        g (WithLp.toLp 2 x + WithLp.toLp 2 (fun i ↦ (m i : ℝ))) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [imageBesselTorusKernel_torusQuotient, imageBesselLatticePeriodization,
        Complex.ofReal_tsum, ← tsum_mul_left]
      apply tsum_congr
      intro m
      dsimp only [g]
      rw [show torusQuotient (WithLp.toLp 2 x + WithLp.toLp 2 (fun i ↦ (m i : ℝ))) =
        torusQuotient (WithLp.toLp 2 x) from torusQuotient_add_integerTranslation _ m]
    _ = ∫ x, g x := integral_unitLatticeIocCube_tsum g hg
    _ = (ContinuumRow.periodicBesselSymbol k : ℂ) := by
      have he := fourier_imageBesselKernel (WithLp.toLp 2 (fun i ↦ (k i : ℝ)) : E)
      rw [imageBesselSymbol_integer] at he
      simpa only [g, mFourier_neg_torusQuotient_eq_fourierChar, Real.fourier_eq,
        Circle.smul_def, smul_eq_mul] using he

end JanetCartan.ContinuumNormalReduction.ImageNormal
