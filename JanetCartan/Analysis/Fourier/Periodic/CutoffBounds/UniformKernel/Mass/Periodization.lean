module
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.UniformKernel.Mass.Euclidean
public import JanetCartan.Analysis.Fourier.Periodic.Parseval
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
/-!
# L¹ bounds for unit-lattice periodization

For `main:lem:smoothing` and `main:eq:smoothing-low` of `paper.tex`, periodizing an
integrable Euclidean kernel does not increase its L¹ mass. The product cube
`(0, 1]^n` tiles coordinate space under integer translations. Tonelli's theorem
then gives absolute summability almost everywhere on the cube and justifies
interchanging the lattice sum and the Bochner integral. The torus integral uses
the project's normalized unit-period Haar measure and Euclidean volume.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace JanetCartan

private local instance latticeAddAction (n : ℕ) : AddAction (Fin n → ℤ) (Fin n → ℝ) where
  vadd k x := x + fun i ↦ (k i : ℝ)
  zero_vadd x := by
    change x + (fun i ↦ ((0 : Fin n → ℤ) i : ℝ)) = x
    simp only [Pi.zero_apply, Int.cast_zero]
    exact add_zero x
  add_vadd k l x := by
    change x + (fun i ↦ ((k + l) i : ℝ)) =
      (x + fun i ↦ (l i : ℝ)) + fun i ↦ (k i : ℝ)
    ext i
    simp only [Pi.add_apply, Int.cast_add]
    ring

private local instance latticeMeasurableConstVAdd (n : ℕ) :
    MeasurableConstVAdd (Fin n → ℤ) (Fin n → ℝ) where
  measurable_const_vadd k := measurable_id.add_const (fun i ↦ (k i : ℝ))

private local instance latticeVAddInvariantMeasure (n : ℕ) :
    VAddInvariantMeasure (Fin n → ℤ) (Fin n → ℝ) volume where
  measure_preimage_vadd k _s hs := (measurePreserving_add_right volume
    (fun i ↦ (k i : ℝ))).measure_preimage hs.nullMeasurableSet

/-- The half-open coordinate cube used to periodize the kernels in
`main:lem:smoothing`. Its integer translates tile space, including when `n = 0`. -/
def unitLatticeIocCube (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i ∈ Ioc (0 : ℝ) 1}

/-- The unit cube is a fundamental domain for coordinatewise integer translation. -/
private theorem cube_fundamentalDomain (n : ℕ) :
    IsAddFundamentalDomain (Fin n → ℤ) (unitLatticeIocCube n) volume := by
  apply IsAddFundamentalDomain.mk'
    (MeasurableSet.univ_pi' (fun _ ↦ measurableSet_Ioc)).nullMeasurableSet
  intro x
  refine ⟨fun i ↦ 1 - ⌈x i⌉, ?_, ?_⟩
  · intro i
    have hi := Int.ceil_eq_iff.mp (rfl : ⌈x i⌉ = ⌈x i⌉)
    change 0 < x i + ((1 - ⌈x i⌉ : ℤ) : ℝ) ∧
      x i + ((1 - ⌈x i⌉ : ℤ) : ℝ) ≤ 1
    push_cast
    constructor <;> linarith [hi.1, hi.2]
  · intro k hk
    ext i
    have hi : ⌈x i + (k i : ℝ)⌉ = 1 :=
      Int.ceil_eq_iff.mpr (by
        have hki := hk i
        change 0 < x i + (k i : ℝ) ∧ x i + (k i : ℝ) ≤ 1 at hki
        simpa using hki)
    rw [Int.ceil_add_intCast] at hi
    omega

/-- `main:lem:smoothing`: Tonelli unfolding of the unit-lattice sum of a
nonnegative measurable function over the fundamental cube. -/
theorem lintegral_unitLatticeIocCube_tsum (n : ℕ)
    (f : (Fin n → ℝ) → ℝ≥0∞) (hf : AEMeasurable f volume) :
    (∫⁻ x in unitLatticeIocCube n, ∑' k : Fin n → ℤ,
      f (x + fun i ↦ (k i : ℝ))) = ∫⁻ x, f x := by
  rw [lintegral_tsum]
  · exact (cube_fundamentalDomain n).lintegral_eq_tsum'' f |>.symm
  · intro k
    exact (hf.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume (fun i ↦ (k i : ℝ))).quasiMeasurePreserving).restrict

variable {n : ℕ} {G : Type*} [NormedAddCommGroup G]

set_option backward.isDefEq.respectTransparency false in
/-- `main:eq:smoothing-low`: the sum of the translated Euclidean kernel norms
has exactly the original Euclidean mass on the fundamental cube. -/
theorem lintegral_unitLatticeIocCube_tsum_enorm
    (f : EuclideanSpace ℝ (Fin n) → G) (hf : Integrable f) :
    (∫⁻ x in unitLatticeIocCube n, ∑' k : Fin n → ℤ,
      ‖f (WithLp.toLp 2 x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))‖ₑ) =
      ∫⁻ x, ‖f x‖ₑ := by
  have hm : AEMeasurable (fun x : Fin n → ℝ ↦ ‖f (WithLp.toLp 2 x)‖ₑ) volume :=
    hf.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
      (PiLp.volume_preserving_toLp (Fin n)).quasiMeasurePreserving
  calc
    _ = ∫⁻ x : Fin n → ℝ, ‖f (WithLp.toLp 2 x)‖ₑ :=
      lintegral_unitLatticeIocCube_tsum n _ hm
    _ = _ := (PiLp.volume_preserving_toLp (Fin n)).lintegral_comp_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding (fun x ↦ ‖f x‖ₑ)

/-- `main:lem:smoothing`: integrability implies absolute summability of the
unit-lattice translates almost everywhere on the fundamental cube. -/
theorem ae_summable_norm_unitLattice_translates
    (f : EuclideanSpace ℝ (Fin n) → G) (hf : Integrable f) :
    ∀ᵐ x ∂volume.restrict (unitLatticeIocCube n),
      Summable (fun k : Fin n → ℤ ↦
        ‖f (WithLp.toLp 2 x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))‖) := by
  have hm (k : Fin n → ℤ) :
      AEMeasurable (fun x : Fin n → ℝ ↦
        ‖f (WithLp.toLp 2 x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))‖ₑ)
        (volume.restrict (unitLatticeIocCube n)) := by
    exact (hf.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
      ((PiLp.volume_preserving_toLp (Fin n)).comp
        (measurePreserving_add_right volume (fun i ↦ (k i : ℝ)))).quasiMeasurePreserving).restrict
  have hfin : (∫⁻ x in unitLatticeIocCube n, ∑' k : Fin n → ℤ,
      ‖f (WithLp.toLp 2 x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))‖ₑ) ≠ ∞ := by
    rw [lintegral_unitLatticeIocCube_tsum_enorm f hf]
    exact hf.hasFiniteIntegral.ne
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hfin] with x hx
  exact tsum_enorm_ne_top_iff_summable_norm.mp hx.ne

/-- `main:lem:smoothing`: the lattice series of an integrable Banach-valued
kernel converges almost everywhere on the fundamental cube. -/
theorem ae_summable_unitLattice_translates [CompleteSpace G]
    (f : EuclideanSpace ℝ (Fin n) → G) (hf : Integrable f) :
    ∀ᵐ x ∂volume.restrict (unitLatticeIocCube n),
      Summable (fun k : Fin n → ℤ ↦
        f (WithLp.toLp 2 x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))) := by
  filter_upwards [ae_summable_norm_unitLattice_translates f hf] with x hx
  exact hx.of_norm

set_option backward.isDefEq.respectTransparency false in
/-- `main:lem:smoothing`: integrability alone justifies interchanging the
unit-lattice sum and the Bochner integral; unfolding gives the Euclidean integral. -/
theorem integral_unitLatticeIocCube_tsum [NormedSpace ℝ G] [CompleteSpace G]
    (f : EuclideanSpace ℝ (Fin n) → G) (hf : Integrable f) :
    (∫ x in unitLatticeIocCube n, ∑' k : Fin n → ℤ,
      f (WithLp.toLp 2 x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))) = ∫ x, f x := by
  have hm (k : Fin n → ℤ) :
      AEStronglyMeasurable (fun x : Fin n → ℝ ↦
        f (WithLp.toLp 2 x + WithLp.toLp 2 (fun i ↦ (k i : ℝ))))
        (volume.restrict (unitLatticeIocCube n)) := by
    exact (hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      ((PiLp.volume_preserving_toLp (Fin n)).comp
        (measurePreserving_add_right volume (fun i ↦ (k i : ℝ)))).quasiMeasurePreserving).restrict
  have hfin : (∑' k : Fin n → ℤ, ∫⁻ x in unitLatticeIocCube n,
      ‖f (WithLp.toLp 2 x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))‖ₑ) ≠ ∞ := by
    rw [← lintegral_tsum (fun k ↦ (hm k).enorm),
      lintegral_unitLatticeIocCube_tsum_enorm f hf]
    exact hf.hasFiniteIntegral.ne
  rw [integral_tsum hm hfin]
  have hi : Integrable (fun x : Fin n → ℝ ↦ f (WithLp.toLp 2 x)) :=
    ((PiLp.volume_preserving_toLp (Fin n)).integrable_comp hf.aestronglyMeasurable).mpr hf
  calc
    _ = ∫ x : Fin n → ℝ, f (WithLp.toLp 2 x) :=
      ((cube_fundamentalDomain n).integral_eq_tsum'' _ hi).symm
    _ = _ := (PiLp.volume_preserving_toLp (Fin n)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding f

set_option backward.isDefEq.respectTransparency false in
/-- `main:eq:smoothing-low`: a continuous unit-torus periodization of an
integrable Euclidean kernel has L¹ mass at most the Euclidean L¹ mass. The
periodization identity uses the unscaled integer lattice and the measures are
exactly the project's torus volume and Euclidean volume. -/
theorem integral_norm_torus_periodization_le [NormedSpace ℝ G] [CompleteSpace G]
    (f : EuclideanSpace ℝ (Fin n) → G) (hf : Integrable f)
    (g : Torus n → G) (hg : Continuous g)
    (hperiod : ∀ x, g (torusQuotient x) = ∑' k : Fin n → ℤ,
      f (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))) :
    (∫ y : Torus n, ‖g y‖) ≤ ∫ x, ‖f x‖ := by
  rw [integral_norm_eq_lintegral_enorm hg.aestronglyMeasurable,
    integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable]
  apply ENNReal.toReal_mono hf.hasFiniteIntegral.ne
  rw [torus_volume_eq_pi_haarAddCircle]
  have he := UnitAddTorus.lintegral_preimage (fun y ↦ ‖g y‖ₑ) (0 : Fin n → ℝ)
  change (∫⁻ x : Torus n, ‖g x‖ₑ ∂Measure.pi
    (fun _ : Fin n ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle))) = _ at he
  rw [he]
  simp only [Pi.zero_apply, zero_add]
  change (∫⁻ x in unitLatticeIocCube n, ‖g (torusQuotient (WithLp.toLp 2 x))‖ₑ) ≤ _
  calc
    _ ≤ ∫⁻ x in unitLatticeIocCube n, ∑' k : Fin n → ℤ,
        ‖f (WithLp.toLp 2 x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))‖ₑ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [hperiod]
      exact enorm_tsum_le_tsum_enorm
    _ = _ := lintegral_unitLatticeIocCube_tsum_enorm f hf
end JanetCartan
