module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Basic
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveProfiles

/-!
# Coordinates for the elapsed symbol budgets

The affine pullback in `app:ch_regular_base:eq:fixed-time-representation`
retains both original time variables. The conic comparison below is the
frequency comparison in the derivative paragraph of
`app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FourierIntegral FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
variable {d q : ℕ}

/-- Joint original variables `(t,s,y,η)` for the primitive budgets of
`app:ch_regular_base:lem:retarded-kernel`. Only `η` is normalized. -/
abbrev TwoTimePoint (d : ℕ) := (ℝ × ℝ × Euclidean d) × Euclidean d

/-- The original matrix field, with both time variables differentiated jointly.
Consumer: the elapsed amplitude in `app:ch_regular_base:eq:fixed-time-representation`. -/
def jointAmplitude (b : TwoTimeAmplitude d q) (p : TwoTimePoint d) :
    Matrix (Fin q) (Fin q) ℂ := b p.1.1 p.1.2.1 p.1.2.2 p.2

/-- The original phase, with both time variables differentiated jointly.
Consumer: the elapsed phase in `app:ch_regular_base:eq:fixed-time-representation`. -/
def jointPhase (Ψ : TwoTimePhase d) (p : TwoTimePoint d) : ℝ :=
  Ψ p.1.1 p.1.2.1 p.1.2.2 p.2

/-- The spatial norm does not exceed the spacetime norm, in the conic
comparison of `app:ch_regular_base:lem:retarded-kernel`. -/
theorem norm_spatialPart_le (x : Euclidean (d + 1)) : ‖spatialPart x‖ ≤ ‖x‖ := by
  have h := inner_eq_time_add_spatial x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg x, norm_nonneg (spatialPart x), sq_nonneg (x 0)]

/-- Spatial projection as a fixed continuous linear map. Consumer: joint jet
pullback in `app:ch_regular_base:eq:fixed-time-representation`. -/
def spatialProjection : Euclidean (d + 1) →L[ℝ] Euclidean d :=
  LinearMap.toContinuousLinearMap
    { toFun := spatialPart
      map_add' := by intro x y; ext i; rfl
      map_smul' := by intro a x; ext i; rfl }

/-- Spatial projection commutes with physical covector normalization in
`app:ch_regular_base:eq:fixed-time-representation`. -/
@[simp] theorem spatialPart_smul (a : ℝ) (x : Euclidean (d + 1)) :
    spatialPart (a • x) = a • spatialPart x :=
  (spatialProjection (d := d)).map_smul a x

/-- The full frequency is controlled by its time and spatial parts in the
cone argument of `app:ch_regular_base:lem:retarded-kernel`. -/
theorem norm_le_time_add_spatial (ξ : Euclidean (d + 1)) :
    ‖ξ‖ ≤ |ξ 0| + ‖spatialPart ξ‖ := by
  have h := inner_eq_time_add_spatial ξ ξ
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg ξ, norm_nonneg (spatialPart ξ), abs_nonneg (ξ 0),
    sq_abs (ξ 0), mul_nonneg (abs_nonneg (ξ 0)) (norm_nonneg (spatialPart ξ))]

/-- On the multiplier cone, spatial and spacetime frequencies are comparable.
This is the order-minus-one conversion in `app:ch_regular_base:lem:retarded-kernel`. -/
theorem norm_le_spatial_of_cone {C : ℝ} {ξ : Euclidean (d + 1)}
    (hcone : |ξ 0| ≤ C * ‖spatialPart ξ‖) :
    ‖ξ‖ ≤ (C + 1) * ‖spatialPart ξ‖ := by
  calc
    ‖ξ‖ ≤ |ξ 0| + ‖spatialPart ξ‖ := norm_le_time_add_spatial ξ
    _ ≤ C * ‖spatialPart ξ‖ + ‖spatialPart ξ‖ := by gcongr
    _ = _ := by ring

/-- The inhomogeneous weights compare on the multiplier cone, including the
low-frequency shoulder in `app:ch_regular_base:lem:retarded-kernel`. -/
theorem bracket_le_spatial_of_cone {C : ℝ} (hC : 0 ≤ C)
    {ξ : Euclidean (d + 1)} (hcone : |ξ 0| ≤ C * ‖spatialPart ξ‖) :
    1 + ‖ξ‖ ≤ (C + 1) * (1 + ‖spatialPart ξ‖) := by
  have := norm_le_spatial_of_cone hcone
  nlinarith

/-- The actual order-minus-one weight comparison, with no loss of order.
Consumer: the gain-one amplitude budgets in `app:ch_regular_base:eq:fio-input`. -/
theorem inv_spatial_bracket_le_of_cone {C : ℝ} (hC : 0 ≤ C)
    {ξ : Euclidean (d + 1)} (hcone : |ξ 0| ≤ C * ‖spatialPart ξ‖) :
    (1 + ‖spatialPart ξ‖)⁻¹ ≤ (C + 1) / (1 + ‖ξ‖) := by
  have hη : 0 < 1 + ‖spatialPart ξ‖ := by positivity
  have hξ : 0 < 1 + ‖ξ‖ := by positivity
  apply (le_div_iff₀ hξ).mpr
  rw [inv_mul_eq_div, div_le_iff₀ hη]
  exact bracket_le_spatial_of_cone hC hcone

/-- The linear part of the elapsed substitution. The source position is
retained in the domain, although the original spatial symbol is independent
of it. Consumer: the full joint budgets in the fixed-time representation. -/
def elapsedLinear : Point (d + 1) →L[ℝ] TwoTimePoint d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p ↦ ((p.1.1 0, p.1.1 0, spatialPart p.1.1), spatialPart p.2)
      map_add' := by intro x y; ext <;> rfl
      map_smul' := by intro a x; ext <;> rfl }

/-- The translation carries the exact lower time `s=t-r`, including the
lower-end buffer of `app:ch_regular_base:lem:retarded-kernel`. -/
def elapsedTranslation (r : ℝ) : TwoTimePoint d := ((0, -r, 0), 0)

/-- The actual joint two-time evaluation map in
`app:ch_regular_base:eq:fixed-time-representation`. -/
def elapsedPoint (r : ℝ) (p : Point (d + 1)) : TwoTimePoint d :=
  elapsedLinear p + elapsedTranslation r

/-- Explicit coordinates of the elapsed pullback in the fixed-time representation. -/
@[simp] theorem elapsedPoint_eq (r : ℝ) (p : Point (d + 1)) :
    elapsedPoint r p = ((p.1.1 0, p.1.1 0 - r, spatialPart p.1.1), spatialPart p.2) := by
  simp [elapsedPoint, elapsedLinear, elapsedTranslation, sub_eq_add_neg]

/-- The pullback has operator norm at most one for the joint product norm;
there is no derivative loss and no dependence on elapsed time in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem norm_elapsedLinear_le : ‖elapsedLinear (d := d)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  simp only [one_mul]
  change max (max |p.1.1 0| (max |p.1.1 0| ‖spatialPart p.1.1‖))
    ‖spatialPart p.2‖ ≤ ‖p‖
  have hx : ‖p.1.1‖ ≤ ‖p‖ := (norm_fst_le p.1).trans (norm_fst_le p)
  have ht : |p.1.1 0| ≤ ‖p‖ := (PiLp.norm_apply_le p.1.1 0).trans hx
  exact max_le (max_le ht (max_le ht ((norm_spatialPart_le _).trans hx)))
    ((norm_spatialPart_le _).trans (norm_snd_le p))

/-- The original spatial normalization commutes with the elapsed pullback.
Consumer: both order-zero and order-minus-one amplitude seminorms. -/
theorem elapsedPoint_dilate (r R : ℝ) (p : Point (d + 1)) :
    elapsedPoint r (p.1, R • p.2) = ((elapsedPoint r p).1, R • (elapsedPoint r p).2) := by
  simp

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
