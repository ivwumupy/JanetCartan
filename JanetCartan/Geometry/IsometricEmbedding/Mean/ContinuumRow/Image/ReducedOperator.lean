module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Cutoff
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.WeakDerivative
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Stress.Reduced.Formula

/-!
# The weak reduced operator on the periodic Sobolev space

The first-order factor of `app:ch_background:defn:bg-row` is constructed from
its scalar coefficient arrays, including the zeroth-order connection term.
The inputs here are continuous coefficients, not an assumed operator bound.
The image-channel parent composes this operator with the actual Bessel inverse.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace JanetCartan.ContinuumRow

variable {n : ℕ}

/-- A matrix unit on the real Euclidean fiber in `app:ch_waves:eq:reduced-symbol`. -/
def reducedMatrixUnit (i k : Fin n) : Euclidean n →L[ℝ] Euclidean n :=
  (PiLp.proj 2 (fun _ : Fin n ↦ ℝ) k).smulRight (EuclideanSpace.single i 1)

/-- The matrix unit inserts the specified input coordinate into row `i`
(`app:ch_waves:eq:reduced-symbol`). -/
theorem reducedMatrixUnit_apply (i k : Fin n) (v : Euclidean n) :
    reducedMatrixUnit i k v = v k • EuclideanSpace.single i 1 := rfl

/-- Matrix units are contractions for the real Hilbert norm
(`app:ch_background:defn:bg-row`). -/
theorem reducedMatrixUnit_norm_le (i k : Fin n) : ‖reducedMatrixUnit i k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa [reducedMatrixUnit_apply, norm_smul, EuclideanSpace.single, PiLp.norm_single]
    using PiLp.norm_apply_le v k

/-- One scalar matrix coefficient acting on the full real L² space
(`app:ch_background:defn:bg-row`). -/
def reducedCoefficientMultiplier (c : C(Torus n, ℝ)) (i k : Fin n) :
    OutputL2 n →L[ℝ] OutputL2 n :=
  (reducedMatrixUnit i k).compLpL 2 volume ∘L cutoffMultiplier c

/-- The actual pointwise action of a scalar matrix coefficient
(`app:ch_waves:eq:reduced-symbol`). -/
theorem reducedCoefficientMultiplier_coeFn (c : C(Torus n, ℝ)) (i k : Fin n)
    (u : OutputL2 n) :
    reducedCoefficientMultiplier c i k u =ᵐ[volume]
      fun x ↦ (c x * u x k) • EuclideanSpace.single i 1 := by
  filter_upwards [(reducedMatrixUnit i k).coeFn_compLpL (cutoffMultiplier c u),
    cutoffMultiplier_coeFn c u] with x h₁ h₂
  change ((reducedMatrixUnit i k).compLpL 2 volume (cutoffMultiplier c u)) x = _
  rw [h₁, h₂, reducedMatrixUnit_apply]
  rfl

/-- The coefficient sup norm controls the corresponding L² multiplier
(`app:ch_background:prop:bg-frame`). -/
theorem reducedCoefficientMultiplier_norm_le (c : C(Torus n, ℝ)) (i k : Fin n) :
    ‖reducedCoefficientMultiplier c i k‖ ≤ ‖c‖ := by
  calc
    _ ≤ ‖(reducedMatrixUnit i k).compLpL 2 (volume : Measure (Torus n))‖ *
        ‖cutoffMultiplier c‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖c‖ := mul_le_mul
      ((ContinuousLinearMap.norm_compLpL_le _).trans (reducedMatrixUnit_norm_le i k))
      (cutoffMultiplier_norm_le c) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- The weak derivative into actual L², with the unit-torus normalization
(`app:ch_background:defn:bg-row`). -/
def reducedCoordinateDerivative (a : Fin n) :
    PeriodicSobolevSpace n (Euclidean n) 1 →L[ℝ] OutputL2 n :=
  PeriodicSobolevSpace.toL2 0 ∘L PeriodicSobolevSpace.coordinateDerivative 0 a

/-- The weak derivative is bounded by the H¹ norm with constant one
(`app:ch_background:prop:bg-frame`). -/
theorem reducedCoordinateDerivative_norm_le (a : Fin n)
    (u : PeriodicSobolevSpace n (Euclidean n) 1) :
    ‖reducedCoordinateDerivative a u‖ ≤ ‖u‖ := by
  exact (PeriodicSobolevSpace.norm_toL2_le 0
    (PeriodicSobolevSpace.coordinateDerivative 0 a u)).trans
      (PeriodicSobolevSpace.norm_coordinateDerivative_le 0 a u)

/-- The explicit low coefficient norm used for the image-channel estimate
(`app:ch_background:prop:bg-frame`). Only fixed coefficient sup norms occur. -/
def reducedCoefficientBound
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ)) : ℝ :=
  (∑ a, ∑ i, ∑ k, ‖c (.inl (a, i, k))‖) + ∑ i, ∑ k, ‖c (.inr (i, k))‖

/-- The first-order reduced operator from H¹ to L², constructed from its
principal and zeroth-order arrays (`app:ch_waves:eq:reduced-symbol`). -/
def reducedWeakOperator
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ)) :
    PeriodicSobolevSpace n (Euclidean n) 1 →L[ℝ] OutputL2 n :=
  (∑ a, ∑ i, ∑ k,
    reducedCoefficientMultiplier (c (.inl (a, i, k))) i k ∘L reducedCoordinateDerivative a) +
    ∑ i, ∑ k, reducedCoefficientMultiplier (c (.inr (i, k))) i k ∘L
      PeriodicSobolevSpace.toL2 1

/-- The coefficient norm is nonnegative (`app:ch_background:prop:bg-frame`). -/
theorem reducedCoefficientBound_nonneg
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ)) :
    0 ≤ reducedCoefficientBound c := by
  unfold reducedCoefficientBound
  positivity

/-- The actual reduced operator bound, including the connection coefficients
(`app:ch_background:prop:bg-frame`). -/
theorem reducedWeakOperator_norm_apply_le
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (u : PeriodicSobolevSpace n (Euclidean n) 1) :
    ‖reducedWeakOperator c u‖ ≤ reducedCoefficientBound c * ‖u‖ := by
  simp only [reducedWeakOperator, add_apply,
    sum_apply, ContinuousLinearMap.comp_apply]
  apply (norm_add_le _ _).trans
  rw [reducedCoefficientBound, add_mul]
  apply add_le_add
  · apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul
      (reducedCoefficientMultiplier_norm_le _ _ _) (reducedCoordinateDerivative_norm_le a u)
      (norm_nonneg _) (norm_nonneg _))
  · apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul
      (reducedCoefficientMultiplier_norm_le _ _ _) (PeriodicSobolevSpace.norm_toL2_le 1 u)
      (norm_nonneg _) (norm_nonneg _))

/-- Operator-norm form of the reduced-operator estimate
(`app:ch_background:prop:bg-frame`). -/
theorem reducedWeakOperator_norm_le
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ)) :
    ‖reducedWeakOperator c‖ ≤ reducedCoefficientBound c :=
  ContinuousLinearMap.opNorm_le_bound _ (reducedCoefficientBound_nonneg c)
    (reducedWeakOperator_norm_apply_le c)

/-- Literal smooth coefficient formula, before passage to L²
(`app:ch_waves:eq:reduced-symbol`). -/
def reducedPeriodicFormula
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (f : Torus n → Euclidean n) (x : Torus n) : Euclidean n :=
  (∑ a, ∑ i, ∑ k, (c (.inl (a, i, k)) x * periodicCoordinateDeriv a f x k) •
    EuclideanSpace.single i 1) +
  ∑ i, ∑ k, (c (.inr (i, k)) x * f x k) • EuclideanSpace.single i 1

/-- On smooth fields the weak derivative has its literal representative
(`app:ch_waves:eq:reduced-symbol`). -/
theorem reducedCoordinateDerivative_ofSmooth_ae (a : Fin n)
    (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) :
    reducedCoordinateDerivative a (PeriodicSobolevSpace.ofSmooth 1 f hf) =ᵐ[volume]
      periodicCoordinateDeriv a f := by
  change PeriodicSobolevSpace.toL2 0
    (PeriodicSobolevSpace.coordinateDerivative 0 a
      (PeriodicSobolevSpace.ofSmooth 1 f hf)) =ᵐ[volume] _
  rw [PeriodicSobolevSpace.coordinateDerivative_ofSmooth]
  exact PeriodicSobolevSpace.toL2_ofSmooth_ae 0 _ _

private theorem coeFn_sum_ae {ι : Type*} [Fintype ι]
    (u : ι → OutputL2 n) (f : ι → Torus n → Euclidean n)
    (h : ∀ i, u i =ᵐ[volume] f i) :
    (∑ i, u i : OutputL2 n) =ᵐ[volume] fun x ↦ ∑ i, f i x := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ u, Filter.eventually_all.mpr h] with x hx hx'
  simp only [Finset.sum_apply] at hx
  exact hx.trans (Finset.sum_congr rfl (fun i _ ↦ hx' i))

/-- The bounded H¹ operator is exactly the actual coefficient expression on
smooth tests (`app:ch_waves:eq:reduced-symbol`). -/
theorem reducedWeakOperator_ofSmooth_ae
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) :
    reducedWeakOperator c (PeriodicSobolevSpace.ofSmooth 1 f hf) =ᵐ[volume]
      reducedPeriodicFormula c f := by
  let u := PeriodicSobolevSpace.ofSmooth 1 f hf
  have hfirst : (∑ a, ∑ i, ∑ k,
      reducedCoefficientMultiplier (c (.inl (a, i, k))) i k
        (reducedCoordinateDerivative a u) : OutputL2 n) =ᵐ[volume]
      fun x ↦ ∑ a, ∑ i, ∑ k,
        (c (.inl (a, i, k)) x * periodicCoordinateDeriv a f x k) •
          EuclideanSpace.single i 1 := by
    apply coeFn_sum_ae
    intro a
    apply coeFn_sum_ae
    intro i
    apply coeFn_sum_ae
    intro k
    filter_upwards [reducedCoefficientMultiplier_coeFn (c (.inl (a, i, k))) i k
      (reducedCoordinateDerivative a u), reducedCoordinateDerivative_ofSmooth_ae a f hf]
      with x h₁ h₂
    rw [h₁, h₂]
  have hzero : (∑ i, ∑ k,
      reducedCoefficientMultiplier (c (.inr (i, k))) i k
        (PeriodicSobolevSpace.toL2 1 u) : OutputL2 n) =ᵐ[volume]
      fun x ↦ ∑ i, ∑ k, (c (.inr (i, k)) x * f x k) • EuclideanSpace.single i 1 := by
    apply coeFn_sum_ae
    intro i
    apply coeFn_sum_ae
    intro k
    filter_upwards [reducedCoefficientMultiplier_coeFn (c (.inr (i, k))) i k
      (PeriodicSobolevSpace.toL2 1 u), PeriodicSobolevSpace.toL2_ofSmooth_ae 1 f hf]
      with x h₁ h₂
    rw [h₁, h₂]
  convert (Lp.coeFn_add _ _).trans (hfirst.add hzero) using 1
  · simp only [reducedWeakOperator, add_apply, sum_apply,
      ContinuousLinearMap.comp_apply, u]
  · rfl

/-- Each row of the smooth expression is the scalar principal-plus-connection
formula (`app:ch_waves:eq:reduced-symbol`). -/
theorem reducedPeriodicFormula_apply
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (f : Torus n → Euclidean n) (x : Torus n) (i : Fin n) :
    reducedPeriodicFormula c f x i =
      (∑ a, ∑ k, c (.inl (a, i, k)) x * periodicCoordinateDeriv a f x k) +
      ∑ k, c (.inr (i, k)) x * f x k := by
  classical
  simp [reducedPeriodicFormula, EuclideanSpace.single, ← Finset.sum_smul, Pi.single_apply, mul_ite]

/-- The smooth periodic coefficient formula agrees with the existing geometric
`P_G` on every chart where the coefficient arrays are the actual arrays.
This is a pointwise coefficient hypothesis, with no operator estimate assumed
(`app:ch_waves:eq:reduced-symbol`; `app:ch_background:defn:bg-row`). -/
theorem reducedPeriodicFormula_eq_geometric
    {N : ℕ} (G : Euclidean n → Euclidean N)
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) (y : Euclidean n)
    (hc : ∀ j, c j (torusQuotient y) = GeometricProfile.geometricReducedCoefficients G y j) :
    reducedPeriodicFormula c f (torusQuotient y) =
      NullTransport.reducedOperator G
        (fun z j ↦ (StressFrame.geometricCubeStress G z j).val) (periodicLift f) y := by
  funext i
  rw [reducedPeriodicFormula_apply, GeometricProfile.reducedOperator_geometricCubeStress_eq]
  simp only [hc, periodicLift, Function.comp_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  have hder := congr_fun (periodicLift_coordinateDeriv
    (hf.comp_clm (PiLp.proj 2 (fun _ : Fin n ↦ ℝ) k)).2 a) y
  rw [periodicCoordinateDeriv_comp_clm hf] at hder
  exact hder

/-- Fixed entrywise sup bounds give an explicit dimensional coefficient bound
for `app:ch_background:prop:bg-frame`, including the zeroth-order term. -/
theorem reducedCoefficientBound_le
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    {C₁ C₀ : ℝ} (hC₁ : 0 ≤ C₁) (hC₀ : 0 ≤ C₀)
    (hfirst : ∀ a i k x, |c (.inl (a, i, k)) x| ≤ C₁)
    (hzero : ∀ i k x, |c (.inr (i, k)) x| ≤ C₀) :
    reducedCoefficientBound c ≤ (n : ℝ) ^ 3 * C₁ + (n : ℝ) ^ 2 * C₀ := by
  have h₁ (a i k : Fin n) : ‖c (.inl (a, i, k))‖ ≤ C₁ :=
    (ContinuousMap.norm_le _ hC₁).mpr (hfirst a i k)
  have h₀ (i k : Fin n) : ‖c (.inr (i, k))‖ ≤ C₀ :=
    (ContinuousMap.norm_le _ hC₀).mpr (hzero i k)
  calc
    reducedCoefficientBound c ≤ (∑ _a : Fin n, ∑ _i : Fin n, ∑ _k : Fin n, C₁) +
        ∑ _i : Fin n, ∑ _k : Fin n, C₀ := by
      unfold reducedCoefficientBound
      exact add_le_add
        (Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun i _ ↦
          Finset.sum_le_sum fun k _ ↦ h₁ a i k)
        (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun k _ ↦ h₀ i k)
    _ = _ := by simp; ring

end JanetCartan.ContinuumRow
