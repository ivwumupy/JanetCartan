module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.PhysicalL2
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.WeakDerivatives
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Hilbert

/-!
# The real quadrature on physical Sobolev levels

For `app:ch_background:eq:bg-density-adjoint` before the physical cutoff,
real outputs are literally complexified in the shared physical Sobolev scale.
Weak derivatives commute with the real quadrature in every physical direction.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped SchwartzMap LineDeriv
namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev Pseudodifferential
variable {n s : ℕ}

/-- Literal complexification of real physical L² data, used for the output of
`app:ch_background:eq:bg-density-adjoint` in the shared complex scale. -/
def physicalComplexifyL2 : Lp ℝ 2 (carrierMeasure n) →L[ℝ] CarrierL2 n :=
  Complex.ofRealCLM.compLpL 2 (carrierMeasure n)

/-- Complexification retains the actual real representative
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem physicalComplexifyL2_coeFn (u : Lp ℝ 2 (carrierMeasure n)) :
    physicalComplexifyL2 u =ᵐ[carrierMeasure n] fun x ↦ (u x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL u

/-- Complexification is an isometry on the actual physical L² classes
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_physicalComplexifyL2 (u : Lp ℝ 2 (carrierMeasure n)) :
    ‖physicalComplexifyL2 u‖ = ‖u‖ := by
  apply le_antisymm <;> apply Lp.norm_le_norm_of_ae_le <;>
    filter_upwards [physicalComplexifyL2_coeFn u] with x hx <;>
    simp [hx]


/-- The actual uncut real L² operator, with its output literally complexified
for `app:ch_background:eq:bg-density-adjoint`. -/
def complexTwoReL2 : CarrierL2 n →L[ℝ] CarrierL2 n :=
  physicalComplexifyL2.comp twoReL2

/-- Compatibility with the existing real L² operator
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem complexTwoReL2_eq (u : CarrierL2 n) :
    complexTwoReL2 u = physicalComplexifyL2 (twoReL2 u) := rfl

/-- The complex representative is exactly twice the real part
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem complexTwoReL2_coeFn (u : CarrierL2 n) :
    complexTwoReL2 u =ᵐ[carrierMeasure n] fun x ↦ ((2 * (u x).re : ℝ) : ℂ) := by
  filter_upwards [physicalComplexifyL2_coeFn (twoReL2 u), twoReL2_coeFn u] with x hx hy
  exact hx.trans (congrArg (fun r : ℝ ↦ (r : ℂ)) hy)

/-- The complexification retains the physical factor-two bound
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_complexTwoReL2_le (u : CarrierL2 n) : ‖complexTwoReL2 u‖ ≤ 2 * ‖u‖ := by
  rw [complexTwoReL2_eq, norm_physicalComplexifyL2]
  exact norm_twoReL2_le u

private theorem flat_compLp (T : ℂ →L[ℝ] ℂ) (u : CarrierL2 n) :
    flatInitialL2Equiv n (T.compLp u) = T.compLp (flatInitialL2Equiv n u) := by
  apply Lp.ext
  filter_upwards [flatInitialL2Equiv_coeFn n (T.compLp u),
    (flatInitialCoordinates_symm_measurePreserving n).quasiMeasurePreserving.ae_eq_comp
      (T.coeFn_compLp u),
    T.coeFn_compLp (flatInitialL2Equiv n u), flatInitialL2Equiv_coeFn n u]
    with x h₁ h₂ h₃ h₄
  exact h₁.trans (h₂.trans (by rw [h₃, h₄]; rfl))

private theorem conj_schwartz_deriv {d : ℕ}
    (φ : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (v : EuclideanSpace ℝ (Fin d)) (x) :
    (∂_{v} (φ.postcompCLM Complex.conjCLE.toContinuousLinearMap)) x =
      starRingEnd ℂ ((∂_{v} φ) x) := by
  change fderiv ℝ (Complex.conjCLE.toContinuousLinearMap ∘ φ) x v = _
  rw [(Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x (φ.hasFDerivAt x)).fderiv]
  rfl

private theorem coordinateDerivative_conj {d : ℕ} {i : Fin d}
    {u v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))}
    (h : HasEuclideanL2CoordinateDerivative i u v) :
    HasEuclideanL2CoordinateDerivative i (Complex.conjCLE.toContinuousLinearMap.compLp u)
      (Complex.conjCLE.toContinuousLinearMap.compLp v) := by
  ext φ
  have he := congrArg (fun T : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ) ↦
    starRingEnd ℂ (T (φ.postcompCLM Complex.conjCLE.toContinuousLinearMap))) h
  simp only [euclideanCoordinateDerivative, TemperedDistribution.lineDerivOp_apply_apply,
    Lp.toTemperedDistribution_apply,
    map_neg, ← integral_conj, smul_eq_mul, map_mul,
    SchwartzMap.postcompCLM_apply, conj_schwartz_deriv, Complex.conjCLE_apply,
    ContinuousLinearEquiv.coe_coe, RingHomCompTriple.comp_apply, RingHom.id_apply] at he
  simp only [euclideanCoordinateDerivative, TemperedDistribution.lineDerivOp_apply_apply,
    Lp.toTemperedDistribution_apply, neg_apply, smul_eq_mul, neg_mul, integral_neg]
  convert he using 1
  · congr 1
    apply integral_congr_ae
    filter_upwards [Complex.conjCLE.toContinuousLinearMap.coeFn_compLp u] with x hx
    simp [hx]
  · apply integral_congr_ae
    filter_upwards [Complex.conjCLE.toContinuousLinearMap.coeFn_compLp v] with x hx
    simp [hx]

private theorem coordinateDerivative_add {d : ℕ} {i : Fin d}
    {u v a b : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))}
    (h : HasEuclideanL2CoordinateDerivative i u v)
    (k : HasEuclideanL2CoordinateDerivative i a b) :
    HasEuclideanL2CoordinateDerivative i (u + a) (v + b) := by
  unfold HasEuclideanL2CoordinateDerivative euclideanCoordinateDerivative at *
  simp only [← Lp.toTemperedDistributionCLM_apply, map_add] at *
  rw [LineDeriv.lineDerivOp_add, h, k]

private theorem complexTwoReL2_add_conj (u : CarrierL2 n) :
    complexTwoReL2 u = u + Complex.conjCLE.toContinuousLinearMap.compLp u := by
  apply Lp.ext
  filter_upwards [complexTwoReL2_coeFn u,
    Complex.conjCLE.toContinuousLinearMap.coeFn_compLp u,
    Lp.coeFn_add u (Complex.conjCLE.toContinuousLinearMap.compLp u)] with x hx hy hz
  rw [hx, hz, Pi.add_apply, hy]
  exact (Complex.add_conj (u x)).symm

/-- Twice the real part commutes with each actual weak derivative, including
all three carrier coordinates and every initial coordinate, for
`app:ch_background:eq:bg-density-adjoint`. -/
theorem hasCarrierL2CoordinateDerivative_complexTwoReL2
    {i : Fin (3 + (n - 1))} {u v : CarrierL2 n}
    (h : HasCarrierL2CoordinateDerivative i u v) :
    HasCarrierL2CoordinateDerivative i (complexTwoReL2 u) (complexTwoReL2 v) := by
  unfold HasCarrierL2CoordinateDerivative at *
  simp only [complexTwoReL2_add_conj, map_add, flat_compLp]
  exact coordinateDerivative_add h (coordinateDerivative_conj h)

/-- The entire mixed weak derivative family is transported by the actual
real-quadrature L² operator (`app:ch_background:eq:bg-density-adjoint`). -/
theorem hasCarrierL2Derivatives_complexTwoReL2 {u : CarrierL2 n}
    {v : CarrierL2DerivativeFamily n s} (h : HasCarrierL2Derivatives s u v) :
    HasCarrierL2Derivatives s (complexTwoReL2 u) (fun w ↦ complexTwoReL2 (v w)) := by
  induction s generalizing u with
  | zero =>
    rw [hasCarrierL2Derivatives_zero_iff] at *
    rw [h]
  | succ s ih =>
    rw [hasCarrierL2Derivatives_succ_iff] at *
    refine ⟨congrArg complexTwoReL2 h.1, fun i ↦ ?_⟩
    exact ⟨hasCarrierL2CoordinateDerivative_complexTwoReL2 (h.2 i).1, ih (h.2 i).2⟩

/-- The uncut real density preserves every integer physical Sobolev level.
Output membership follows from actual weak derivatives, for
`app:ch_background:eq:bg-density-adjoint`. -/
theorem memPhysicalSobolev_complexTwoReL2 {u : CarrierL2 n}
    (hu : MemPhysicalSobolev s u) : MemPhysicalSobolev s (complexTwoReL2 u) := by
  obtain ⟨v, hv⟩ := hu.exists_carrierL2Derivatives
  exact (hasCarrierL2Derivatives_complexTwoReL2 hv).memPhysicalSobolev

/-- A datum-independent bound at every shared physical Sobolev level, before
`χ_y`, for `app:ch_background:eq:bg-density-adjoint`. The explicit constant
comes from the checked comparison with all mixed weak derivatives. -/
theorem physicalSobolevNorm_complexTwoReL2_le {u : CarrierL2 n}
    (hu : MemPhysicalSobolev s u) :
    physicalSobolevNorm s (complexTwoReL2 u) ≤
      ((4 * Real.pi) ^ s * 2 * (1 + 2 * Real.pi * (3 + (n - 1) : ℕ)) ^ s) *
        physicalSobolevNorm s u := by
  obtain ⟨v, hv⟩ := hu.exists_carrierL2Derivatives
  have hsum : carrierL2DerivativeNormSum (fun w ↦ complexTwoReL2 (v w)) ≤
      2 * carrierL2DerivativeNormSum v := by
    unfold carrierL2DerivativeNormSum
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun w _ ↦ norm_complexTwoReL2_le (v w))
  calc
    _ ≤ (4 * Real.pi) ^ s * carrierL2DerivativeNormSum
        (fun w ↦ complexTwoReL2 (v w)) :=
      (hasCarrierL2Derivatives_complexTwoReL2 hv).physicalSobolevNorm_le
    _ ≤ (4 * Real.pi) ^ s * (2 * carrierL2DerivativeNormSum v) := by gcongr
    _ ≤ (4 * Real.pi) ^ s *
        (2 * ((1 + 2 * Real.pi * (3 + (n - 1) : ℕ)) ^ s * physicalSobolevNorm s u)) := by
      gcongr
      exact hv.normSum_le_physicalSobolevNorm
    _ = _ := by ring

/-- Twice the real quadrature as a bounded real-linear map on the existing
complex physical Hilbert level (`app:ch_background:eq:bg-density-adjoint`). -/
def twoRePhysicalSobolev (s : ℕ) : PhysicalSobolevSpace n s →L[ℝ] PhysicalSobolevSpace n s :=
  LinearMap.mkContinuous
    { toFun := fun u ↦ PhysicalSobolevSpace.ofL2 s
        (complexTwoReL2 (PhysicalSobolevSpace.toL2 s u))
        (memPhysicalSobolev_complexTwoReL2 (PhysicalSobolevSpace.toL2_mem s u))
      map_add' := by
        intro u v
        apply PhysicalSobolevSpace.toL2_injective s
        simp only [PhysicalSobolevSpace.toL2_ofL2, map_add]
      map_smul' := by
        intro c u
        apply PhysicalSobolevSpace.toL2_injective s
        have hm (w : PhysicalSobolevSpace n s) :
            PhysicalSobolevSpace.toL2 s (c • w) = c • PhysicalSobolevSpace.toL2 s w :=
          ((PhysicalSobolevSpace.toL2 s).restrictScalars ℝ).map_smul c w
        simp only [PhysicalSobolevSpace.toL2_ofL2, hm, map_smul, RingHom.id_apply] }
    ((4 * Real.pi) ^ s * 2 * (1 + 2 * Real.pi * (3 + (n - 1) : ℕ)) ^ s)
    (fun u ↦ by
      simp only [PhysicalSobolevSpace.norm_eq]
      exact physicalSobolevNorm_complexTwoReL2_le (PhysicalSobolevSpace.toL2_mem s u))

/-- The bounded Sobolev operator is the literal complexification of the
already constructed real L² operator, for
`app:ch_background:eq:bg-density-adjoint`. -/
theorem toL2_twoRePhysicalSobolev (s : ℕ) (u : PhysicalSobolevSpace n s) :
    PhysicalSobolevSpace.toL2 s (twoRePhysicalSobolev s u) =
      physicalComplexifyL2 (twoReL2 (PhysicalSobolevSpace.toL2 s u)) := rfl

/-- The uncut density bound on the actual Hilbert norm, at every integer
level (`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_twoRePhysicalSobolev_le (s : ℕ) (u : PhysicalSobolevSpace n s) :
    ‖twoRePhysicalSobolev s u‖ ≤
      ((4 * Real.pi) ^ s * 2 * (1 + 2 * Real.pi * (3 + (n - 1) : ℕ)) ^ s) * ‖u‖ := by
  simp only [PhysicalSobolevSpace.norm_eq, toL2_twoRePhysicalSobolev]
  exact physicalSobolevNorm_complexTwoReL2_le (PhysicalSobolevSpace.toL2_mem s u)

end JanetCartan.ContinuumAdjoint.DensityMultiplier
