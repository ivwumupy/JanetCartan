module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.SmoothRealization

/-!
# The component operator of the literal smooth raw response

Construct the real Hilbert-space component `A_{ν,K}` in
`main:prop:canonical` from the original raw derivative map, background and
measurement. Its continuity follows from the raw derivative's L² bound and
the proved Hermitian product estimate. No canonical-adjoint estimate is
assumed. The L² identification needed by `completeCanonicalCorrection_toL2`
then holds by construction for this SAME component.

The corrected-atom producer still supplies the actual smooth raw maps and
their primitive L² bounds; the sampling construction must refer to this
literal component or prove agreement with its kernel realization. No
independently selected operator or sample is identified here.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalChange

open ContinuumRow CurrentMean CurrentMean.SmoothPeriodicFamily

variable {n : ℕ} {ι m : Type*} [Fintype m]
    {Raw : ι → Type*} [∀ i, NormedAddCommGroup (Raw i)]
    [∀ i, InnerProductSpace ℝ (Raw i)]
    (base : SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ))
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))

/-- The literal measured cross response in `main:eq:canonical-identity` is
bounded from the raw derivative's L² size, using the original zero atom's
`C^0` size and the actual measurement coefficient. -/
theorem norm_smoothRawCrossResponse_toL2_le (i : ι) (v : Raw i) :
    ‖smoothResidualToL2 n (smoothRawCrossResponse base C hC G i v)‖ ≤
      (2 * cNorm (fundamentalCell n) 0 (periodicLift C) *
        cNorm (fundamentalCell n) 0 (periodicLift (fun x ↦ base.val x i))) *
          periodicL2Norm (fun x ↦ (G i v).val x ()) := by
  let b : SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ) :=
    ⟨fun x _ ↦ base.val x i, fun _ ↦ smooth base i⟩
  have hb := norm_measuredHermitianBilinear_le_cNorm (fun _ : Unit ↦ (1 : ℝ))
    (fun _ ↦ zero_le_one) C hC b (G i v)
  have he : smoothResidualToL2 n (smoothRawCrossResponse base C hC G i v) =
      (2 : ℝ) • measuredHermitianBilinear (fun _ : Unit ↦ (1 : ℝ)) C hC b (G i v) := by
    simp only [smoothRawCrossResponse, LinearMap.smul_apply, LinearMap.comp_apply,
      map_smul, measuredHermitianBilinear, LinearMap.compr₂_apply, measurementL2,
      smoothResidualToL2, b]
  rw [he, norm_smul]
  have hsz := cNorm_nonneg (fundamentalCell n) 0 (periodicLift (fun x ↦ base.val x i))
  have hlz : 0 ≤ periodicL2Norm (fun x ↦ (G i v).val x ()) := Real.sqrt_nonneg _
  simp only [cSeminorm_eq, l2Seminorm_eq, weightedPeriodicCNorm, weightedPeriodicL2Norm,
    b, Finset.univ_unique, Finset.sum_singleton, one_mul, Real.sqrt_sq hsz,
    Real.sqrt_sq hlz] at hb
  calc
    _ = 2 * ‖measuredHermitianBilinear (fun _ : Unit ↦ (1 : ℝ)) C hC b (G i v)‖ := by
      norm_num
    _ ≤ 2 * (cNorm (fundamentalCell n) 0 (periodicLift C) *
        cNorm (fundamentalCell n) 0 (periodicLift (fun x ↦ base.val x i)) *
          periodicL2Norm (fun x ↦ (G i v).val x ())) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

variable (CG : ι → ℝ)
    (hG : ∀ i v, periodicL2Norm (fun x ↦ (G i v).val x ()) ≤ CG i * ‖v‖)

/-- The actual real component `A_{ν,K}` of `main:prop:canonical`, with the
original raw Hilbert space. The continuous linear map is constructed from
its literal smooth cross response and primitive raw derivative bound. -/
def smoothRawCrossOperator (i : ι) : Raw i →L[ℝ] OutputL2 n :=
  ((smoothResidualToL2 n).comp (smoothRawCrossResponse base C hC G i)).mkContinuous
    (2 * cNorm (fundamentalCell n) 0 (periodicLift C) *
      cNorm (fundamentalCell n) 0 (periodicLift (fun x ↦ base.val x i)) * CG i)
    (fun v ↦ (norm_smoothRawCrossResponse_toL2_le base C hC G i v).trans <| by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hG i v)
        (mul_nonneg (mul_nonneg (by norm_num) (cNorm_nonneg _ _ _)) (cNorm_nonneg _ _ _)))

/-- The component and smooth representative in `main:eq:canonical-identity`
have exactly the SAME L² action. This discharges the `hraw` identification
of `completeCanonicalCorrection_toL2` when using the constructed component. -/
@[simp] theorem smoothRawCrossOperator_apply (i : ι) (v : Raw i) :
    smoothRawCrossOperator base C hC G CG hG i v =
      smoothResidualToL2 n (smoothRawCrossResponse base C hC G i v) := rfl

/-- The component norm in `main:prop:canonical` is derived from the original
raw L² bound. For a raw half-derivative bound `CG i = C₁ * sqrt K`, this is
the individual `sqrt K` estimate, with the SAME fixed uncut background. -/
theorem norm_smoothRawCrossOperator_le (hCG : ∀ i, 0 ≤ CG i) (i : ι) :
    ‖smoothRawCrossOperator base C hC G CG hG i‖ ≤
      2 * cNorm (fundamentalCell n) 0 (periodicLift C) *
        cNorm (fundamentalCell n) 0 (periodicLift (fun x ↦ base.val x i)) * CG i := by
  apply LinearMap.mkContinuous_norm_le
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (cNorm_nonneg _ _ _)) (cNorm_nonneg _ _ _)) (hCG i)

omit G CG hG in
/-- Instantiate the existing complete residual with the components constructed
from the literal raw derivatives (`main:eq:full-recursion`). The smooth
canonical updates and L² normals use exactly these same components, and the
raw-response identification is discharged by construction. Uniform primitive
raw bounds and matching with the sampled kernel remain producer obligations;
no residual, inverse or canonical-input estimate is assumed here. -/
theorem completeResidualRepresentative_toL2_of_rawDerivative [Fintype ι]
    [∀ i, CompleteSpace (Raw i)]
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j : Torus n → ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
    (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ))
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (G : ℕ → ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (CG : ℕ → ι → ℝ)
    (hG : ∀ l i v, periodicL2Norm (fun x ↦ (G l i v).val x ()) ≤ CG l i * ‖v‖)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (K : ℕ → ℝ) (hK : ∀ l, 1 ≤ K l)
    (e : SmoothResidual n) (I : ℕ) :
    let A := fun l ↦ smoothRawCrossOperator base C hC (G l) (CG l) (hG l)
    let D := fun l ↦ smoothCanonicalDerivative (A l) (G l) Q₀
    smoothResidualToL2 n
      (completeResidualRepresentative c hc χmeas χsrc ψ hm hs hψ μ A
        (fun l ↦ smoothRawCrossResponse base C hC (G l)) Q₀ K hK D C hC e I) =
      (MeanRecurrence.run Q₀.toLinearMap
        (fun l ↦ (completeCanonicalNormal c χmeas χsrc ψ μ (A l) (hK l)).toLinearMap)
        D (measuredHermitianBilinear μ C hC) (smoothResidualToL2 n e) I).2 := by
  dsimp only
  apply completeResidualRepresentative_toL2 c hc χmeas χsrc ψ hm hs hψ μ hμ
  intro l i v
  rfl

end JanetCartan.CanonicalChange
