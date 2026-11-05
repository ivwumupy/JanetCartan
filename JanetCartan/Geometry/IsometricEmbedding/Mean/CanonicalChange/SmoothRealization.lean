module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.CompleteResidual

/-!
# Smooth realization of a fixed canonical derivative row

For `app:ch_mean_pairs:defn:mean-canonical`, apply each component's real
adjoint and the SAME `Q₀` before its supplied smooth raw derivative map.
Construct the corresponding smooth cross response using the original
background and measurement. Its exact weighted identity is proved before
any normal comparison or analytic canonical estimate is used.

The corrected-atom producer must supply the smooth raw maps and identify
their measured L² actions with the original component operators. No new
operator family, raw space, sample, or successful-estimate record is selected.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalChange

open CurrentMean CurrentMean.SmoothPeriodicFamily ContinuumRow

variable {n : ℕ} {ι m : Type*} [Fintype ι] [Fintype m]
    {Raw : ι → Type*} [∀ i, NormedAddCommGroup (Raw i)]
    [∀ i, InnerProductSpace ℝ (Raw i)] [∀ i, CompleteSpace (Raw i)]

/-- The literal component response `C[2 sym Re(Bᵢ* Gᵢ v)]` in
`main:eq:canonical-identity`, as a smooth representative. The original
zero-atom background is fixed independently of the raw band. -/
def smoothRawCrossResponse
    (base : SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ))
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (i : ι) : Raw i →ₗ[ℝ] SmoothResidual n :=
  (2 : ℝ) • (measurementFamily C hC).comp
    ((tensorBilinear (fun _ : Unit ↦ (1 : ℝ))
      ⟨fun x _ ↦ base.val x i, fun _ ↦ smooth base i⟩).comp (G i))

omit [Fintype ι] [∀ i, CompleteSpace (Raw i)] in
/-- Evaluation retains the exact real polarization and factor two of
`main:eq:canonical-identity`. -/
theorem smoothRawCrossResponse_apply
    (base : SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ))
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (i : ι) (v : Raw i) (x : Torus n) :
    (smoothRawCrossResponse base C hC G i v).val x () =
      C x ((2 : ℝ) • mixedHermitianTensor (base.val x i) ((G i v).val x ())) := by
  simp [smoothRawCrossResponse, measurementFamily, tensorBilinear,
    weightedHermitianBilinear, hermitianBilinear, map_smul]

/-- The SAME smooth canonical derivative family of
`app:ch_mean_pairs:eq:mean-current-canonical`. Raw adjoints use the original
Hilbert spaces and are applied before physical realization, without inverse
sample weights. -/
def smoothCanonicalDerivative
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) :
    OutputL2 n →ₗ[ℝ] SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ) where
  toFun e := ⟨fun x i ↦ (G i ((A i).adjoint (Q₀ e))).val x (),
    fun i ↦ smooth (G i ((A i).adjoint (Q₀ e))) ()⟩
  map_add' e f := by
    apply Subtype.ext
    funext x i
    simp only [map_add, Submodule.coe_add, Pi.add_apply]
  map_smul' a e := by
    apply Subtype.ext
    funext x i
    simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]

/-- The constructed smooth canonical family realizes the complete weighted
linear cross response (`main:eq:canonical-identity`). This identity uses the
actual maps just defined, rather than assuming a one-step response formula. -/
theorem smoothCanonicalResponse_eq_measured_cross
    (μ : ι → ℝ) (base : SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ))
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (e : OutputL2 n) :
    smoothCanonicalResponse μ A (smoothRawCrossResponse base C hC G) Q₀ e =
      measurementFamily C hC
        ((2 : ℝ) • tensorBilinear μ base (smoothCanonicalDerivative A G Q₀ e)) := by
  apply Subtype.ext
  funext x u
  cases u
  simp only [smoothCanonicalResponse, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, ContinuousLinearMap.coe_coe, Submodule.coe_sum,
    Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smoothRawCrossResponse_apply]
  change (∑ i, μ i • C x ((2 : ℝ) • mixedHermitianTensor (base.val x i)
      ((G i ((A i).adjoint (Q₀ e))).val x ()))) =
    C x ((2 : ℝ) • ∑ i, μ i • mixedHermitianTensor (base.val x i)
      ((G i ((A i).adjoint (Q₀ e))).val x ()))
  simp only [map_smul, map_sum, Finset.smul_sum, smul_comm (2 : ℝ)]

end JanetCartan.CanonicalChange
