module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.NormalizedTransfer.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.SpatialRealization.Assembly

/-!
# Literal spatial interpretation of normalized expressions

The coefficient extension is identified only on the original closed amplitude
support. Multiplication then gives a global identity of the full products.
Differentiating that identity retains every inverse-coefficient derivative and
every mask in `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ResponseTransfer.NormalizedTransfer
open FourierIntegral FullAmplitudePrimitiveBudget.Local
open IsometricEmbedding.Response.NearCarrier NearCarrierSymbol
variable {n r : ℕ} {ι : Type*}
local notation "E" => Euclidean n

/-- Physical recovery commutes with output differentiation, with frequency
fixed (`app:ch_response:eq:direct-envelope-profile`). -/
theorem physical_outputDerivative (ρ : ℝ) {b : Point n → ℂ}
    (hb : ContDiff ℝ ∞ b) (i : Fin n) (x y δ : E) :
    scalarPhysicalAmplitude (r := r) ρ (fun z ↦ fderiv ℝ b z (outputDirection i)) x y δ =
      partialDeriv (fun z ↦ scalarPhysicalAmplitude ρ b z y δ) x i := by
  have hd : DifferentiableAt ℝ b ((x, y), ρ⁻¹ • δ) :=
    (hb.differentiable (by simp)).differentiableAt
  have hs : DifferentiableAt ℝ (fun z : E ↦ b ((z, y), ρ⁻¹ • δ)) x := hd.comp x
    ((differentiableAt_id.prodMk (differentiableAt_const y)).prodMk
      (differentiableAt_const (ρ⁻¹ • δ)))
  have h := (ContinuousLinearMap.hasFDerivAt (F := Matrix (Fin r) (Fin r) ℂ) scalarMatrixMap).comp x hs.hasFDerivAt
  change scalarMatrixMap (fderiv ℝ b ((x, y), ρ⁻¹ • δ) (outputDirection i)) =
    fderiv ℝ (F := Matrix (Fin r) (Fin r) ℂ) (fun z ↦ scalarMatrixMap (b ((z, y), ρ⁻¹ • δ))) x (EuclideanSpace.single i 1)
  rw [fderiv_outputDirection hd]
  exact (congrArg (fun L : E →L[ℝ] Matrix (Fin r) (Fin r) ℂ ↦
    L (EuclideanSpace.single i 1)) (h.fderiv (F := Matrix (Fin r) (Fin r) ℂ))).symm

/-- Physical recovery commutes with source differentiation of the complete
coefficient-amplitude product (`app:ch_response:eq:direct-envelope-profile`). -/
theorem physical_sourceDerivative (ρ : ℝ) {b : Point n → ℂ}
    (hb : ContDiff ℝ ∞ b) (j : Fin n) (x y δ : E) :
    scalarPhysicalAmplitude (r := r) ρ (fun z ↦ fderiv ℝ b z (sourceDirection j)) x y δ =
      partialDeriv (fun z ↦ scalarPhysicalAmplitude ρ b x z δ) y j := by
  have hd : DifferentiableAt ℝ b ((x, y), ρ⁻¹ • δ) :=
    (hb.differentiable (by simp)).differentiableAt
  have hs : DifferentiableAt ℝ (fun z : E ↦ b ((x, z), ρ⁻¹ • δ)) y := hd.comp y
    (((differentiableAt_const x).prodMk differentiableAt_id).prodMk
      (differentiableAt_const (ρ⁻¹ • δ)))
  have h := (ContinuousLinearMap.hasFDerivAt (F := Matrix (Fin r) (Fin r) ℂ) scalarMatrixMap).comp y hs.hasFDerivAt
  change scalarMatrixMap (fderiv ℝ b ((x, y), ρ⁻¹ • δ) (sourceDirection j)) =
    fderiv ℝ (F := Matrix (Fin r) (Fin r) ℂ) (fun z ↦ scalarMatrixMap (b ((x, z), ρ⁻¹ • δ))) y (EuclideanSpace.single j 1)
  rw [fderiv_sourceDirection hd]
  exact (congrArg (fun L : E →L[ℝ] Matrix (Fin r) (Fin r) ℂ ↦
    L (EuclideanSpace.single j 1)) (h.fderiv (F := Matrix (Fin r) (Fin r) ℂ))).symm

/-- Agreement of a smooth coefficient extension on the original amplitude
support identifies the entire physical product globally. The actual coefficient
may be defined only by its formula on the buffered selector neighborhood.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem physical_product_of_eqOn_support {ρ : ℝ} (hρ : ρ ≠ 0)
    (b q : Point n → ℂ) (Q : E → E → E → ℂ)
    (hq : ∀ z ∈ tsupport b, q z = Q z.1.1 z.1.2 (ρ • z.2)) :
    scalarPhysicalAmplitude (r := r) ρ (fun z ↦ q z * b z) =
      fun x y δ ↦ Q x y δ • scalarPhysicalAmplitude ρ b x y δ := by
  funext x y δ
  ext i j
  simp only [scalarPhysicalAmplitude_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hz : ((x, y), ρ⁻¹ • δ) ∈ tsupport b
  · rw [hq _ hz]
    simp [smul_smul, hρ]
  · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]

/-- The normalized forward datum branch is the published literal amplitude.
The coefficient is `B(x,ρ ε)` on the support, including selector shoulders.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem physical_forwardDatum {ρ : ℝ} (hρ : ρ ≠ 0)
    (a : ι → Point n → ℂ) (b : AmplitudeExpression (Point n) ℂ ι)
    (B : E → E → Matrix (Fin n) (Fin n) ℝ) (idx : Fin n → Fin n → ι)
    (i j : Fin n)
    (hB : ∀ z ∈ tsupport (b.evaluate a), a (idx i j) z = (B z.1.1 (ρ • z.2) i j : ℂ)) :
    scalarPhysicalAmplitude (r := r) ρ
        ((b.coefficientProduct (ContinuousLinearMap.mul ℝ ℂ) (idx i j)).evaluate a) =
      forwardDatumAmplitude B (scalarPhysicalAmplitude ρ (b.evaluate a)) i j :=
  physical_product_of_eqOn_support hρ _ _ (fun x _ δ ↦ (B x δ i j : ℂ)) hB

/-- The normalized reverse datum branch has the inverse coefficient at the
source position. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem physical_reverseDatum {ρ : ℝ} (hρ : ρ ≠ 0)
    (a : ι → Point n → ℂ) (b : AmplitudeExpression (Point n) ℂ ι)
    (J : E → E → Matrix (Fin n) (Fin n) ℝ) (idx : Fin n → Fin n → ι)
    (i j : Fin n)
    (hJ : ∀ z ∈ tsupport (b.evaluate a), a (idx i j) z = (J z.1.2 (ρ • z.2) i j : ℂ)) :
    scalarPhysicalAmplitude (r := r) ρ
        ((b.coefficientProduct (ContinuousLinearMap.mul ℝ ℂ) (idx i j)).evaluate a) =
      ReverseDerivative.datumAmplitude J (scalarPhysicalAmplitude ρ (b.evaluate a)) i j :=
  physical_product_of_eqOn_support hρ _ _ (fun _ y δ ↦ (J y δ i j : ℂ)) hJ

/-- The full spatial remainder is recovered as output derivative plus the
source divergences of the physical products. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem physical_spatialSourceTerms (ρ : ℝ)
    (a : ι → Point n → ℂ) (b : AmplitudeExpression (Point n) ℂ ι)
    (hb : ContDiff ℝ ∞ (b.evaluate a)) (i : Fin n) (idx : Fin n → ι)
    (ha : ∀ j, ContDiff ℝ ∞ (a (idx j))) (x y δ : E) :
    scalarPhysicalAmplitude (r := r) ρ
        ((b.divergenceTransfer (outputDirection i) (spatialSourceTerms idx)).evaluate a) x y δ =
      partialDeriv (fun z ↦ scalarPhysicalAmplitude ρ (b.evaluate a) z y δ) x i +
        ∑ j, partialDeriv (fun z ↦ scalarPhysicalAmplitude ρ
          (fun w ↦ a (idx j) w * b.evaluate a w) x z δ) y j := by
  rw [← physical_outputDerivative ρ hb]
  simp_rw [← physical_sourceDerivative ρ ((ha _).mul hb)]
  ext k l
  simp only [scalarPhysicalAmplitude_apply, Matrix.add_apply, Matrix.sum_apply]
  exact evaluate_spatialSourceTerms a b i idx _

/-- Literal reverse remainder, with the derivative of `J = B⁻¹` retained
inside each source product. Equality of the extension is needed only on the
closed amplitude support. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem physical_reverseRemainder {ρ : ℝ} (hρ : ρ ≠ 0)
    (a : ι → Point n → ℂ) (b : AmplitudeExpression (Point n) ℂ ι)
    (hb : ContDiff ℝ ∞ (b.evaluate a))
    (J : E → E → Matrix (Fin n) (Fin n) ℝ) (idx : Fin n → Fin n → ι)
    (i : Fin n) (ha : ∀ j, ContDiff ℝ ∞ (a (idx i j)))
    (hJ : ∀ j z, z ∈ tsupport (b.evaluate a) →
      a (idx i j) z = (J z.1.2 (ρ • z.2) i j : ℂ)) :
    scalarPhysicalAmplitude (r := r) ρ
        ((b.divergenceTransfer (outputDirection i) (spatialSourceTerms (idx i))).evaluate a) =
      ReverseDerivative.remainderAmplitude J (scalarPhysicalAmplitude ρ (b.evaluate a)) i := by
  funext x y δ
  rw [physical_spatialSourceTerms ρ a b hb i (idx i) ha]
  unfold ReverseDerivative.remainderAmplitude
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have he := physical_reverseDatum (r := r) hρ a b J idx i j (hJ j)
  change partialDeriv (fun z ↦ scalarPhysicalAmplitude ρ
    ((b.coefficientProduct (ContinuousLinearMap.mul ℝ ℂ) (idx i j)).evaluate a) x z δ) y j = _
  rw [he]

/-- Literal forward remainder: the coefficient is independent of the source
position, so its source divergence reduces to `B ∂source A`. Every derivative
of the selected amplitude remains. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem physical_forwardRemainder {ρ : ℝ} (hρ : ρ ≠ 0)
    (a : ι → Point n → ℂ) (b : AmplitudeExpression (Point n) ℂ ι)
    (hb : ContDiff ℝ ∞ (b.evaluate a))
    (B : E → E → Matrix (Fin n) (Fin n) ℝ) (idx : Fin n → Fin n → ι)
    (i : Fin n) (ha : ∀ j, ContDiff ℝ ∞ (a (idx i j)))
    (hB : ∀ j z, z ∈ tsupport (b.evaluate a) →
      a (idx i j) z = (B z.1.1 (ρ • z.2) i j : ℂ)) :
    scalarPhysicalAmplitude (r := r) ρ
        ((b.divergenceTransfer (outputDirection i) (spatialSourceTerms (idx i))).evaluate a) =
      forwardRemainderAmplitude B (scalarPhysicalAmplitude ρ (b.evaluate a)) i := by
  funext x y δ
  rw [physical_spatialSourceTerms ρ a b hb i (idx i) ha]
  unfold forwardRemainderAmplitude
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have he := physical_forwardDatum (r := r) hρ a b B idx i j (hB j)
  change partialDeriv (fun z ↦ scalarPhysicalAmplitude ρ
    ((b.coefficientProduct (ContinuousLinearMap.mul ℝ ℂ) (idx i j)).evaluate a) x z δ) y j = _
  rw [he]
  have hd : Differentiable ℝ (fun z ↦ scalarPhysicalAmplitude (r := r) ρ
      (b.evaluate a) x z δ) := ((contDiff_scalarPhysicalAmplitude (r := r) ρ hb).comp
    ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)).differentiable (by simp)
  simp only [forwardDatumAmplitude, partialDeriv,
    fderiv_fun_const_smul (hd y), smul_apply]

end JanetCartan.ResponseTransfer.NormalizedTransfer
