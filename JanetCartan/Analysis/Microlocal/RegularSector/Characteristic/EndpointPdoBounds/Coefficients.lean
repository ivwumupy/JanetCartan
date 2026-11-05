module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds.Endpoint

/-!
# The original physical time coefficient in the endpoint budget

The matrix multiplying `W₁(t,t)` is the same coefficient selected by
`ResidualCoordinates.coefficient`. It is a fixed linear function of `Q`
after the fixed coordinate permutation, so it costs no derivative reserve.
Consumer: the original-coefficient estimate for the upper endpoint in
`paper-v2.tex`, `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
open ResidualCoordinates ActualCarriers NullTransport.AmplitudeTame
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "QValue" => Fin (d + 1) → MetricTensor (d + 1)
local notation "Mat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ

/-- The actual complex time coefficient is a fixed linear extraction from
the original real stress pencil (`energy-complete-residual`). -/
def timeCoefficientLinear (i : Fin (d + 1)) : QValue →L[ℝ] Mat :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Q a b ↦ (Q a b i : ℂ)
      map_add' := by intro Q V; ext a b; simp
      map_smul' := by intro t Q; ext a b; simp [Complex.real_smul] }

/-- Identification with the SAME physical coefficient from the cancellation
identity; no auxiliary extension is substituted (`energy-complete-residual`). -/
theorem timeCoefficientLinear_eq (i : Fin (d + 1)) (Q : E → QValue) (x : E) :
    timeCoefficientLinear i (Q (physicalCoordinates i x)) =
      (coefficient i Q x 0).map Complex.ofReal := by
  ext a b
  simp [coefficient, pencil, EuclideanSpace.single, timeCoefficientLinear]

/-- A fixed dimension/coordinate cost, independent of the varying `Q`.
Source: the endpoint term of `energy-complete-residual`. -/
def timeCoefficientCost (i : Fin (d + 1)) (m : ℕ) : ℝ :=
  max 1 ‖timeCoefficientLinear i‖ * linearNormCost (physicalCoordinates i).toContinuousLinearMap m

/-- Positivity of the fixed coefficient cost (`energy-complete-residual`). -/
theorem timeCoefficientCost_pos (i : Fin (d + 1)) (m : ℕ) : 0 < timeCoefficientCost i m :=
  mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (linearNormCost_pos _ _)

/-- The literal complex time coefficient has the original `Q` budget at the
SAME derivative order. The only geometric hypothesis is the physical image
inclusion, to be instantiated on the parent's selected chart.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem cNorm_timeCoefficient_le
    (i : Fin (d + 1)) {K KQ Ω : Set E} (hK : IsCompact K) (hKQ : IsCompact KQ)
    (hΩ : IsOpen Ω) (hKΩ : KQ ⊆ Ω)
    (hmap : MapsTo (physicalCoordinates i) K KQ)
    {Q : E → QValue} (hQ : ContDiffOn ℝ ∞ Q Ω) (m : ℕ) :
    cNorm K m (fun x ↦ (coefficient i Q x 0).map Complex.ofReal) ≤
      timeCoefficientCost i m * cNorm KQ m Q := by
  let f : E → QValue := Q ∘ physicalCoordinates i
  let L := timeCoefficientLinear i
  have hf : ∀ x ∈ K, ContDiffAt ℝ m f x := by
    intro x hx
    exact ((hQ.contDiffAt (hΩ.mem_nhds (hKΩ (hmap hx)))).comp x
      (physicalCoordinates i).contDiff.contDiffAt).of_le (by simp)
  have hpost : cNorm K m (L ∘ f) ≤ ‖L‖ * cNorm K m f := by
    simp only [cNorm, Finset.mul_sum]
    apply cNorm_le_sum_of_bounds
      (fun j _ ↦ mul_nonneg (norm_nonneg _) (sSup_norm_iteratedFDeriv_nonneg K j f))
    intro j hj x hx
    exact (L.norm_iteratedFDeriv_comp_left (hf x hx) (by exact_mod_cast hj)).trans
      (mul_le_mul_of_nonneg_left
        (le_csSup (bddAbove_norm_iteratedFDeriv_of_contDiffAt hK hf hj)
          (mem_image_of_mem _ hx)) (norm_nonneg _))
  have hpre := cNorm_comp_linear_le (physicalCoordinates i).toContinuousLinearMap
    hKQ hΩ hKΩ hQ hmap m
  have he : (L ∘ f) = (fun x ↦ (coefficient i Q x 0).map Complex.ofReal) := by
    funext x
    exact timeCoefficientLinear_eq i Q x
  rw [he] at hpost
  calc
    _ ≤ ‖L‖ * cNorm K m f := hpost
    _ ≤ max 1 ‖L‖ * (linearNormCost (physicalCoordinates i).toContinuousLinearMap m * cNorm KQ m Q) :=
      mul_le_mul (le_max_right _ _) hpre (cNorm_nonneg _ _ _) (by positivity)
    _ = _ := by simp only [timeCoefficientCost, L, mul_assoc]

/-- The actual coefficient is smooth on the inverse image of the original
physical chart; the output mask localizes this SAME coefficient globally.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem contDiffOn_timeCoefficient
    (i : Fin (d + 1)) {Ω : Set E} {Q : E → QValue} (hQ : ContDiffOn ℝ ∞ Q Ω) :
    ContDiffOn ℝ ∞ (fun x ↦ (coefficient i Q x 0).map Complex.ofReal)
      ((physicalCoordinates i) ⁻¹' Ω) := by
  have hp : ContDiffOn ℝ ∞ (Q ∘ physicalCoordinates i) ((physicalCoordinates i) ⁻¹' Ω) :=
    hQ.comp (physicalCoordinates i).contDiff.contDiffOn (fun _ hx ↦ hx)
  have h := (timeCoefficientLinear i).contDiff.comp_contDiffOn hp
  have he : (timeCoefficientLinear i ∘ (Q ∘ physicalCoordinates i)) =
      (fun x ↦ (coefficient i Q x 0).map Complex.ofReal) := by
    funext x
    exact timeCoefficientLinear_eq i Q x
  rw [he] at h
  exact h

end JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
