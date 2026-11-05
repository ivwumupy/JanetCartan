module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.DensityDiscrepancy.Polarization
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Matrix
public import JanetCartan.Analysis.ContDiff.Norm.Products
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Measured Hermitian products and carrier integration

The integration step of `app:ch_mean_pairs:eq:mean-density-lipschitz` uses
literal measures. Color masks occur only as scalar weights under the integral.
Their partition of unity removes the number of colors from the bound.
`L` is the actual measurement/realization in a fixed output space; its linear
finite-jet bound is explicit, independent of any atom or discrepancy estimate.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.DensityDiscrepancy

variable {P V Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {m n : Type*} [Fintype m] [Fintype n]

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: the measured polarization
of the actual matrix derivative fields. `F` realizes an amplitude as a field. -/
def measuredHermitianBilinear
    (F : V →ₗ[ℝ] (P → Matrix m n ℂ))
    (L : (P → Matrix n n ℝ) →ₗ[ℝ] Y) : V →ₗ[ℝ] V →ₗ[ℝ] Y :=
  LinearMap.mk₂ ℝ (fun u v ↦ L (fun x ↦ CurrentMean.hermitianBilinear (F u x) (F v x)))
    (by intro u v w; simp only [map_add, Pi.add_apply]; rw [← map_add]; rfl)
    (by intro c u v; simp only [map_smul, Pi.smul_apply]; rw [← map_smul]; rfl)
    (by intro u v w; simp only [map_add, Pi.add_apply]; rw [← map_add]; rfl)
    (by intro c u v; simp only [map_smul, Pi.smul_apply]; rw [← map_smul]; rfl)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype n] in
/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: its diagonal is exactly
the measured Hermitian tensor, not a replacement quadratic form. -/
theorem measuredHermitianBilinear_self
    (F : V →ₗ[ℝ] (P → Matrix m n ℂ)) (L : (P → Matrix n n ℝ) →ₗ[ℝ] Y) (v : V) :
    measuredHermitianBilinear F L v v = L (fun x ↦ hermitianTensor (F v x)) := by
  simp only [measuredHermitianBilinear, LinearMap.mk₂_apply, CurrentMean.hermitianBilinear,
    CurrentMean.mixedHermitianTensor_self]

set_option backward.isDefEq.respectTransparency false in
/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: the required measured
bilinear bound follows from Leibniz and the linear measurement bound. The latter
can be a `C^k` to `H^s` realization estimate with its fixed finite shift. -/
theorem norm_measuredHermitianBilinear_le
    (F : V →ₗ[ℝ] (P → Matrix m n ℂ)) (L : (P → Matrix n n ℝ) →ₗ[ℝ] Y)
    {s : Set P} (hs : IsCompact s) (k : ℕ)
    (hF : ∀ v, ContDiff ℝ k (F v)) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ f, ContDiff ℝ k f → ‖L f‖ ≤ C * cNorm s k f) (u v : V) :
    ‖measuredHermitianBilinear F L u v‖ ≤
      (C * (2 : ℝ) ^ k) * cNorm s k (F u) * cNorm s k (F v) := by
  let H := CurrentMean.hermitianContinuousBilinear (m := m) (n := n)
  have hh : ContDiff ℝ k (fun x ↦ H (F u x) (F v x)) :=
    (H.contDiff.comp (hF u)).clm_apply (hF v)
  have hb := cNorm_bilinear_le_of_opNorm_le H hs (hF u) (hF v)
    CurrentMean.norm_hermitianContinuousBilinear_le
  have heq : measuredHermitianBilinear F L u v = L (fun x ↦ H (F u x) (F v x)) := rfl
  rw [heq]
  apply (hL _ hh).trans
  simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hb hC

section Masks

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: a partition-weighted
sum has the same bound as each color. No derivative of a mask occurs. -/
theorem norm_masked_sum_le (mask : ι → ℝ) (f : ι → Y)
    (hm : ∀ i, 0 ≤ mask i) (hpartition : ∑ i, mask i = 1)
    {C : ℝ} (hf : ∀ i, ‖f i‖ ≤ C) : ‖∑ i, mask i • f i‖ ≤ C := by
  calc
    _ ≤ ∑ i, mask i * ‖f i‖ := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hm _)] using
        norm_sum_le Finset.univ (fun i ↦ mask i • f i)
    _ ≤ ∑ i, mask i * C := Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (hf i) (hm i))
    _ = C := by rw [← Finset.sum_mul, hpartition, one_mul]

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: integration preserves
the gain, with only the literal measure's mass. Nonnegative masks with sum one
are automatically at most one, and the bound is independent of their mesh. -/
theorem norm_integral_masked_sum_le (μ : Measure α) [IsFiniteMeasure μ]
    (mask : ι → α → ℝ) (f : ι → α → Y)
    (hm : ∀ i z, 0 ≤ mask i z) (hpartition : ∀ z, ∑ i, mask i z = 1)
    {C : ℝ} (hf : ∀ i z, ‖f i z‖ ≤ C) :
    ‖∫ z, ∑ i, mask i z • f i z ∂μ‖ ≤ C * μ.real Set.univ :=
  norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun z ↦
    norm_masked_sum_le (fun i ↦ mask i z) (fun i ↦ f i z)
      (fun i ↦ hm i z) (hpartition z) (fun i ↦ hf i z))

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: the actual measured,
integrated current-minus-transport Hermitian square. The measure is explicit;
this definition makes no identification of initial Lebesgue and torus data. -/
def integratedHermitianDiscrepancy (μ : Measure α) (mask : ι → α → ℝ)
    (F : V →ₗ[ℝ] (P → Matrix m n ℂ)) (L : (P → Matrix n n ℝ) →ₗ[ℝ] Y)
    (U T : ι → α → A →ₗ[ℝ] V) (a : A) : Y :=
  ∫ z, ∑ i, mask i z • squareDiscrepancy (measuredHermitianBilinear F L) (U i z) (T i z) a ∂μ

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype n] in
/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: unfolding the discrepancy
recovers the literal difference of the two measured Hermitian tensors. An
identification of the second term with the transported density remains a
separate lower-level identity, never an assumption on the discrepancy bound. -/
theorem integratedHermitianDiscrepancy_eq (μ : Measure α) (mask : ι → α → ℝ)
    (F : V →ₗ[ℝ] (P → Matrix m n ℂ)) (L : (P → Matrix n n ℝ) →ₗ[ℝ] Y)
    (U T : ι → α → A →ₗ[ℝ] V) (a : A) :
    integratedHermitianDiscrepancy μ mask F L U T a =
      ∫ z, ∑ i, mask i z •
        (L (fun x ↦ hermitianTensor (F (U i z a) x)) -
         L (fun x ↦ hermitianTensor (F (T i z a) x))) ∂μ := by
  simp only [integratedHermitianDiscrepancy, squareDiscrepancy, measuredHermitianBilinear_self]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype n] in
/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: identify the discrepancy
with the measured current mean minus the transported density. The sole transport
identity is the exact lower-level identification of its integrated square;
no estimate on the discrepancy is assumed. -/
theorem integratedHermitianDiscrepancy_eq_current_sub_transport
    (μ : Measure α) (mask : ι → α → ℝ)
    (F : V →ₗ[ℝ] (P → Matrix m n ℂ)) (L : (P → Matrix n n ℝ) →ₗ[ℝ] Y)
    (U T : ι → α → A →ₗ[ℝ] V) (a : A) (transportDensity : Y)
    (hU : Integrable (fun z ↦ ∑ i, mask i z •
      L (fun x ↦ hermitianTensor (F (U i z a) x))) μ)
    (hT : Integrable (fun z ↦ ∑ i, mask i z •
      L (fun x ↦ hermitianTensor (F (T i z a) x))) μ)
    (htransport : (∫ z, ∑ i, mask i z •
      L (fun x ↦ hermitianTensor (F (T i z a) x)) ∂μ) = transportDensity) :
    integratedHermitianDiscrepancy μ mask F L U T a =
      (∫ z, ∑ i, mask i z • L (fun x ↦ hermitianTensor (F (U i z a) x)) ∂μ) -
        transportDensity := by
  rw [integratedHermitianDiscrepancy_eq]
  simp_rw [smul_sub, Finset.sum_sub_distrib]
  rw [integral_sub hU hT, htransport]

set_option backward.isDefEq.respectTransparency false in
/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: the integrated quadratic
Lipschitz estimate derived from the actual linear amplitude operator bounds.
The finite input shift is carried by `p`; the output order by `L` and `k`.
Only integrability, not a discrepancy estimate, is assumed for the integral. -/
theorem norm_integratedHermitianDiscrepancy_sub_le
    (μ : Measure α) [IsFiniteMeasure μ] (mask : ι → α → ℝ)
    (hm : ∀ i z, 0 ≤ mask i z) (hpartition : ∀ z, ∑ i, mask i z = 1)
    (F : V →ₗ[ℝ] (P → Matrix m n ℂ)) (L : (P → Matrix n n ℝ) →ₗ[ℝ] Y)
    (U T : ι → α → A →ₗ[ℝ] V) (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    {s : Set P} (hs : IsCompact s) (k : ℕ) (hF : ∀ v, ContDiff ℝ k (F v))
    {C K δ : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hL : ∀ f, ContDiff ℝ k f → ‖L f‖ ≤ K * cNorm s k f)
    (hU : ∀ i z a, cNorm s k (F (U i z a)) ≤ C * p a)
    (hT : ∀ i z a, cNorm s k (F (T i z a)) ≤ C * p a)
    (hD : ∀ i z a, cNorm s k (F ((U i z - T i z) a)) ≤ δ * C * p a)
    (a b : A)
    (ha : Integrable (fun z ↦ ∑ i, mask i z •
      squareDiscrepancy (measuredHermitianBilinear F L) (U i z) (T i z) a) μ)
    (hb : Integrable (fun z ↦ ∑ i, mask i z •
      squareDiscrepancy (measuredHermitianBilinear F L) (U i z) (T i z) b) μ) :
    ‖integratedHermitianDiscrepancy μ mask F L U T a -
      integratedHermitianDiscrepancy μ mask F L U T b‖ ≤
      (2 * (K * 2 ^ k) * C ^ 2 * δ * (p a + p b) * p (a - b)) * μ.real Set.univ := by
  unfold integratedHermitianDiscrepancy
  rw [← integral_sub ha hb]
  simp_rw [← Finset.sum_sub_distrib, ← smul_sub]
  apply norm_integral_masked_sum_le μ mask _ hm hpartition
  intro i z
  exact squareDiscrepancy_sub_le (measuredHermitianBilinear F L) (U i z) (T i z)
    p (fun v ↦ cNorm s k (F v)) (normSeminorm ℝ Y)
    (mul_nonneg hK (by positivity)) hC hδ hp (fun v ↦ cNorm_nonneg _ _ _)
    (norm_measuredHermitianBilinear_le F L hs k hF hK hL)
    (hU i z) (hT i z) (hD i z) a b

set_option backward.isDefEq.respectTransparency false in
/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: the initial-discrepancy
bound, proved from the same operator estimates. Apply with the unperturbed
amplitude `r_F` to supply the preparation theorem's `hinit`. -/
theorem norm_integratedHermitianDiscrepancy_le
    (μ : Measure α) [IsFiniteMeasure μ] (mask : ι → α → ℝ)
    (hm : ∀ i z, 0 ≤ mask i z) (hpartition : ∀ z, ∑ i, mask i z = 1)
    (F : V →ₗ[ℝ] (P → Matrix m n ℂ)) (L : (P → Matrix n n ℝ) →ₗ[ℝ] Y)
    (U T : ι → α → A →ₗ[ℝ] V) (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    {s : Set P} (hs : IsCompact s) (k : ℕ) (hF : ∀ v, ContDiff ℝ k (F v))
    {C K δ : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hL : ∀ f, ContDiff ℝ k f → ‖L f‖ ≤ K * cNorm s k f)
    (hU : ∀ i z a, cNorm s k (F (U i z a)) ≤ C * p a)
    (hT : ∀ i z a, cNorm s k (F (T i z a)) ≤ C * p a)
    (hD : ∀ i z a, cNorm s k (F ((U i z - T i z) a)) ≤ δ * C * p a) (a : A) :
    ‖integratedHermitianDiscrepancy μ mask F L U T a‖ ≤
      (2 * (K * 2 ^ k) * C ^ 2 * δ * p a ^ 2) * μ.real Set.univ := by
  apply norm_integral_masked_sum_le μ mask _ hm hpartition
  intro i z
  exact squareDiscrepancy_le (measuredHermitianBilinear F L) (U i z) (T i z)
    p (fun v ↦ cNorm s k (F v)) (normSeminorm ℝ Y)
    (mul_nonneg hK (by positivity)) hC hδ hp (fun v ↦ cNorm_nonneg _ _ _)
    (norm_measuredHermitianBilinear_le F L hs k hF hK hL)
    (hU i z) (hT i z) (hD i z) a

end Masks
end JanetCartan.DensityDiscrepancy
