module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.SourceEndpoint.Source
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.SourceEndpoint.RetainedProfiles

/-!
# The coefficient and product in the selected endpoint

These are the remaining product factors of the literal endpoint in
`app:ch_regular_base:eq:energy-complete-residual`. The coefficient profile
uses the original coefficient ball, with no additional derivative reserve.
The source factor retains all masks at the fixed doubled threshold.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius Topology
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FinitePdo RegularSector.FiniteAlgebraic
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.EndpointPdoBounds RegularSector.Characteristic.EvolutionIntegral
open FiniteChain.Retarded.KernelDecay
open ResidualLocalization
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Mat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ

/-- Pointwise Leibniz convolution, allowing the original coefficient to be
smooth only on its physical domain. Consumer: the full endpoint PDO product
in `app:ch_regular:eq:high-amplitude`. -/
theorem norm_iteratedFDeriv_endpoint_product_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : V → Mat} {v : V} (hf : ContDiffAt ℝ ∞ f v) (hg : ContDiffAt ℝ ∞ g v)
    {A B : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) {S T L : ℝ}
    (hS : 0 ≤ S) (hL : 0 ≤ L)
    (ha : ∀ j, ‖iteratedFDeriv ℝ j f v‖ ≤ S * A j * L ^ j)
    (hb : ∀ j, ‖iteratedFDeriv ℝ j g v‖ ≤ T * B j * L ^ j) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun w ↦ f w * g w) v‖ ≤
      (S * T) * derivativeConvolution A B n * L ^ n := by
  obtain ⟨U, hUv, hUf⟩ := hf.contDiffOn (m := n) (by simp) (by simp)
  obtain ⟨U', hU'v, hUg⟩ := hg.contDiffOn (m := n) (by simp) (by simp)
  obtain ⟨O, hOU, hO, hv⟩ := _root_.mem_nhds_iff.mp (Filter.inter_mem hUv hU'v)
  have h := norm_iteratedFDerivWithin_mul_le (hUf.mono (hOU.trans inter_subset_left))
    (hUg.mono (hOU.trans inter_subset_right)) hO.uniqueDiffOn hv (n := n) le_rfl
  simp only [iteratedFDerivWithin_of_isOpen _ hO hv] at h
  apply h.trans
  simp only [derivativeConvolution, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  calc
    _ ≤ (n.choose j : ℝ) * (S * A j * L ^ j) * (T * B (n-j) * L ^ (n-j)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (ha j) (Nat.cast_nonneg _)) (hb _)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (mul_nonneg hS (hA j)) (pow_nonneg hL _)))
    _ = (S*T) * ((n.choose j : ℝ) * A j * B (n-j)) * (L^j * L^(n-j)) := by ring
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le hjn]

/-- The full forward endpoint is exactly the masked source factor times the
original time coefficient and the SAME endpoint amplitude. This identity
preserves the source cutoff at `2 * threshold` (`energy-complete-residual`). -/
theorem selectedEndpointAmplitude_eq_source_product
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {threshold : ℝ} (ht : f.radialThreshold ≤ threshold)
    {output : E → ℝ} (hout : tsupport output ⊆ ball x f.physicalRadius)
    (Q : E → Fin (d+1) → MetricTensor (d+1))
    (W : EvolutionIntegral.TwoTimeAmplitude d (d+1)) (y z ξ : E) :
    orientedMaskedPDOAmplitude false (endpointOutputMask f p output) (chartInputMask f p)
      (selectedEndpointSymbol f p threshold Q W) y z ξ =
      (orientedMaskedPDOAmplitude false (endpointOutputMask f p output) (chartInputMask f p)
        (selectedSourceSymbol f p (2 * threshold)) y z ξ *
        (coefficient (f.chart p).index Q y 0).map Complex.ofReal) *
          W (y 0) (y 0) (spatialPart y) (spatialPart ξ) := by
  rw [selectedSourceAmplitude_eq_multiplier_masks f p ht hout]
  simp only [orientedMaskedPDOAmplitude, Bool.false_eq_true, ↓reduceIte, selectedEndpointSymbol,
    Matrix.smul_mul, Matrix.one_mul]
  exact smul_comm _ _ _

/-- Original coefficient jets after any contracting physical projection.
The projections to `v.1.1` and `z.1` give the joint and physical inputs of
`CompleteFactor`. No PDO grade is assumed (`app:ch_regular:eq:high-amplitude`). -/
theorem endpointCoefficient_jet_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (hQ : ContDiffOn ℝ ∞ Q Ω)
    (P : V →L[ℝ] E) (hP : ‖P‖ ≤ 1) {v : V}
    (hv : P v ∈ closedBall ((physicalCoordinates (f.chart p).index).symm x)
      (2 * f.physicalRadius)) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun w ↦ (coefficient (f.chart p).index Q (P w) 0).map Complex.ofReal) v‖ ≤
      timeCoefficientCost (f.chart p).index m * cNorm (closedBall x RQ) m Q := by
  let U := (physicalCoordinates (f.chart p).index) ⁻¹' Ω
  let B := closedBall ((physicalCoordinates (f.chart p).index).symm x) (2*f.physicalRadius)
  let q := fun y ↦ (coefficient (f.chart p).index Q y 0).map Complex.ofReal
  have hU : IsOpen U := hΩ.preimage (physicalCoordinates (f.chart p).index).continuous
  have hq : ContDiffOn ℝ ∞ q U := contDiffOn_timeCoefficient _ hQ
  have hBU : B ⊆ U := fun y hy ↦ hball (selectedEndpoint_physical_ball_mapsTo f p hy)
  have hb : ‖iteratedFDeriv ℝ m q (P v)‖ ≤
      timeCoefficientCost (f.chart p).index m * cNorm (closedBall x RQ) m Q :=
    (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
      (fun y hy ↦ (hq.contDiffAt (hU.mem_nhds (hBU hy))).of_le (by simp)) hv le_rfl).trans
        (cNorm_timeCoefficient_le _ (isCompact_closedBall _ _) (isCompact_closedBall _ _)
          hΩ hball (selectedEndpoint_physical_ball_mapsTo f p) hQ m)
  exact (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le P hU hq (hBU hv) m).trans
    ((mul_le_mul hb (pow_le_one₀ (norm_nonneg _) hP) (by positivity)
      (mul_nonneg (timeCoefficientCost_pos _ _).le (cNorm_nonneg _ _ _))).trans_eq (mul_one _))

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
