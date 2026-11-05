module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedMask
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.InactiveSource.Sobolev.Coordinates

/-!
# The corrected source tail in the actual Fourier Sobolev space

Transfer the already proved physical-frequency energy to the SAME normalized
complementary operator. The change of variables retains `η=2πξ` and its
Jacobian; the dimension constant is fixed before every source and frequency.
Consumer: the signed source contribution in `app:ch_pairs:prop:pairs-lag-sum`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory FourierTransform
namespace JanetCartan.SignedProductEstimates
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open ResponseTransfer.Complement.InactiveSource JanetCartan.Localization Pseudodifferential
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp V 2 (volume : Measure E)

/-- Physical dilation contracts nonnegative-order energy after its exact
Jacobian is included (`app:ch_osc:prop:osc-source-shell`). -/
private theorem scaled_positive_energy {s : ℝ} (hs : 0 ≤ s) (G : E → V)
    (hm : AEStronglyMeasurable (fun ξ ↦ G ((2*Real.pi) • ξ)) volume)
    (hi : Integrable (fun η ↦ (1 + ‖η‖^2)^s * ‖G η‖^2) volume) :
    Integrable (fun ξ ↦ (1 + ‖ξ‖^2)^s * ‖G ((2*Real.pi) • ξ)‖^2) volume ∧
      fourierWeightedL2Norm volume s (fun ξ ↦ G ((2*Real.pi) • ξ)) ≤
        fourierWeightedL2Norm volume s G := by
  have hi' := hi.comp_smul (by positivity : (2*Real.pi : ℝ) ≠ 0)
  have hw : AEStronglyMeasurable (fun ξ : E ↦ (1 + ‖ξ‖^2)^s *
      ‖G ((2*Real.pi) • ξ)‖^2) volume :=
    ((continuous_const.add (continuous_norm.pow 2)).rpow_const
      (fun ξ : E ↦ Or.inl (show (1 + ‖ξ‖^2 : ℝ) ≠ 0 by positivity))).aestronglyMeasurable.mul (hm.norm.pow 2)
  have hd (ξ : E) : (1 + ‖ξ‖^2)^s * ‖G ((2*Real.pi) • ξ)‖^2 ≤
      (1 + ‖(2*Real.pi) • ξ‖^2)^s * ‖G ((2*Real.pi) • ξ)‖^2 := by
    apply mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (show (0:ℝ) ≤ 1+‖ξ‖^2 by positivity) ?_ hs) (sq_nonneg _)
    have hn : ‖ξ‖ ≤ ‖(2*Real.pi) • ξ‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      nlinarith [Real.two_le_pi, norm_nonneg ξ]
    nlinarith [norm_nonneg ξ, norm_nonneg ((2*Real.pi) • ξ)]
  have hu := hi'.mono' hw (Filter.Eventually.of_forall fun ξ ↦ by
    rw [Real.norm_of_nonneg (by positivity)]
    exact hd ξ)
  refine ⟨hu, ?_⟩
  apply Real.sqrt_le_sqrt
  have hint := integral_mono hu hi' hd
  rw [Measure.integral_comp_smul_of_nonneg volume
    (fun η : E ↦ (1+‖η‖^2)^s * ‖G η‖^2) (2*Real.pi) (hR := by positivity)] at hint
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hint
  apply hint.trans
  have hc : (2*Real.pi : ℝ) ^ (d+1) ≥ 1 := one_le_pow₀ (by nlinarith [Real.two_le_pi])
  exact mul_le_of_le_one_left (integral_nonneg fun η ↦ by positivity)
    ((inv_le_one₀ (by positivity)).mpr hc)

/-- The literal corrected multiplier inherits the physical Fourier energy
of the original datum. Energy integrability is supplied by
`exists_reduced_signed_protected_source_stage_constants`; no decay bound is
assumed here (`app:ch_pairs:prop:pairs-lag-sum`, Step 2). -/
theorem normalizedComplementFourier_sobolev_le_physical_energy
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L₀ : ℝ)
    (g : E → V) (hg : Integrable g volume) (h₂ : MemLp g 2 volume)
    {s : ℝ} (hs : 0 ≤ s) :
    let G := fun η ↦ (normalizedComplementMask f hK L₀ η : ℂ) •
      physicalFourierIntegral volume g (InnerProductSpace.toDual ℝ E η)
    Integrable (fun η ↦ (1+‖η‖^2)^s * ‖G η‖^2) volume →
      MemVectorFourierSobolev s (complementFourierOperator f hK L₀ (h₂.toLp g)) ∧
        vectorFourierSobolevNorm s (complementFourierOperator f hK L₀ (h₂.toLp g)) ≤
          (d+1 : ℝ) * fourierWeightedL2Norm volume s G := by
  intro G henergy
  let u := complementFourierOperator f hK L₀ (h₂.toLp g)
  have he : (𝓕 u : H) =ᵐ[volume] fun ξ ↦ G ((2*Real.pi) • ξ) := by
    filter_upwards [complementFourierOperator_fourier_ae f hK L₀ (h₂.toLp g),
      fourierTransform_coeFn_ae_integral_hilbert (h₂.toLp g) (hg.congr h₂.coeFn_toLp.symm)]
      with ξ hm hf
    rw [hm, hf, Real.fourier_congr_ae h₂.coeFn_toLp]
    dsimp only [G]
    rw [physicalFourierIntegral_eq_fourier, smul_smul,
      inv_mul_cancel₀ (by positivity : (2*Real.pi : ℝ) ≠ 0), one_smul]
  have hm := (Lp.memLp (𝓕 u : H)).aestronglyMeasurable.congr he
  obtain ⟨hi, hn⟩ := scaled_positive_energy hs G hm henergy
  obtain ⟨hmem, hnorm⟩ := vectorSobolev_of_fourier_energy s u _ hm he hi
  refine ⟨hmem, hnorm.trans ?_⟩
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
    mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (d+1))
end JanetCartan.SignedProductEstimates
