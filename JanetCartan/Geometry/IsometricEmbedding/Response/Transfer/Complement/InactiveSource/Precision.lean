module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.InactiveSource.EnvelopeJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.InactiveSource.Sobolev
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Scale
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.Assembly

/-!
# Arbitrary precision for inactive Fourier source factors

The inactive-source application of `app:ch_osc:prop:osc-source-shell` in
`app:ch_response:thm:response-literal-transfer`. The actual envelope Sobolev
profile supplies every pointwise jet; the actual multiplier supplies membership
and the spectral estimate. The fixed loss is `d + 1`, independent of the
integration order. The existing finite-Neumann scale inequality absorbs it.

The index may include frequency, datum, phase, mask and compact parameters.
All geometric and profile bounds are uniform before that index. No parameter
derivative identity is asserted. The full nonzero mask must satisfy the gap,
including its bounded-frequency pieces and all angular/radial shoulders.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff
open JanetCartan.Pseudodifferential JanetCartan.ArbitraryAccuracy

namespace JanetCartan.ResponseTransfer.Complement.InactiveSource

variable {d r : ℕ} {ι : Type*}

variable {U S : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
  (m : ι → BoundedMask d) (φ : ι → (EuclideanSpace ℝ (Fin d)) → ℝ) (f : ι → (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℂ (Fin r)))
  (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) U) (hf : ∀ i, ContDiff ℝ ∞ (f i))
  (hsupport : ∀ i, tsupport (f i) ⊆ S)
  (hfLp : ∀ i, MemLp (f i) 2 volume)
  (A K ρ : ι → ℝ) (c G M ν : ℝ) (P C : ℕ → ℝ)
  (hc : 0 < c) (hν : ν ∈ Set.Ioo (0 : ℝ) 1)
  (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 1 ≤ K i) (hρ : ∀ i, 1 ≤ ρ i)
  (hscale : ∀ i, K i ≤ (ρ i) ^ (1 - ν))
  (hmask : ∀ i, (m i).bound ≤ M)
  (hgap : ∀ i η, (m i).symbol η ≠ 0 → ∀ x ∈ U,
    c * (ρ i + ‖η‖) ≤ ‖ρ i • fderiv ℝ (φ i) x - InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) η‖)
  (hupper : ∀ i x, x ∈ U → ‖fderiv ℝ (φ i) x‖ ≤ G)
  (hP : ∀ j, 0 ≤ P j)
  (hphase : ∀ i x, x ∈ tsupport (f i) → ∀ j, 1 ≤ j →
    ‖iteratedFDeriv ℝ (j + 1) (φ i) x‖ ≤ P j * K i ^ j)
  (hmem : ∀ i (p : ℕ), MemVectorFourierSobolev (p : ℝ) ((hfLp i).toLp (f i)))
  (hprofile : ∀ i (p : ℕ), vectorFourierSobolevNorm (p : ℝ) ((hfLp i).toLp (f i)) ≤
    C p * A i * K i ^ p)

include hc hν hA hK hρ hscale hmask hgap hupper hP hphase hmem hprofile

/-- Uniform arbitrary precision for the actual inactive multiplier applied to
the original compactly supported carrier in
`app:ch_response:thm:response-literal-transfer`. The input is the all-order
Sobolev profile on its genuine Euclidean L² class. No pointwise envelope bound,
spectral tail, or desired output estimate is an input. The proof chooses its
constant before the family index, so all supplied parameter labels are uniform.
The explicit `hfLp` may be obtained from `(hf i).continuous` and `hsupport i`.
-/
theorem masked_carrierSource_arbitrary_precision (s : ℝ) (hs : 0 ≤ s) :
    ∀ Q : ℝ, ∃ D : ℝ, 0 ≤ D ∧ ∀ i,
      MemVectorFourierSobolev s ((m i).fourierMultiplier (carrierSource hU (ρ i) (φ i) (f i) (hφ i)
        (hf i).contDiffOn ((hsupport i).trans hSU)
        (hS.of_isClosed_subset (isClosed_tsupport _) (hsupport i)))) ∧
      vectorFourierSobolevNorm s ((m i).fourierMultiplier (carrierSource hU (ρ i) (φ i) (f i) (hφ i)
        (hf i).contDiffOn ((hsupport i).trans hSU)
        (hS.of_isClosed_subset (isClosed_tsupport _) (hsupport i)))) ≤
        D * A i * (ρ i) ^ (-Q) := by
  intro Q
  obtain ⟨q₀, _, hq₀⟩ := exists_finite_neumann_order hν.1 (s + (d : ℝ) / 2) Q (d + 1)
  obtain ⟨q₁, hq₁⟩ := exists_nat_gt (s + (d : ℝ) / 2)
  let q := q₀ + q₁
  have hq : s + (d : ℝ) / 2 < (q : ℝ) := by
    dsimp [q]
    rw [Nat.cast_add]
    linarith [Nat.cast_nonneg (α := ℝ) q₀]
  have horder : s + (d : ℝ) / 2 + (d + 1 : ℕ) - ν * q ≤ -Q := by
    dsimp [q]
    simp only [Nat.cast_add, Nat.cast_one] at hq₀ ⊢
    nlinarith [mul_nonneg hν.1.le (Nat.cast_nonneg (α := ℝ) q₁)]
  let J := envelopeJetProfileConstant d C
  have hJ : ∀ j, 0 ≤ J j := envelopeJetProfileConstant_nonneg d C
  let D := (r : ℝ) * max 0 M * gapKernelConstant d c G P J q * volume.real S *
    Real.sqrt (∫ ξ : (EuclideanSpace ℝ (Fin d)), (1 + ‖ξ‖) ^ (-(2 * (q : ℝ) - 2 * s)))
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (Nat.cast_nonneg r) (le_max_left _ _))
      (gapKernelConstant_nonneg c G P J hJ q)) (measureReal_nonneg))
      (Real.sqrt_nonneg _)
  refine ⟨D, hD, ?_⟩
  intro i
  have hAi := hA i
  have hKi : 0 ≤ K i := zero_le_one.trans (hK i)
  have hρi : 0 ≤ ρ i := zero_le_one.trans (hρ i)
  have hker := gapKernelConstant_nonneg (d := d) c G P J hJ q
  have hjets := norm_iteratedFDeriv_le_envelope_profile (hf i).continuous (hfLp i)
    (hA i) (hK i) (hmem i) (hprofile i)
  obtain ⟨hm, hb⟩ := masked_carrierSource_sobolev hU hS hSU (m i) (φ i) (f i) q s
    (hφ i) (hf i).contDiffOn (hsupport i) hc
    (mul_nonneg (hA i) (pow_nonneg hKi _)) hKi (hρ i) hs hq
    (hgap i) (hupper i) hP hJ (hphase i) (fun x _ j ↦ hjets j x)
  refine ⟨hm, hb.trans ?_⟩
  calc
    _ ≤ D * (A i * K i ^ (d + 1)) *
        ((ρ i) ^ (s + (d : ℝ) / 2) * (K i / ρ i) ^ q) := by
      dsimp [D]
      simp only [Fintype.card_fin]
      gcongr
      exact (hmask i).trans (le_max_right _ _)
    _ = (D * A i) * ((ρ i) ^ (s + (d : ℝ) / 2) *
        K i ^ (d + 1) * (K i / ρ i) ^ q) := by ring
    _ ≤ (D * A i) * (ρ i) ^ (s + (d : ℝ) / 2 + (d + 1 : ℕ) - ν * q) :=
      mul_le_mul_of_nonneg_left
        (finite_neumann_scale_bound (hρ i) hKi hν.1.le (hscale i) (d + 1) q)
        (mul_nonneg hD (hA i))
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hρ i) horder) (mul_nonneg hD (hA i))

/-- The inactive source estimate in the same concrete graded scale consumed by
`completeComplement_observations` (`app:ch_response:thm:response-literal-transfer`).
This is the already proved estimate above, with exact membership and norm
identification; no analytic estimate is added as an assumption. -/
theorem masked_carrierSource_rapidDecay (s : ℕ) :
    RapidDecayAt vectorFourierSobolevScale s ρ A
      (fun i ↦ (m i).fourierMultiplier (carrierSource hU (ρ i) (φ i) (f i) (hφ i)
        (hf i).contDiffOn ((hsupport i).trans hSU)
        (hS.of_isClosed_subset (isClosed_tsupport _) (hsupport i)))) := by
  intro Q
  obtain ⟨D, hD, hb⟩ := masked_carrierSource_arbitrary_precision hU hS hSU m φ f hφ hf
    hsupport hfLp A K ρ c G M ν P C hc hν hA hK hρ hscale hmask hgap hupper hP
    hphase hmem hprofile s (Nat.cast_nonneg s) Q
  refine ⟨D, hD, fun i ↦ ⟨(hb i).1, ?_⟩⟩
  simpa only [vectorFourierSobolevScale_gradeNorm s (hb i).1] using (hb i).2

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  (Jout : GradedScale W)
  (O : ι → Lp (EuclideanSpace ℂ (Fin r)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin d))) →ₗ[ℝ] W)
  (χout χin : ι → BoundedMask d) (t s : ℕ) (D e : ℝ)
  (hD : 0 ≤ D)
  (hin : ∀ i x, x ∈ tsupport (f i) → (χin i).symbol x = 1)
  (hcost : ∀ i v, MemVectorFourierSobolev (t : ℝ) v →
    O i ((χout i).multiply v) ∈ Jout.level s ∧
    Jout.gradeNorm s (O i ((χout i).multiply v)) ≤
      D * (ρ i) ^ e * vectorFourierSobolevNorm (t : ℝ) v)

include hD hin hcost

/-- Physical and demodulated observations of an inactive source factor, with
the exact source/target cutoff order of
`app:ch_response:thm:response-literal-transfer`.

For physical Sobolev norms take `Jout = vectorFourierSobolevScale` and `O = id`;
for demodulated norms take the actual demodulation map. The producer of `hcost`
is the fixed physical-cutoff/carrier multiplication estimate in the parent
`jc-response-complement` construction. It is explicitly a fixed polynomial
bound on all inputs at order `t`, chosen before precision, and remains an
instantiation obligation of that parent. The Fourier decay itself is proved
here from the original profile and primitive full gap.
-/
theorem localized_carrierSource_observations :
    RapidDecayAt Jout s ρ A (fun i ↦ O i ((m i).localized (χout i) (χin i)
      (carrierSource hU (ρ i) (φ i) (f i) (hφ i) (hf i).contDiffOn
        ((hsupport i).trans hSU) (hS.of_isClosed_subset (isClosed_tsupport _) (hsupport i))))) := by
  have hdecay := masked_carrierSource_rapidDecay hU hS hSU m φ f hφ hf
    hsupport hfLp A K ρ c G M ν P C hc hν hA hK hρ hscale hmask hgap hupper hP
    hphase hmem hprofile t
  apply rapidDecayAt_polynomial_observation vectorFourierSobolevScale Jout _ _ ρ A t s D e
    (fun i ↦ zero_lt_one.trans_le (hρ i)) hD hdecay
  intro i hv
  rw [(m i).localized_eq_on_supported_source (χout i) (χin i) _
    (carrierSource_plateau hU (ρ i) (φ i) (f i) (hφ i) (hf i).contDiffOn
      ((hsupport i).trans hSU) (hS.of_isClosed_subset (isClosed_tsupport _) (hsupport i))
      (χin i) (hin i))]
  simpa only [vectorFourierSobolevScale_gradeNorm t hv] using hcost i _ hv

omit hgap in
/-- The actual ordered `A₊-I` error has arbitrary precision in physical or
demodulated Sobolev norms (`app:ch_response:thm:response-literal-transfer`).
The full gap is required on the ENTIRE complementary mask `1-m`, including
shoulders and bounded frequencies. Both physical cutoffs are one on the
original envelope support. `hcost` is exactly the same fixed polynomial
cutoff/observation cost as in `localized_carrierSource_observations`; its
producer and remaining parent instantiation obligation are described there.
No arbitrary-accuracy estimate or parameter differentiation identity is assumed.
-/
theorem identityError_carrierSource_observations
    (hout : ∀ i x, x ∈ tsupport (f i) → (χout i).symbol x = 1)
    (hcomplementGap : ∀ i η, 1 - (m i).symbol η ≠ 0 → ∀ x ∈ U,
      c * (ρ i + ‖η‖) ≤ ‖ρ i • fderiv ℝ (φ i) x -
        InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) η‖) :
    let u := fun i ↦ carrierSource hU (ρ i) (φ i) (f i) (hφ i) (hf i).contDiffOn
      ((hsupport i).trans hSU) (hS.of_isClosed_subset (isClosed_tsupport _) (hsupport i))
    RapidDecayAt Jout s ρ A (fun i ↦ O i ((m i).localized (χout i) (χin i) (u i) - u i)) := by
  dsimp only
  have hbound : ∀ i, (m i).complement.bound ≤ 1 + M :=
    fun i ↦ by
      change 1 + (m i).bound ≤ 1 + M
      linarith [hmask i]
  have hdecay := masked_carrierSource_rapidDecay hU hS hSU (fun i ↦ (m i).complement)
    φ f hφ hf hsupport hfLp A K ρ c G (1 + M) ν P C hc hν hA hK hρ hscale
    hbound hcomplementGap hupper hP hphase hmem hprofile t
  apply rapidDecayAt_polynomial_observation vectorFourierSobolevScale Jout _ _ ρ A t s D e
    (fun i ↦ zero_lt_one.trans_le (hρ i)) hD hdecay
  intro i hv
  rw [localized_carrierSource_sub_identity hU (m i) (χout i) (χin i) (ρ i)
    (φ i) (f i) (hφ i) (hf i).contDiffOn ((hsupport i).trans hSU)
    (hS.of_isClosed_subset (isClosed_tsupport _) (hsupport i)) (hin i) (hout i), map_neg]
  obtain ⟨hm, hb⟩ := hcost i _ hv
  refine ⟨(Jout.level s).neg_mem hm, ?_⟩
  have hneg := Jout.gradeNorm_neg_one_pow_smul s 1 hm
  simp only [pow_one, neg_one_smul] at hneg
  rw [hneg, vectorFourierSobolevScale_gradeNorm t hv]
  exact hb

end JanetCartan.ResponseTransfer.Complement.InactiveSource
