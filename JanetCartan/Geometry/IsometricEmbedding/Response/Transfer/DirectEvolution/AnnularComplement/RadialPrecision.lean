module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.Radial
public import JanetCartan.Analysis.Operator.FiniteNeumann.Decay

/-!
# Arbitrary precision after full radial integration

The all-frequency summation for the outside-annulus kernel in
`app:ch_response:lem:energy-carrier-jets`, retaining the original separate
coefficient and envelope scales from `app:ch_response:eq:fixed-factor-transfer`.
The source-kernel producer must supply the displayed profile. This deduction
integrates it over the entire Euclidean frequency space and chooses accuracy
before frequency and both scales. It does not postulate a graph remainder
estimate or assert that the actual differentiated kernel has that profile.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open LowEnvelope

/-- Full radial integration absorbs every fixed coefficient/envelope loss by
increasing only the number of source integrations. The losses `ell`, `b`,
`dLoss` and the physical order `s` are fixed before the accuracy order `N`.
All frequencies, including zero and the unbounded tail, are included.
Consumer: the physical and demodulated complementary Sobolev estimates for
`app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_annular_radial_precision (n s ell b : ℕ) (dLoss Q : ℝ)
    {ν : ℝ} (hν : 0 < ν) (_hνlt : ν < 1) :
    ∃ N : ℕ, s + n + 1 < N ∧ ∀ (lam L K : ℝ),
      1 ≤ lam → 1 ≤ L → L ≤ K → K ≤ lam ^ (1 - ν) →
      Integrable (fun ξ : Euclidean n =>
        (lam + ‖ξ‖) ^ s * (K / (lam + ‖ξ‖)) ^ N) ∧
      lam ^ dLoss * L ^ ell * K ^ b *
        (∫ ξ : Euclidean n, (lam + ‖ξ‖) ^ s * (K / (lam + ‖ξ‖)) ^ N) ≤
          lowEnvelopeRadialMass n * lam ^ (-Q) := by
  obtain ⟨q, hq, hqexp⟩ := exists_finite_neumann_order hν
    (dLoss + (s + n : ℕ)) Q (ell + b)
  refine ⟨q + s + n + 1, by omega, ?_⟩
  intro lam L K hlam hL hLK hKlam
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hK0 : 0 ≤ K := hL0.trans hLK
  have hKle : K ≤ lam := hKlam.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hlam (show 1 - ν ≤ 1 by linarith))
  obtain ⟨hi, hbnd⟩ := integral_lowEnvelope_kernel_profile_le (n := n) hK0 hlam0 hKle s q
  refine ⟨hi, ?_⟩
  have hscale := finite_neumann_scale_bound (c := dLoss + (s + n : ℕ))
    hlam hK0 hν.le hKlam (ell + b) q
  have hprecision : lam ^ (dLoss + (s + n : ℕ)) * K ^ (ell + b) * (K / lam) ^ q ≤
      lam ^ (-Q) := hscale.trans (Real.rpow_le_rpow_of_exponent_le hlam hqexp)
  calc
    _ ≤ lam ^ dLoss * L ^ ell * K ^ b *
        (lowEnvelopeRadialMass n * lam ^ (s + n) * (K / lam) ^ q) :=
      mul_le_mul_of_nonneg_left hbnd (by positivity)
    _ ≤ lam ^ dLoss * K ^ ell * K ^ b *
        (lowEnvelopeRadialMass n * lam ^ (s + n) * (K / lam) ^ q) := by
      gcongr
      have := lowEnvelopeRadialMass_nonneg n
      positivity
    _ = lowEnvelopeRadialMass n *
        (lam ^ (dLoss + (s + n : ℕ)) * K ^ (ell + b) * (K / lam) ^ q) := by
      rw [Real.rpow_add hlam0, Real.rpow_natCast, pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprecision (lowEnvelopeRadialMass_nonneg n)

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
