module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.ReserveInterpolation.Transport
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.Interpolation

/-!
# Joint coefficient and datum interpolation with a fixed symbol reserve

For `app:ch_background:prop:bg-adjoint`, after `bg-derivative-trade`, the
actual coefficient expansion uses only (s-k) high derivatives. A reserve Q
is absorbed by the fixed low baseline of the original amplitude and L,V.
The Fourier datum estimate therefore uses H^s, with no reserve derivative loss.

The geometric instantiation, conic support, operator bound, and final finite
sum remain obligations of the parent raw Sobolev construction. The theorems
here derive all generated coefficient estimates from original primitive jets.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow Pseudodifferential
variable {n : ℕ}

/-- The numerical joint interpolation following
`app:ch_background:eq:bg-derivative-trade`. The Fourier interpolation theorem
is applied to the actual datum. The coefficient has exponent (s-k)/s, so the
right side involves H^s and H times L2, without a fixed derivative loss. -/
theorem adjoint_coefficient_data_interpolate {s k : ℕ} (hs : 0 < s) (hk : k ≤ s)
    (C : ℝ) (hC : 0 ≤ C) {H R A : ℝ} (hH : 0 ≤ H)
    (hA : A ≤ C * H ^ (((s-k : ℕ) : ℝ) / s) * Real.sqrt R)
    (u : MeasureTheory.Lp (α := Euclidean n) ℂ 2) (hu : MemFourierSobolev s u) :
    A * fourierSobolevNorm k u ≤
      C * Real.sqrt R * (fourierSobolevNorm s u + H * ‖u‖) := by
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  have he : ((s-k : ℕ) : ℝ) / s = 1 - (k : ℝ) / s := by
    rw [Nat.cast_sub hk, sub_div, div_self hs']
  have hi := fourierSobolevNorm_weighted_interpolate
    (by positivity : (0 : ℝ) ≤ k) (by exact_mod_cast hk) hH hu
  rw [fourierSobolevNorm_zero] at hi
  calc
    _ ≤ (C * H ^ (((s-k : ℕ) : ℝ) / s) * Real.sqrt R) * fourierSobolevNorm k u :=
      mul_le_mul_of_nonneg_right hA (fourierSobolevNorm_nonneg _ _)
    _ = (C * Real.sqrt R) * (H ^ (1 - (k : ℝ) / s) * fourierSobolevNorm k u) := by
      rw [he]
      ring
    _ ≤ (C * Real.sqrt R) * (H * ‖u‖ + fourierSobolevNorm s u) :=
      mul_le_mul_of_nonneg_left hi (mul_nonneg hC (Real.sqrt_nonneg R))
    _ = _ := by ring

set_option maxHeartbeats 800000 in
/-- Actual generated coefficient jets times the datum norm, with one
constant for every q ≤ Q chosen before H and the datum. This is the numerical
coefficient/data estimate consumed by the raw Sobolev assembly of
`app:ch_background:prop:bg-adjoint`; all generated-symbol premises have been
discharged by the expression recursion and the original primitive profiles. -/
theorem exists_expansion_fixedReserve_joint_bound (L V) (a : AdjointAmplitude n)
    (ha : ∀ η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (ds : List (InitialCarrierDerivative n)) (χ : ℝ → ℝ)
    (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds
      (frequencyScaleAmplitude (halfOrderRadialFactor χ) a))
    (hs : 0 < ds.length) (Q : ℕ) (W B : ℕ → ℝ) (hW : ∀ i, 0 ≤ W i) (hB : ∀ i, 0 ≤ B i) :
    ∃ C ≥ 0, ∀ (H R : ℝ), 1 ≤ H →
      ∀ (U : Set (Euclidean (n-1))), IsOpen U →
      (∀ η ∈ U, ∀ p, ContDiffAt ℝ ∞
        (fun p : AdjointSymbolPoint n ↦ a p.1.1 p.1.2 (R • p.2)) (p,η)) →
      ∀ (p : AdjointSymbolPoint n), p.2 ∈ U →
      ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦
        halfOrderRadialFactor χ (R • p.2)) p →
      (∀ i ≤ Q, ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
        halfOrderRadialFactor χ (R • p.2)) p‖ ≤ W i * Real.sqrt R) →
      (∀ i ≤ ds.length - t.dataDerivatives.length + Q,
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          a p.1.1 p.1.2 (R • p.2)) p‖ ≤ B i * H ^ (((i - Q : ℕ) : ℝ) / ds.length)) →
      (∀ d ∈ ds, ∀ j i, i ≤ ds.length - t.dataDerivatives.length + Q →
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          branchField L V d j p.1) p‖ ≤ B i * H ^ (((i - Q : ℕ) : ℝ) / ds.length)) →
      ∀ (u : MeasureTheory.Lp (α := Euclidean n) ℂ 2),
      MemFourierSobolev ds.length u →
      ∀ q ≤ Q, ‖iteratedFDeriv ℝ q (fun p : AdjointSymbolPoint n ↦
          t.amplitude p.1.1 p.1.2 (R • p.2)) p‖ *
          fourierSobolevNorm t.dataDerivatives.length u ≤
        C * Real.sqrt R * (fourierSobolevNorm ds.length u + H * ‖u‖) := by
  obtain ⟨C, hC, hb⟩ := exists_expansion_fixedReserve_symbol_bound L V a ha hfield
    ds χ t ht hs Q W B hW hB
  refine ⟨C, hC, ?_⟩
  intro H R hH U hU hlocal p hp hrad hradBound hamp hcoeff u hu q hq
  exact adjoint_coefficient_data_interpolate hs
    (dataDerivatives_length_le_expansion L V ds _ t ht) C hC (le_trans zero_le_one hH)
    (hb H R hH U hU hlocal p hp hrad hradBound hamp hcoeff q hq) u hu

set_option maxHeartbeats 800000 in
/-- The full transported primitive deduction, including datum interpolation,
for `app:ch_background:prop:bg-adjoint`. The constant is uniform over q ≤ Q,
H, frequency scale and datum. Every rho, r(z,Y), flow and L,V premise is a
primitive smoothness or jet bound; no generated coefficient estimate is assumed. -/
theorem exists_transportExpansion_fixedReserve_joint_bound (L V c ρ r Y flow)
    (hc : ContDiff ℝ ∞ (c : AdjointJetPoint n → ℂ))
    (hρ : ContDiff ℝ ∞ (fun v : CarrierParameter × Euclidean (n-1) ↦ ρ v.1 v.2))
    (hr : ContDiff ℝ ∞ r)
    (hY : ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ (p.1, Y p)))
    (hf : ContDiff ℝ ∞ flow)
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (ds : List (InitialCarrierDerivative n)) (χ : ℝ → ℝ)
    (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds
      (frequencyScaleAmplitude (halfOrderRadialFactor χ)
        (normalizedTransportAmplitude c ρ r Y flow)))
    (hs : 0 < ds.length) (Q : ℕ) (C P N A B F D W : ℕ → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hP : ∀ i, 0 ≤ P i) (hNpos : ∀ i, 0 ≤ N i)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i) (hF : ∀ i, 0 ≤ F i)
    (hD : ∀ i, 0 ≤ D i) (hW : ∀ i, 0 ≤ W i) :
    ∃ K ≥ 0, ∀ (H R : ℝ), 1 ≤ H →
      ∀ (U : Set (Euclidean (n-1))), IsOpen U →
      (∀ η ∈ U, ∀ p, ContDiffAt ℝ ∞ (adjointAngularGraph R) (p,η)) →
      ∀ (p : AdjointSymbolPoint n), p.2 ∈ U →
      ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦ halfOrderRadialFactor χ (R • p.2)) p →
      (∀ i ≤ Q, ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
        halfOrderRadialFactor χ (R • p.2)) p‖ ≤ W i * Real.sqrt R) →
      (∀ i ≤ ds.length - t.dataDerivatives.length + Q,
        ‖iteratedFDeriv ℝ i c p.1‖ ≤
          C i * H ^ (((i - Q : ℕ) : ℝ) / ds.length)) →
      (∀ i ≤ ds.length - t.dataDerivatives.length + Q,
        ‖iteratedFDeriv ℝ i (fun v : CarrierParameter × Euclidean (n-1) ↦ ρ v.1 v.2)
          (adjointAngularGraph R p)‖ ≤ P i * H ^ (((i - Q : ℕ) : ℝ) / ds.length)) →
      (∀ i, 1 ≤ i → i ≤ ds.length - t.dataDerivatives.length + Q →
        ‖iteratedFDeriv ℝ i (adjointAngularGraph R) p‖ ≤
          N i * H ^ (((i-1-Q : ℕ) : ℝ) / ds.length)) →
      (∀ i ≤ ds.length - t.dataDerivatives.length + Q,
        ‖iteratedFDeriv ℝ i r (adjointScalarGraph Y p)‖ ≤ A i * H ^ (((i - Q : ℕ) : ℝ) / ds.length)) →
      (∀ i, 1 ≤ i → i ≤ ds.length - t.dataDerivatives.length + Q →
        ‖iteratedFDeriv ℝ i (fun v : AdjointJetPoint n ↦ (v.1, Y v)) p.1‖ ≤
          B i * H ^ (((i-1-Q : ℕ) : ℝ) / ds.length)) →
      (∀ i ≤ ds.length - t.dataDerivatives.length + Q,
        ‖iteratedFDeriv ℝ i flow p.1‖ ≤
          F i * H ^ (((i - Q : ℕ) : ℝ) / ds.length)) →
      (∀ d ∈ ds, ∀ j i, i ≤ ds.length - t.dataDerivatives.length + Q →
        ‖iteratedFDeriv ℝ i (branchField L V d j) p.1‖ ≤
          D i * H ^ (((i - Q : ℕ) : ℝ) / ds.length)) →
      ∀ (u : MeasureTheory.Lp (α := Euclidean n) ℂ 2),
      MemFourierSobolev ds.length u →
      ∀ q ≤ Q, ‖iteratedFDeriv ℝ q (fun p : AdjointSymbolPoint n ↦
          t.amplitude p.1.1 p.1.2 (R • p.2)) p‖ *
          fourierSobolevNorm t.dataDerivatives.length u ≤
        K * Real.sqrt R * (fourierSobolevNorm ds.length u + H * ‖u‖) := by
  obtain ⟨K, hK, hb⟩ := exists_transportExpansion_fixedReserve_symbol_bound
    L V c ρ r Y flow hc hρ hr hY hf hfield ds χ t ht hs Q C P N A B F D W
    hC hP hNpos hA hB hF hD hW
  refine ⟨K, hK, ?_⟩
  intro H R hH U hU hN p hp hrad hradBound hcC hρP hNN hrA hYB hfF hcoeff u hu q hq
  exact adjoint_coefficient_data_interpolate hs
    (dataDerivatives_length_le_expansion L V ds _ t ht) K hK (le_trans zero_le_one hH)
    (hb H R hH U hU hN p hp hrad hradBound hcC hρP hNN hrA hYB hfF hcoeff q hq) u hu

/-- The s=0 coefficient/data estimate of `app:ch_background:prop:bg-adjoint`.
The empty word has no datum derivatives, and only fixed low symbol profiles
are needed. The constant is chosen before the scale and the L2 datum. -/
theorem exists_expansion_zero_joint_bound (L V) (a : AdjointAmplitude n)
    (χ : ℝ → ℝ) (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V []
      (frequencyScaleAmplitude (halfOrderRadialFactor χ) a))
    (q : ℕ) (W B : ℕ → ℝ) (hW : ∀ i, 0 ≤ W i) (hB : ∀ i, 0 ≤ B i) :
    ∃ C ≥ 0, ∀ (R : ℝ) (p : AdjointSymbolPoint n),
      ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦ a p.1.1 p.1.2 (R • p.2)) p →
      ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦ halfOrderRadialFactor χ (R • p.2)) p →
      (∀ i ≤ q, ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
        halfOrderRadialFactor χ (R • p.2)) p‖ ≤ W i * Real.sqrt R) →
      (∀ i ≤ q, ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
        a p.1.1 p.1.2 (R • p.2)) p‖ ≤ B i) →
      ∀ (u : MeasureTheory.Lp (α := Euclidean n) ℂ 2),
      ‖iteratedFDeriv ℝ q (fun p : AdjointSymbolPoint n ↦
        t.amplitude p.1.1 p.1.2 (R • p.2)) p‖ *
          fourierSobolevNorm t.dataDerivatives.length u ≤ C * Real.sqrt R * ‖u‖ := by
  obtain ⟨C, hC, hb⟩ := exists_expansion_zero_halfOrder_bound L V a χ t ht q W B hW hB
  refine ⟨C, hC, ?_⟩
  intro R p ha hrad hradBound hamp u
  have hk : t.dataDerivatives.length = 0 := Nat.eq_zero_of_le_zero
    (dataDerivatives_length_le_expansion L V [] _ t ht)
  rw [hk, Nat.cast_zero, fourierSobolevNorm_zero]
  exact mul_le_mul_of_nonneg_right (hb R p ha hrad hradBound hamp) (norm_nonneg u)

end JanetCartan.ContinuumAdjoint.DerivativeKernels
