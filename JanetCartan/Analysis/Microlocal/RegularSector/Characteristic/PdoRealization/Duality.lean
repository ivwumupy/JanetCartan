module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PdoRealization.Normalization
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.FourierPairing

/-!
# Euclidean negative-order duality for the canonical PDO estimates

The positive estimates for the literal adjoint imply negative-order estimates
for the SAME operator, as in `app:ch_regular_base:eq:negative-duality`.
The dual test is constructed using inverse Fourier transform and the opposite
Bessel weight. No negative-order bound is assumed. Consumers are the natural
and gain-one estimates in `PdoRealization.NegativeBounds`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory FourierTransform
open scoped ComplexInnerProductSpace
namespace JanetCartan.RegularSector.Characteristic.PdoRealization
open Pseudodifferential

/-- Construct the dual norm test on actual Euclidean Lebesgue L². This closes
the duality step for the canonical PDO at nonpositive orders in
`app:ch_regular_base:eq:negative-duality`. -/
theorem negativeFourierSobolevNorm_le_of_pairings {n : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (v : Lp (α := Euclidean n) ℂ 2) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ g : Lp (α := Euclidean n) ℂ 2, MemFourierSobolev s g →
      ‖inner ℂ v g‖ ≤ K * fourierSobolevNorm s g) :
    fourierSobolevNorm (-s) v ≤ K := by
  let F := Lp.fourierTransformₗᵢ (Euclidean n) ℂ
  have hv := memFourierSobolev_of_nonpos (neg_nonpos.mpr hs) v
  let w := hv.toLp (weightedL2Fourier (-s) v)
  let q := F.symm w
  have hq := memFourierSobolev_of_nonpos (neg_nonpos.mpr hs) q
  let z := hq.toLp (weightedL2Fourier (-s) q)
  let g := F.symm z
  have hFg : (𝓕 g : Lp ℂ 2 (volume : Measure (Euclidean n))) = z := F.apply_symm_apply z
  have hFq : (𝓕 q : Lp ℂ 2 (volume : Measure (Euclidean n))) = w := F.apply_symm_apply w
  have hwgt : weightedL2Fourier s g =ᵐ[volume] w := by
    filter_upwards [hq.coeFn_toLp] with ξ hξ
    change z ξ = _ at hξ
    simp only [weightedL2Fourier, hFg, hξ, weightedL2Fourier, hFq, smul_smul,
      ← euclideanSobolevWeight_add, add_neg_cancel, euclideanSobolevWeight_zero, one_smul]
  have hg : MemFourierSobolev s g := (memLp_congr_ae hwgt).mpr (Lp.memLp w)
  have hw : hg.toLp (weightedL2Fourier s g) = w := Lp.ext (hg.coeFn_toLp.trans hwgt)
  have hn : fourierSobolevNorm s g = ‖w‖ := by rw [← hw]; exact (Lp.norm_toLp _ hg).symm
  have hn' : fourierSobolevNorm (-s) v = ‖w‖ := by exact (Lp.norm_toLp _ hv).symm
  have hi : inner ℂ v g = inner ℂ w w := by
    rw [ArbitraryAccuracy.inner_eq_weightedFourier_inner hv hg, hw]
  have hh := h g hg
  rw [hi, hn, ← inner_self_re_eq_norm, inner_self_eq_norm_mul_norm] at hh
  rw [hn']
  by_cases hw0 : ‖w‖ = 0
  · simpa [hw0] using hK
  · nlinarith [norm_nonneg w]

/-- A proved positive estimate for the literal adjoint yields the negative
estimate for the same operator, including the gain-one case `t = s + 1`.
Consumers instantiate the positive premise from `Sobolev.IntegerBounds`.
Source: `app:ch_regular_base:eq:negative-duality`. -/
theorem negativeFourierSobolev_bound_of_adjoint {n : ℕ} {s t K : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hK : 0 ≤ K)
    (T : Lp ℂ 2 (volume : Measure (Euclidean n)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hT : ∀ g, MemFourierSobolev s g →
      MemFourierSobolev t (T.adjoint g) ∧
        fourierSobolevNorm t (T.adjoint g) ≤ K * fourierSobolevNorm s g)
    (f : Lp ℂ 2 (volume : Measure (Euclidean n))) :
    MemFourierSobolev (-s) (T f) ∧
      fourierSobolevNorm (-s) (T f) ≤ K * fourierSobolevNorm (-t) f := by
  refine ⟨memFourierSobolev_of_nonpos (neg_nonpos.mpr hs) _, ?_⟩
  apply negativeFourierSobolevNorm_le_of_pairings hs _
    (mul_nonneg hK (fourierSobolevNorm_nonneg _ _))
  intro g hg
  rw [← ContinuousLinearMap.adjoint_inner_right]
  calc
    _ ≤ fourierSobolevNorm (-t) f * fourierSobolevNorm t (T.adjoint g) :=
      ArbitraryAccuracy.norm_inner_le_fourierSobolevNorm_mul
        (memFourierSobolev_of_nonpos (neg_nonpos.mpr ht) f) (hT g hg).1
    _ ≤ fourierSobolevNorm (-t) f * (K * fourierSobolevNorm s g) :=
      mul_le_mul_of_nonneg_left (hT g hg).2 (fourierSobolevNorm_nonneg _ _)
    _ = _ := by ring

/-- The positive tame estimate gives one linear high-coefficient factor in
negative duality. Consumer: the four canonical negative integer estimates in
`NegativeBounds`, using the actual scalar PDO producers.
Source: `app:ch_regular_base:eq:negative-duality`. -/
theorem negativeFourierSobolev_tame_bound_of_adjoint {n : ℕ} {s t C H : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (T : Lp ℂ 2 (volume : Measure (Euclidean n)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hT : ∀ g, MemFourierSobolev s g →
      MemFourierSobolev t (T.adjoint g) ∧
        fourierSobolevNorm t (T.adjoint g) ≤
          C * (fourierSobolevNorm s g + H * ‖g‖))
    (f : Lp ℂ 2 (volume : Measure (Euclidean n))) :
    MemFourierSobolev (-s) (T f) ∧
      fourierSobolevNorm (-s) (T f) ≤
        (C * (1 + H)) * fourierSobolevNorm (-t) f := by
  apply negativeFourierSobolev_bound_of_adjoint hs ht (by positivity) T _ f
  intro g hg
  refine ⟨(hT g hg).1, (hT g hg).2.trans ?_⟩
  calc
    _ ≤ C * (fourierSobolevNorm s g + H * fourierSobolevNorm s g) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (norm_le_fourierSobolevNorm hs hg) hH)) hC
    _ = _ := by ring

end JanetCartan.RegularSector.Characteristic.PdoRealization
