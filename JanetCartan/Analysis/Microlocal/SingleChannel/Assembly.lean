module

public import JanetCartan.Analysis.Microlocal.SingleChannel.Slices
public import JanetCartan.Analysis.Operator.RealQuadratures

/-!
# Full-space single-channel operators from buffered slices

Assembles `app:ch_osc:prop:osc-channel` from the mask-free normal theorem,
the exact normalization, and Fubini. The literal kernel is supplied with its
continuity, compact support, time support and original phase/amplitude formula.
There is no assumed channel or slice operator bound.

The normal-geometry API requires only `0 < d`. This assembly therefore includes
the one-dimensional slice case, with physical dimension `d + 1 = 2`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace JanetCartan.SingleChannel
open NormalComparison
variable {d r : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "X" => ℝ × EuclideanSpace ℝ (Fin d)

/-- The literal full-channel integral at a fixed time is exactly
`sqrt(K/(2π))` times the constructed normal-theorem slice, on every L² input
(`app:ch_osc:prop:osc-channel`). -/
theorem channelIntegral_slice_ae
    {G : UniformNormalGeometry d r} {C : ℕ → ℝ}
    (F : UniformNormalData G C) {ε K : ℝ} (hε : ε ∈ Icc 0 G.ε₀) (hK : 0 < K)
    (k : X → Y → V) (hk : Continuous (Function.uncurry k))
    (hs : HasCompactSupport (Function.uncurry k)) (t : ℝ)
    (hker : ∀ y u i, k (t, y) u i =
      (normalOperatorScale (d + 1) K : ℂ) * oscillatoryFactor K (F.phase ε y u) *
        F.amplitude ε y u i)
    (f : Lp ℂ 2 (volume.restrict G.D)) (i : Fin r) :
    (fun y ↦ channelIntegral k f (t, y) i) =ᵐ[volume] fun y ↦
      (Real.sqrt (K / (2 * Real.pi)) : ℂ) * (F.uniformOscillatoryOperator K ε f) i y := by
  filter_upwards [F.uniformOscillatoryOperator_ae_integral K hε f i] with y hy
  rw [hy, channelIntegral, eval_integral_piLp
    (fun j ↦ (integrable_channelIntegrand hk hs f (t, y)).eval_piLp j),
    ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun u ↦ by
    dsimp only
    rw [PiLp.smul_apply, smul_eq_mul, hker, normalOperatorScale_succ d hK,
      Complex.ofReal_mul]
    ring

/-- `app:ch_osc:prop:osc-channel` on the full complex input and physical
output spaces, in every positive slice dimension, including `d = 1`.
The constant depends only on the buffered geometry, the original finite jet
budget, and the interval length, and is chosen before the slice family and K.
The output norm is the Euclidean (hence flattened Frobenius) component norm.
Both complex quadratures remain in the input of the real operator. -/
theorem exists_singleChannelOperator
    (G : UniformNormalGeometry d r) (C : ℕ → ℝ)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ B > 0, ∀ (F : (t : ℝ) → t ∈ Ioo a b → UniformNormalData G C),
      ∀ ε ∈ Icc 0 G.ε₀, ∀ K ≥ 1,
      ∀ k : X → Y → V,
        Continuous (Function.uncurry k) → HasCompactSupport (Function.uncurry k) →
        (∀ t ∉ Ioo a b, ∀ y u, k (t, y) u = 0) →
        (∀ t (ht : t ∈ Ioo a b) y u i, k (t, y) u i =
          (normalOperatorScale (d + 1) K : ℂ) *
            oscillatoryFactor K ((F t ht).phase ε y u) * (F t ht).amplitude ε y u i) →
        ∃ L : Lp ℂ 2 (volume.restrict G.D) →L[ℂ] Lp V 2 (volume : Measure X),
          (∀ f, L f =ᵐ[volume] channelIntegral k f) ∧
          ‖L‖ ^ 2 ≤ B * K ∧ ‖realQuadratureChannel L‖ ^ 2 ≤ 4 * (B * K) := by
  obtain ⟨S, hS, hslice⟩ := exists_uniform_slice_energy_bound G C
  let B₀ := (b - a) * S ^ 2 / (2 * Real.pi)
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀]; positivity
  refine ⟨B₀ + 1, by positivity, ?_⟩
  intro F ε hε K hK k hk hs hsupport hker
  have hK' : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let l := channelIntegralLinearMap (μ := volume.restrict G.D) hk hs
  have henergy (f : Lp ℂ 2 (volume.restrict G.D)) :
      ‖l f‖ ^ 2 ≤ ((B₀ + 1) * K) * ‖f‖ ^ 2 := by
    change ‖(memLp_channelIntegral hk hs f).toLp _‖ ^ 2 ≤ _
    rw [← integral_norm_sq_eq_toLp_norm_sq]
    have hb := integral_norm_sq_le_of_slice_bound hab (memLp_channelIntegral hk hs f)
      (fun t ht y ↦ by simp [channelIntegral, hsupport t ht])
      (fun t ht ↦ hslice (F t ht) ε hε K hK' f (fun y ↦ channelIntegral k f (t, y))
        (fun i ↦ channelIntegral_slice_ae (F t ht) hε hK' k hk hs t (hker t ht) f i))
    calc
      (∫ x, ‖channelIntegral k f x‖ ^ 2) ≤
          (b - a) * (K / (2 * Real.pi) * S ^ 2 * ‖f‖ ^ 2) := hb
      _ = (B₀ * K) * ‖f‖ ^ 2 := by dsimp [B₀]; ring
      _ ≤ ((B₀ + 1) * K) * ‖f‖ ^ 2 := by gcongr; linarith
  have hbound (f : Lp ℂ 2 (volume.restrict G.D)) :
      ‖l f‖ ≤ Real.sqrt ((B₀ + 1) * K) * ‖f‖ := by
    have he := henergy f
    have hsqrt := Real.sq_sqrt (show 0 ≤ (B₀ + 1) * K by positivity)
    have hn : 0 ≤ Real.sqrt ((B₀ + 1) * K) * ‖f‖ := by positivity
    nlinarith [sq_nonneg (‖l f‖ - Real.sqrt ((B₀ + 1) * K) * ‖f‖)]
  let L := l.mkContinuous (Real.sqrt ((B₀ + 1) * K)) hbound
  have hL : ‖L‖ ^ 2 ≤ (B₀ + 1) * K := by
    have h := l.mkContinuous_norm_le (Real.sqrt_nonneg _) hbound
    calc
      ‖L‖ ^ 2 ≤ Real.sqrt ((B₀ + 1) * K) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = _ := Real.sq_sqrt (by positivity)
  refine ⟨L, fun f ↦ channelIntegralLinearMap_ae_integral hk hs f, hL, ?_⟩
  exact (realQuadratureChannel_norm_sq_le L).trans
    (mul_le_mul_of_nonneg_left hL (by norm_num))

end JanetCartan.SingleChannel
