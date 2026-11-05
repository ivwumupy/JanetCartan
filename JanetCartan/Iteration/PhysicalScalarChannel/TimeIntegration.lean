module

public import JanetCartan.Iteration.PhysicalScalarChannel.Family
public import JanetCartan.Analysis.Microlocal.SingleChannel.Assembly
public import JanetCartan.Analysis.Operator.NormalPerturbation.Weighted

/-!
# Integrating the full scalar band row in physical time

The actual scalar family supplies a single normal bound for its entire dyadic
union. This construction integrates that row bound, rather than adding individual
band norms. Its constant therefore has no band-count or logarithmic loss.
The kernel equality retains the transverse normalization, without the half
frequency weight of the differentiated carrier. Consumer:
`app:ch_mean_pairs:eq:raw-adjoint-moments`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators InnerProductSpace ENNReal

namespace JanetCartan.PhysicalScalarChannel
open NormalComparison SingleChannel NormalPerturbation

variable {d r : ℕ}
local notation "Y" => Euclidean d
local notation "X" => ℝ × Y
local notation "V" => EuclideanSpace ℂ (Fin r)

/-- The full transverse row is integrated on one physical time interval.
The normal bound is supplied by
`exists_retained_scalar_full_band_slice_family`, and all kernel equalities are
literal equalities on the same frequency domain, not new operator assumptions.
The resulting constant is independent of the number of bands. -/
theorem exists_fullBand_physical_slice_operator
    (G : UniformNormalGeometry d r) (C : ℕ → ℝ)
    {a b B : ℝ} (hab : a ≤ b) (hB : 0 ≤ B)
    {J : ℕ}
    (F : (j : Fin J) → (t : ℝ) → t ∈ Ioo a b → UniformNormalData G C)
    (K ε : Fin J → ℝ) (hε : ∀ j, ε j ∈ Icc 0 G.ε₀)
    (hbound : ∀ t (ht : t ∈ Ioo a b),
      ‖∑ j : Fin J, (F j t ht).uniformOscillatoryOperator (K j) (ε j) ∘L
        ((F j t ht).uniformOscillatoryOperator (K j) (ε j)).adjoint‖ ≤ B)
    (k : Fin J → X → Y → V)
    (hk : ∀ j, Continuous (Function.uncurry (k j)))
    (hs : ∀ j, HasCompactSupport (Function.uncurry (k j)))
    (htime : ∀ j t, t ∉ Ioo a b → ∀ y u, k j (t, y) u = 0)
    (hkernel : ∀ j t (ht : t ∈ Ioo a b) y u i,
      k j (t, y) u i = (normalOperatorScale d (K j) : ℂ) *
        oscillatoryFactor (K j) ((F j t ht).phase (ε j) y u) *
          (F j t ht).amplitude (ε j) y u i) :
    ∃ L : (PiLp 2 (fun _ : Fin J ↦ Lp ℂ 2 (volume.restrict G.D))) →L[ℂ]
        Lp V 2 (volume : Measure X),
      (∀ f, L f =ᵐ[volume] fun x ↦ ∑ j : Fin J, channelIntegral (k j) (f j) x) ∧
      ‖L‖ ^ 2 ≤ (b - a) * B := by
  classical
  let l : (PiLp 2 (fun _ : Fin J ↦ Lp ℂ 2 (volume.restrict G.D))) →ₗ[ℂ]
      Lp V 2 (volume : Measure X) :=
    ∑ j : Fin J, (channelIntegralLinearMap (hk j) (hs j)).comp
      (PiLp.proj 2 (fun _ : Fin J ↦ Lp ℂ 2 (volume.restrict G.D)) j).toLinearMap
  let g := fun (f : PiLp 2 (fun _ : Fin J ↦ Lp ℂ 2 (volume.restrict G.D))) (x : X) ↦
    ∑ j : Fin J, channelIntegral (k j) (f j) x
  have hmem (f) : MemLp (g f) 2 (volume : Measure X) :=
    memLp_finsetSum Finset.univ (fun j _ ↦ memLp_channelIntegral (hk j) (hs j) (f j))
  have heq (f) : l f =ᵐ[volume] g f := by
    simp only [l, LinearMap.sum_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      PiLp.proj_apply]
    refine (Lp.coeFn_finsetSum _ _).trans ?_
    refine (eventuallyEq_sum (s := Finset.univ)
      (fun j _ ↦ channelIntegralLinearMap_ae_integral (hk j) (hs j) (f j))).trans ?_
    exact Eventually.of_forall fun x ↦ Finset.sum_apply x _ _
  have hslice (f) (t : ℝ) (ht : t ∈ Ioo a b) :
      (∫ y, ‖g f (t, y)‖ ^ 2) ≤ B * ‖f‖ ^ 2 := by
    let A := fun j : Fin J ↦ (F j t ht).uniformOscillatoryOperator (K j) (ε j)
    let R := weightedRow (fun _ : Fin J ↦ (1 : ℝ)) A
    have hR : ‖R‖ ^ 2 ≤ B := by
      rw [← norm_normal, normal_weightedRow _ (fun _ ↦ zero_le_one)]
      simpa [A, normal] using hbound t ht
    have hRapply : R f = ∑ j : Fin J, A j (f j) := by
      simp [R, weightedRow_apply]
    have hactual (j : Fin J) (i : Fin r) :
        (fun y ↦ channelIntegral (k j) (f j) (t, y) i) =ᵐ[volume]
          fun y ↦ (A j (f j)) i y := by
      filter_upwards [(F j t ht).uniformOscillatoryOperator_ae_integral (K j) (hε j) (f j) i]
        with y hy
      rw [hy, channelIntegral, eval_integral_piLp
        (fun i ↦ (integrable_channelIntegrand (hk j) (hs j) (f j) (t, y)).eval_piLp i)]
      apply integral_congr_ae
      exact Eventually.of_forall fun u ↦ by
        simp only [PiLp.smul_apply, smul_eq_mul, hkernel j t ht]
        ring
    have hcomponents (i : Fin r) :
        (fun y ↦ g f (t, y) i) =ᵐ[volume] fun y ↦ (1 : ℂ) * (R f) i y := by
      have he := eventuallyEq_sum (s := Finset.univ) (fun j _ ↦ hactual j i)
      have hp : (R f) i = ∑ j : Fin J, (A j (f j)) i := by
        rw [hRapply]
        exact map_sum (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ Lp ℂ 2 (volume : Measure Y)) i)
          (fun j : Fin J ↦ A j (f j)) Finset.univ
      have hp₂ (y : Y) :
          (∑ j : Fin J, channelIntegral (k j) (f j) (t, y)) i =
            ∑ j : Fin J, channelIntegral (k j) (f j) (t, y) i :=
        map_sum (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) i)
          (fun j : Fin J ↦ channelIntegral (k j) (f j) (t, y)) Finset.univ
      filter_upwards [he, Lp.coeFn_finsetSum Finset.univ (fun j : Fin J ↦ (A j (f j)) i)]
        with y hy hz
      change (∑ j : Fin J, channelIntegral (k j) (f j) (t, y)) i = (1 : ℂ) * (R f) i y
      rw [hp₂, one_mul, hp]
      simpa only [Finset.sum_apply] using hy.trans hz.symm
    rw [integral_norm_sq_eq_sum_output (fun y ↦ g f (t, y)) (R f) 1 hcomponents]
    simp only [one_pow, one_mul]
    calc
      ‖R f‖ ^ 2 ≤ (‖R‖ * ‖f‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (R.le_opNorm f) 2
      _ = ‖R‖ ^ 2 * ‖f‖ ^ 2 := mul_pow _ _ _
      _ ≤ B * ‖f‖ ^ 2 := mul_le_mul_of_nonneg_right hR (sq_nonneg _)
  have henergy (f) : ‖l f‖ ^ 2 ≤ ((b - a) * B) * ‖f‖ ^ 2 := by
    rw [← integral_norm_sq_eq_norm_sq]
    have he := integral_congr_ae ((heq f).fun_comp fun v ↦ ‖v‖ ^ 2)
    dsimp only [Function.comp_def] at he
    rw [he]
    have hb := integral_norm_sq_le_of_slice_bound hab (hmem f)
      (fun t ht y ↦ by simp only [g, channelIntegral, htime _ t ht, smul_zero, integral_zero,
        Finset.sum_const_zero]) (fun t ht ↦ hslice f t ht)
    exact hb.trans_eq (by ring)
  have hBB : 0 ≤ (b - a) * B := mul_nonneg (sub_nonneg.mpr hab) hB
  have hnorm (f) : ‖l f‖ ≤ Real.sqrt ((b - a) * B) * ‖f‖ := by
    have he := henergy f
    have hh := Real.sq_sqrt hBB
    have hn : 0 ≤ Real.sqrt ((b - a) * B) * ‖f‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    nlinarith [sq_nonneg (‖l f‖ - Real.sqrt ((b - a) * B) * ‖f‖)]
  refine ⟨l.mkContinuous (Real.sqrt ((b - a) * B)) hnorm, heq, ?_⟩
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (l.mkContinuous_norm_le (Real.sqrt_nonneg _) hnorm) 2).trans_eq (Real.sq_sqrt hBB)

end JanetCartan.PhysicalScalarChannel
