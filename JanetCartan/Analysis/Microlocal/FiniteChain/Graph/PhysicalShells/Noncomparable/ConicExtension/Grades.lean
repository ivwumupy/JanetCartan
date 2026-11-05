module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.ConicExtension.Phase
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Carriers

/-!
# Original phase grades at the concrete largest pair radius

The derivative hypotheses for `exists_conicPhysicalPair_summable_majorant`
come from the original phase's base derivatives. The affine terms of
`app:ch_regular:eq:joint-kernel-phase` contribute only to the first derivative.
The bounds here are uniform in both external bases and in the independent
shell indices, including shrinking graph shells and the output ball.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable.ConicExtension
open KernelEstimates KernelEstimates.NoncomparableGeometry
variable {n : ℕ}

private theorem iteratedFDeriv_affine_zero
    (l : (Euclidean n × Euclidean n) →L[ℝ] ℝ) (c : ℝ)
    (d : ℕ) (hd : 1 ≤ d) (z : Euclidean n × Euclidean n) :
    iteratedFDeriv ℝ (d + 1) (fun b => l b + c) z = 0 := by
  have he : (fun b => fderiv ℝ (fun b => l b + c) b) = fun _ => l := by
    funext b
    exact (l.hasFDerivAt.add_const c).fderiv
  rw [iteratedFDeriv_succ_eq_comp_right, he, iteratedFDeriv_const_of_ne (by omega)]
  exact (continuousMultilinearCurryRightEquiv' ℝ d (Euclidean n × Euclidean n) ℝ).symm.map_zero

/-- Higher frozen-base derivatives are exactly the original phase's base
jets in norm, for both orientations and all external bases. Thus no phase
extension or external-position grade is needed (`app:ch_regular:eq:high-phase`). -/
theorem norm_iteratedFDeriv_basePhase_eq (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (x y ξ η ζ : Euclidean n)
    (z : Euclidean n × Euclidean n) (d : ℕ) (hd : 1 ≤ d)
    (hS : ContDiffAt ℝ (d + 1) (fun b : Euclidean n × Euclidean n => S b.1 ξ) z) :
    ‖iteratedFDeriv ℝ (d + 1) (basePhase backward S x y ξ η ζ) z‖ =
      ‖iteratedFDeriv ℝ (d + 1) (fun b : Euclidean n × Euclidean n => S b.1 ξ) z‖ := by
  cases backward
  · let l := (-innerSL ℝ ζ).coprod (innerSL ℝ (η - ξ))
    let c := inner ℝ x ζ - inner ℝ y η
    have he : basePhase false S x y ξ η ζ =
        fun b : Euclidean n × Euclidean n => S b.1 ξ + (l b + c) := by
      funext b
      simp only [basePhase, jointPhase, Bool.false_eq_true, ↓reduceIte, forwardPhase,
        l, c, ContinuousLinearMap.coprod_apply, neg_apply,
        innerSL_apply_apply, inner_sub_left, real_inner_comm]
      ring
    rw [he, fun_iteratedFDeriv_add_apply hS (l.contDiff.add contDiff_const).contDiffAt,
      iteratedFDeriv_affine_zero l c d hd z, add_zero]
  · let l := (innerSL ℝ η).coprod (innerSL ℝ (ξ - ζ))
    let c := inner ℝ x ζ - inner ℝ y η
    have he : basePhase true S x y ξ η ζ =
        fun b : Euclidean n × Euclidean n => -(S b.1 ξ) + (l b + c) := by
      funext b
      simp only [basePhase, jointPhase, ↓reduceIte, reversePhase,
        l, c, ContinuousLinearMap.coprod_apply,
        innerSL_apply_apply, inner_sub_left, real_inner_comm]
      ring
    rw [he, fun_iteratedFDeriv_add_apply hS.neg (l.contDiff.add contDiff_const).contDiffAt,
      iteratedFDeriv_affine_zero l c d hd z, add_zero]
    change ‖iteratedFDeriv ℝ (d + 1) (-(fun b : Euclidean n × Euclidean n => S b.1 ξ)) z‖ = _
    rw [iteratedFDeriv_neg_apply, norm_neg]

/-- The first frozen-base derivative is bounded by the four physical
covector norms, independently of external bases
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem norm_fderiv_basePhase_le_covectors (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (x y ξ η ζ g : Euclidean n)
    (z : Euclidean n × Euclidean n)
    (hS : DifferentiableAt ℝ (fun u => S u ξ) z.1)
    (hg : fderiv ℝ (fun u => S u ξ) z.1 = innerSL ℝ g) :
    ‖fderiv ℝ (basePhase backward S x y ξ η ζ) z‖ ≤ ‖g‖ + ‖ξ‖ + ‖η‖ + ‖ζ‖ := by
  have hpair (a b : Euclidean n) :
      ‖(innerSL ℝ a).coprod (innerSL ℝ b)‖ ≤ ‖a‖ + ‖b‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    simp only [ContinuousLinearMap.coprod_apply, innerSL_apply_apply]
    calc
      ‖inner ℝ a v.1 + inner ℝ b v.2‖ ≤ ‖inner ℝ a v.1‖ + ‖inner ℝ b v.2‖ := norm_add_le _ _
      _ ≤ ‖a‖ * ‖v.1‖ + ‖b‖ * ‖v.2‖ := add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ ‖a‖ * ‖v‖ + ‖b‖ * ‖v‖ := add_le_add
        (mul_le_mul_of_nonneg_left (norm_fst_le v) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_snd_le v) (norm_nonneg _))
      _ = _ := by ring
  cases backward
  · rw [fderiv_basePhase_forward S x y ξ η ζ z hS, hg, ← map_sub]
    have hh := (hpair (g - ζ) (η - ξ)).trans
      (add_le_add (norm_sub_le g ζ) (norm_sub_le η ξ))
    linarith
  · rw [fderiv_basePhase_reverse S x y ξ η ζ z hS, hg, ← map_sub]
    have hh := (hpair (η - g) (ξ - ζ)).trans
      (add_le_add (norm_sub_le η g) (norm_sub_le ξ ζ))
    linarith

/-- Actual graph-carrier frequencies are bounded by four times the largest
pair radius, including arbitrarily small graph frequencies
(`app:ch_regular:eq:chain-tail`). -/
theorem graph_frequency_le_pairRadius {ρ : ℝ} (hρ : 1 ≤ ρ)
    (low : Bool) (j k : ℕ) {ξ : Euclidean n}
    (hξ : ξ ∈ normalizedGraphCarrier ρ low j) :
    ‖ρ • ξ‖ ≤ 4 * pairRadius ρ low j k := by
  have hh := ((mem_normalizedGraphCarrier_iff (zero_lt_one.trans_le hρ).ne' low j ξ).mp hξ).2
  have hl := (graphLower_bounds low j).2
  have hr := (le_max_right 1 (branchRadius low j)).trans (pairRadius_bounds hρ low j k).2.2.1
  dsimp [graphUpper] at hh
  linarith

/-- Primitive covector comparison gives the normalized first-grade constant
from the concrete carriers. This bound is uniform in both external positions;
the entire input annulus and output index zero are retained
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem basePhase_first_grade_of_carriers (backward : Bool)
    {ρ a b C : ℝ} (hρ : 1 ≤ ρ) (low : Bool) (j k : ℕ)
    (S : Euclidean n → Euclidean n → ℝ) (x y g : Euclidean n)
    (w : Euclidean n × Euclidean n × Euclidean n) (z : Euclidean n × Euclidean n)
    (hw : w ∈ normalizedGraphCarrier ρ low j ×ˢ frequencyAnnulus a b ×ˢ normalizedOutputCarrier ρ k)
    (hS : DifferentiableAt ℝ (fun u => S u (ρ • w.1)) z.1)
    (hg : fderiv ℝ (fun u => S u (ρ • w.1)) z.1 = innerSL ℝ g)
    (hcomp : ‖g‖ ≤ C * ‖ρ • w.1‖) :
    ‖fderiv ℝ (basePhase backward S x y (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2)) z‖ ≤
      pairRadius ρ low j k * (4 * max 0 C + 4 + max 0 b + 2) := by
  have hR := pairRadius_bounds hρ low j k
  have hξ := graph_frequency_le_pairRadius hρ low j k hw.1
  have hζ := ((mem_normalizedOutputCarrier_iff (zero_lt_one.trans_le hρ).ne' k w.2.2).mp hw.2.2).2
  have hη : ‖ρ • w.2.1‖ ≤ max 0 b * pairRadius ρ low j k := by
    rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans hρ)]
    have hi : ‖w.2.1‖ ≤ max 0 b := hw.2.1.2.trans (le_max_right 0 b)
    have ht := mul_le_mul hi hR.2.1 (zero_le_one.trans hρ) (le_max_left 0 b)
    nlinarith
  have hg' : ‖g‖ ≤ max 0 C * (4 * pairRadius ρ low j k) :=
    hcomp.trans ((mul_le_mul_of_nonneg_right (le_max_right 0 C) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hξ (le_max_left 0 C)))
  have hn := norm_fderiv_basePhase_le_covectors backward S x y (ρ • w.1)
    (ρ • w.2.1) (ρ • w.2.2) g z hS hg
  dsimp [outputUpper] at hζ
  nlinarith [hR.2.2.2]

/-- The original phase's homogeneous base grade supplies the physical grade
at the actual pair radius with only the fixed factor four. No cutoff
extension derivative or accuracy-dependent loss enters
(`app:ch_regular:eq:high-phase`, `app:ch_regular:eq:chain-tail`). -/
theorem basePhase_higher_grade_of_graphCarrier (backward : Bool)
    {ρ L H : ℝ} (hρ : 1 ≤ ρ) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (low : Bool) (j k : ℕ) (S : Euclidean n → Euclidean n → ℝ)
    (x y : Euclidean n) (w : Euclidean n × Euclidean n × Euclidean n)
    (z : Euclidean n × Euclidean n) (d : ℕ) (hd : 1 ≤ d)
    (hξ : w.1 ∈ normalizedGraphCarrier ρ low j)
    (hS : ContDiffAt ℝ (d + 1)
      (fun b : Euclidean n × Euclidean n => S b.1 (ρ • w.1)) z)
    (hp : ‖iteratedFDeriv ℝ (d + 1)
      (fun b : Euclidean n × Euclidean n => S b.1 (ρ • w.1)) z‖ ≤ ‖ρ • w.1‖ * H * L ^ d) :
    ‖iteratedFDeriv ℝ (d + 1)
      (basePhase backward S x y (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2)) z‖ ≤
        pairRadius ρ low j k * ((4 * H) * L ^ d) := by
  rw [norm_iteratedFDeriv_basePhase_eq backward S x y _ _ _ z d hd hS]
  apply hp.trans
  have hh := mul_le_mul_of_nonneg_right (graph_frequency_le_pairRadius hρ low j k hξ)
    (mul_nonneg hH (pow_nonneg hL d))
  nlinarith

end JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable.ConicExtension
