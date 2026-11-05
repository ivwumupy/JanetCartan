module

public import JanetCartan.Analysis.Approximation.BallSmoothing.AffineLinearity
public import JanetCartan.Analysis.Approximation.BallSmoothing.FixedSupport
public import JanetCartan.Analysis.Approximation.BallSmoothing.AffineApproximation
public import JanetCartan.Analysis.Approximation.BallSmoothing.SobolevBounds

/-!
# Smoothing on an arbitrary ball

This constructs every field of the operator asserted in
`app:ch_regular_base:lem:ball-extension`. The real linear operators are
identically the affine transport of the manuscript's finite-binomial
inward-average formula. One compact subset of the prescribed open set
contains every output, all constants precede the input and scale, and both
the all-order norm bound and the `m`th-order approximation estimate are
proved for these same operators. No analytic smoothing interface is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Metric
open scoped ContDiff

namespace JanetCartan.BallSmoothing

open LocalSobolev

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Smoothing on a ball**, `app:ch_regular_base:lem:ball-extension`.
The actual real linear operators use only the original closed-ball data,
have one fixed compact support inside the prescribed open set, satisfy
both all-order `C^r` and integer Cartesian `H^r` bounds from the original
`C⁰` norm, and approximate to order `R⁻ᵐ` using exactly `m` original input
derivatives. The displayed literal formula and restriction independence
identify one genuine construction on closed-ball data. Its componentwise
vector and tensor action is `affineSmoothing_map`. -/
theorem exists_ballSmoothing (c : E) {a : ℝ} (ha : 0 < a)
    {V : Set E} (hV : IsOpen V) (hball : closedBall c a ⊆ V)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ (K : Set E) (R₀ : ℝ) (C : ℕ → ℝ) (A : ℝ)
      (S : (R : ℝ) → R₀ ≤ R → smoothClosedBallData (F := F) c a →ₗ[ℝ] (E → F)),
      IsCompact K ∧ K ⊆ V ∧ 1 ≤ R₀ ∧ (2 : ℝ) * m ≤ R₀ ∧
        (∀ r, 0 ≤ C r) ∧ 0 ≤ A ∧
        (∀ (R : ℝ) (hR : R₀ ≤ R) (f : smoothClosedBallData (F := F) c a),
          S R hR f = affineSmoothing c a R m (f : E → F) ∧
          ContDiff ℝ ∞ (S R hR f) ∧ tsupport (S R hR f) ⊆ K ∧
          (∀ r, MemLp (iteratedFDeriv ℝ r (S R hR f)) 2 volume ∧
            cNorm univ r (S R hR f) +
              cartesianJetNorm univ r (fun j ↦ iteratedFDeriv ℝ j (S R hR f)) ≤
                C r * R ^ r * cNorm (closedBall c a) 0 (f : E → F)) ∧
          cNorm (closedBall c a) 0 ((f : E → F) - S R hR f) ≤
            A * (R⁻¹)^m * cNorm (closedBall c a) m (f : E → F)) ∧
        ∀ (R : ℝ) (hR : R₀ ≤ R) (f g : smoothClosedBallData (F := F) c a),
          EqOn (f : E → F) (g : E → F) (closedBall c a) → S R hR f = S R hR g := by
  obtain ⟨K, Rg, hK, hKV, hRg, hsupp⟩ := exists_affineSmoothing_fixed_support (F := F) c ha hV hball
  obtain ⟨B, hB, hb⟩ := exists_affineSmoothing_jet_bounds (F := F) c ha m hm
  obtain ⟨H, hH, hh⟩ := exists_cartesianSobolev_profile_of_fixed_support (F := F) hK B hB
  let R₀ := max Rg ((2 : ℝ) * m)
  have hR₀g : Rg ≤ R₀ := le_max_left _ _
  have hR₀m : (2 : ℝ) * m ≤ R₀ := le_max_right _ _
  let D r := ∑ j ∈ Finset.range (r + 1), B j
  have hD r : 0 ≤ D r := Finset.sum_nonneg fun j _ ↦ hB j
  let C r := D r + H r
  let A := radialApproximationConstant m * ∑ j ∈ Finset.range (m + 1), a ^ j
  have hA : 0 ≤ A := mul_nonneg (radialApproximationConstant_nonneg m)
    (Finset.sum_nonneg fun j _ ↦ pow_nonneg ha.le _)
  let S (R : ℝ) (hR : R₀ ≤ R) : smoothClosedBallData (F := F) c a →ₗ[ℝ] (E → F) :=
    affineSmoothingLinear c ha hm (hR₀m.trans hR)
  refine ⟨K, R₀, C, A, S, hK, hKV, hRg.trans hR₀g, hR₀m,
    fun r ↦ add_nonneg (hD r) (hH r), hA, ?_, ?_⟩
  · intro R hR f
    have hRm := hR₀m.trans hR
    have hRgR := hR₀g.trans hR
    have hR1 : 1 ≤ R := hRg.trans hRgR
    have hR0 : 0 ≤ R := zero_le_one.trans hR1
    have hf := smoothClosedBallData_continuousOn f
    have hu := contDiff_affineSmoothing c ha hm hRm hf
    have hs := hsupp R hRgR m (f : E → F)
    refine ⟨rfl, hu, hs, ?_, cNorm_affineSmoothing_sub_le c ha hm hRm (f : E → F) f.property⟩
    intro r
    let M := cNorm (closedBall c a) 0 (f : E → F)
    have hM : 0 ≤ M := cNorm_nonneg _ _ _
    obtain ⟨hmem, _, hnorm⟩ := hh r R M (affineSmoothing c a R m (f : E → F))
      hR1 hM hu hs (fun j _ x ↦ hb R hRm (f : E → F) hf j x)
    refine ⟨hmem r le_rfl, ?_⟩
    have hc : cNorm univ r (affineSmoothing c a R m (f : E → F)) ≤ D r * R ^ r * M := by
      calc
        _ ≤ ∑ j ∈ Finset.range (r + 1), B j * R ^ j * M :=
          cNorm_le_sum_of_bounds
            (fun j _ ↦ mul_nonneg (mul_nonneg (hB j) (pow_nonneg hR0 _)) hM)
            (fun j _ x _ ↦ hb R hRm (f : E → F) hf j x)
        _ ≤ ∑ j ∈ Finset.range (r + 1), B j * R ^ r * M := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hR1 (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) (hB j)) hM
        _ = _ := by simp only [D, Finset.sum_mul]
    exact (add_le_add hc hnorm).trans_eq (by dsimp only [C]; ring)
  · intro R hR f g hfg
    exact affineSmoothing_congr_closedBall c ha hm (hR₀m.trans hR) hfg

end JanetCartan.BallSmoothing
