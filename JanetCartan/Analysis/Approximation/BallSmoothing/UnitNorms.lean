module

public import JanetCartan.Analysis.Approximation.BallSmoothing.UnitBounds
public import JanetCartan.Analysis.Approximation.BallSmoothing.SobolevBounds
public import JanetCartan.Analysis.Approximation.BallSmoothing.Approximation

/-!
# Simultaneous norm estimates for the actual unit-ball smoother

Both norms in `app:ch_regular_base:eq:ball-extension-sobolev` are bounded
for the literal inward-average construction. The Sobolev norm is the
existing Cartesian norm, with one term per multiindex. Its integrability
and bound follow from the actual fixed output support and already proved
kernel derivative profile. The approximation clause uses the same output.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Metric
open scoped ContDiff

namespace JanetCartan.BallSmoothing

open LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The actual inward smoother satisfies BOTH global norm bounds, with
one profile chosen before the scale and input. Only original closed-ball
continuity and its `C⁰` norm enter this estimate
(`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem exists_unitSmoothing_norm_bounds (n : ℕ) (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℕ → ℝ, (∀ r, 0 ≤ C r) ∧
      ∀ R : ℝ, (2 : ℝ) * m ≤ R → ∀ f : EuclideanSpace ℝ (Fin n) → F,
        ContinuousOn f (closedBall 0 1) → ∀ r,
          cNorm univ r (unitSmoothing R m f) +
            cartesianJetNorm univ r (fun j ↦ iteratedFDeriv ℝ j (unitSmoothing R m f)) ≤
              C r * R ^ r * cNorm (closedBall 0 1) 0 f := by
  obtain ⟨B, hB, hb⟩ := exists_unitSmoothing_jet_bounds (F := F) n m hm
  obtain ⟨H, hH, hh⟩ := exists_cartesianSobolev_profile_of_fixed_support
    (F := F) (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 2) B hB
  let D r := ∑ j ∈ Finset.range (r + 1), B j
  have hD r : 0 ≤ D r := Finset.sum_nonneg fun j _ ↦ hB j
  refine ⟨fun r ↦ D r + H r, fun r ↦ add_nonneg (hD r) (hH r), ?_⟩
  intro R hR f hf r
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  let M := cNorm (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) 0 f
  have hM : 0 ≤ M := cNorm_nonneg _ _ _
  have hc : cNorm univ r (unitSmoothing R m f) ≤ D r * R ^ r * M := by
    calc
      _ ≤ ∑ j ∈ Finset.range (r + 1), B j * R ^ j * M :=
        cNorm_le_sum_of_bounds
          (fun j _ ↦ mul_nonneg (mul_nonneg (hB j) (pow_nonneg hR0 _)) hM)
          (fun j _ x _ ↦ hb R hR f hf j x)
      _ ≤ ∑ j ∈ Finset.range (r + 1), B j * R ^ r * M := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hR1 (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) (hB j)) hM
      _ = _ := by simp only [D, Finset.sum_mul]
  have hs := (hh r R M (unitSmoothing R m f) hR1 hM (contDiff_unitSmoothing hm hR hf)
    (unitSmoothing_tsupport_subset_closedBall_two hR1 m f)
    (fun j _ x ↦ hb R hR f hf j x)).2.2
  exact (add_le_add hc hs).trans_eq (by ring)

/-- All actual Sobolev jets of the inward smoother are in `L²`, so the
displayed integer Sobolev norms are genuine finite norms
(`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem memLp_unitSmoothing_jet {m : ℕ} (hm : 1 ≤ m) {R : ℝ}
    (hR : (2 : ℝ) * m ≤ R) {f : E → F}
    (hf : ContinuousOn f (closedBall 0 1)) (r : ℕ) :
    MemLp (iteratedFDeriv ℝ r (unitSmoothing R m f)) 2 volume := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  exact memLp_iteratedFDeriv_of_contDiff_hasCompactSupport
    (contDiff_unitSmoothing hm hR hf) (unitSmoothing_hasCompactSupport (by linarith) m f) r

end JanetCartan.BallSmoothing
