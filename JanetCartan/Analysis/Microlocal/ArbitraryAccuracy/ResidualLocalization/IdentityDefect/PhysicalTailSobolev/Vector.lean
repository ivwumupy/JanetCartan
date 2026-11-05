module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailSobolev.ScalarTests
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FourierAssembly.Extension

/-!
# Vector physical tails and density

The scalar test estimate is applied to the literal Euclidean fiber
coordinates. The existing compact-smooth density theorem then extends it
to every L² input of the same bounded operator. No regularity of its L²
outputs is assumed (`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailSobolev

open FourierIntegral Pseudodifferential

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- The finite scalar kernel-jet bound gives an all-data vector Fourier
Sobolev estimate for its bounded realization. The realization premise is
only the literal action on the dense graph tests; neither weak derivatives
nor Sobolev output bounds are premises. Consumer: the signed physical tails
of the right localizer in `app:ch_regular:eq:resolved-angular-tail`.
The constant precedes the kernel, its budget and the bounded realization. -/
theorem exists_physicalTail_vector_fourierSobolev_constant (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : E → E → ℂ),
      ContDiff ℝ ∞ (Function.uncurry k) → ∀ B : ℝ, 0 ≤ B →
      (∀ j ≤ m, ∀ x y,
        (1 + ‖x - y‖) ^ (n + 1) * ‖iteratedFDeriv ℝ j (fun z ↦ k z y) x‖ ≤ B) →
      ∀ T : H →L[ℂ] H,
      (∀ u : graphTestSpace n r, T (graphTestToLp u) =ᵐ[volume]
        fun x ↦ ∫ y, k x y • u.val y) →
      ∀ u : H, MemVectorFourierSobolev (m : ℝ) (T u) ∧
        vectorFourierSobolevNorm (m : ℝ) (T u) ≤ C * B * ‖u‖ := by
  obtain ⟨C, hC, hscalar⟩ := exists_physicalTail_scalarTest_fourierSobolev_constant (n := n) m
  refine ⟨(r : ℝ) * r * ((r : ℝ) * C), by positivity, ?_⟩
  intro k hk B hB hb T hT u
  have htest (v : graphTestSpace n r) :
      MemVectorFourierSobolev (m : ℝ) (T (graphTestToLp v)) ∧
      vectorFourierSobolevNorm (m : ℝ) (T (graphTestToLp v)) ≤
        ((r : ℝ) * C * B) *
          (vectorFourierSobolevNorm (0 : ℝ) (graphTestToLp v) + 0 * ‖graphTestToLp v‖) := by
    let Q := finiteL2CoordinateIsometry (I := Fin r) (volume : Measure E)
    have hcoord (a : Fin r) :
        MemFourierSobolev (m : ℝ) (Q (T (graphTestToLp v)) a) ∧
          fourierSobolevNorm (m : ℝ) (Q (T (graphTestToLp v)) a) ≤
            C * B * ‖graphTestToLp v‖ := by
      let g : E → ℂ := fun y ↦ v.val y a
      let P : V →L[ℂ] ℂ := PiLp.proj 2 (fun _ : Fin r ↦ ℂ) a
      have hg : ContDiff ℝ ∞ g := (P.restrictScalars ℝ).contDiff.comp v.property.1
      have hgc : HasCompactSupport g := v.property.2.comp_left P.map_zero
      have hki (x : E) : Integrable (fun y ↦ k x y • v.val y) :=
        ((hk.continuous.comp (continuous_const.prodMk continuous_id)).smul
          v.property.1.continuous).integrable_of_hasCompactSupport
            (v.property.2.smul_left (f := fun y ↦ k x y))
      have he : Q (T (graphTestToLp v)) a =ᵐ[volume]
          fun x ↦ ∫ y, k x y * g y := by
        filter_upwards [finiteL2Coordinates_apply_ae volume (T (graphTestToLp v)) a,
          hT v] with x hx hv
        change (Q (T (graphTestToLp v)) a) x = (T (graphTestToLp v) x) a at hx
        rw [hx, hv]
        exact (P.integral_comp_comm (hki x)).symm
      have h := hscalar k hk B hB hb g hg hgc _ he
      have heInput : Q (graphTestToLp v) a = (hg.continuous.memLp_of_hasCompactSupport hgc).toLp g := by
        apply Lp.ext
        filter_upwards [finiteL2Coordinates_apply_ae volume (graphTestToLp v) a,
          (graphTest_memLp v).coeFn_toLp,
          (hg.continuous.memLp_of_hasCompactSupport hgc).coeFn_toLp] with x hx hv hgx
        exact hx.trans ((congrArg (fun z : V ↦ z a) hv).trans hgx.symm)
      have hgnorm : (eLpNorm g 2 volume).toReal ≤ ‖graphTestToLp v‖ := by
        rw [← Lp.norm_toLp (f := g) (hg.continuous.memLp_of_hasCompactSupport hgc), ← heInput]
        exact (PiLp.norm_apply_le (Q (graphTestToLp v)) a).trans_eq (Q.norm_map _)
      exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_left hgnorm (mul_nonneg hC hB))⟩
    refine ⟨fun a ↦ (hcoord a).1, ?_⟩
    calc
      _ ≤ ∑ a, fourierSobolevNorm (m : ℝ) (Q (T (graphTestToLp v)) a) :=
        matrixFourierSobolevNorm_le_sum _ _
      _ ≤ ∑ _a : Fin r, C * B * ‖graphTestToLp v‖ :=
        Finset.sum_le_sum (fun a _ ↦ (hcoord a).2)
      _ = _ := by simp [mul_assoc]
  have hu : MemVectorFourierSobolev (0 : ℝ) u := fun a ↦ memFourierSobolev_zero _
  have h := graph_vector_bound_of_compactSmooth T 0 (m : ℝ)
    ((r : ℝ) * C * B) 0 (by positivity) le_rfl (by simpa only [Nat.cast_zero] using htest)
    u (by simpa only [Nat.cast_zero] using hu)
  simpa only [Nat.cast_zero, vectorFourierSobolevNorm_zero, zero_mul, add_zero, mul_assoc] using h

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailSobolev
