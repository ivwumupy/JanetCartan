module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.Density

/-!
# Density bounds after subtracting the response amplitude

The consumer is `app:ch_response:eq:current-density-lipschitz`. The input maps
are the raw derivative amplitude, its leading term, and the demodulated physical
derivative of the SAME fixed response. The corrected amplitude is their literal
difference. Its size and error bounds are proved, rather than assumed as an
additional corrected-family interface.

The raw finite-jet estimates belong to `RawPrimary`; the response derivative
estimate belongs to `Response.Transfer`. Their actual same-history instantiation
remains necessary. In particular this deduction does not construct an inverse.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CorrectedAtoms

variable {R D : Type*} [AddCommGroup R] [Module ℝ R]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Subtracting the literal response derivative preserves the density Lipschitz
bound (`app:ch_response:eq:current-density-lipschitz`). `Kpr` bounds the raw
amplitude error and `Kresp` bounds the demodulated physical response derivative,
both with the SAME finite-jet seminorm `p`. The displayed constant is independent
of `lam` and of any later accuracy. The response estimate is still a producer
obligation; it is not replaced by a premise about the corrected density. -/
theorem cNorm_atomicDensityError_sub_le_of_response
    {m n : Type*} [Fintype m] [Fintype n]
    (Apr A₀ Y : R →ₗ[ℝ] (D → Matrix m n ℂ)) {s : Set D} (hs : IsCompact s) {q : ℕ}
    (hApr : ∀ u, ContDiff ℝ q (Apr u)) (hA₀ : ∀ u, ContDiff ℝ q (A₀ u))
    (hY : ∀ u, ContDiff ℝ q (Y u))
    (p : R → ℝ) (hp : ∀ u, 0 ≤ p u) {C₀ Kpr Kresp : ℝ}
    (hC₀ : 0 ≤ C₀) (hKpr : 0 ≤ Kpr) (hKresp : 0 ≤ Kresp)
    {lam : ℝ} (hlam : 1 ≤ lam)
    (hleading : ∀ u, cNorm s q (A₀ u) ≤ C₀ * p u)
    (hprimary : ∀ u, cNorm s q ((Apr - A₀) u) ≤ Kpr * lam⁻¹ * p u)
    (hresponse : ∀ u, cNorm s q (Y u) ≤ Kresp * lam⁻¹ * p u) (u v : R) :
    cNorm s q (atomicDensityError (Apr - Y) A₀ u - atomicDensityError (Apr - Y) A₀ v) ≤
      (2 * (2 : ℝ) ^ q * (C₀ + Kpr + Kresp) * (Kpr + Kresp)) *
        lam⁻¹ * (p u + p v) * p (u - v) := by
  have hpos : 0 < lam := zero_lt_one.trans_le hlam
  have hinv : lam⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlam
  have hdiff (w : R) :
      cNorm s q (((Apr - Y) - A₀) w) ≤ (Kpr + Kresp) * lam⁻¹ * p w := by
    have he : ((Apr - Y) - A₀) w = (Apr - A₀) w - Y w := by
      simp only [LinearMap.sub_apply]
      abel
    rw [he]
    exact (cNorm_sub_le hs ((hApr w).sub (hA₀ w)) (hY w)).trans
      ((add_le_add (hprimary w) (hresponse w)).trans_eq (by ring))
  have htotal (w : R) : cNorm s q ((Apr - Y) w) ≤ (C₀ + Kpr + Kresp) * p w := by
    have he : (Apr - Y) w = A₀ w + ((Apr - Y) - A₀) w := by
      simp only [LinearMap.sub_apply]
      abel
    calc
      _ = cNorm s q (A₀ w + ((Apr - Y) - A₀) w) := congrArg (cNorm s q) he
      _ ≤ cNorm s q (A₀ w) + cNorm s q (((Apr - Y) - A₀) w) :=
        cNorm_add_le hs (hA₀ w) (((hApr w).sub (hY w)).sub (hA₀ w))
      _ ≤ C₀ * p w + (Kpr + Kresp) * lam⁻¹ * p w :=
        add_le_add (hleading w) (hdiff w)
      _ ≤ C₀ * p w + (Kpr + Kresp) * 1 * p w := by
        gcongr
        exact hp w
      _ = _ := by ring
  apply cNorm_atomicDensityError_sub_le (Apr - Y) A₀ hs
    (fun w ↦ (hApr w).sub (hY w)) hA₀ p hp
    (add_nonneg (add_nonneg hC₀ hKpr) hKresp) (add_nonneg hKpr hKresp) hpos
    htotal (fun w ↦ (hleading w).trans ?_) hdiff u v
  exact mul_le_mul_of_nonneg_right (by linarith) (hp w)

end JanetCartan.CorrectedAtoms
