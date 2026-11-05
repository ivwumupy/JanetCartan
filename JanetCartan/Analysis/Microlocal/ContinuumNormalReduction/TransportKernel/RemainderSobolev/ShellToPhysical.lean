module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.ShellBounds
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.Coordinates

/-!
# Physical derivative budgets from the actual remainder's shell bounds

The conversion needed by the gain-one estimates following
`app:ch_background:eq:bg-real-symbol`. The small-frequency bound is separate:
`HasAmplitudeShellBound` gives no information below frequency one.
-/

@[expose] public noncomputable section
open scoped ContDiff
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
namespace JanetCartan.ContinuumRow.TransportKernel
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "P" => EuclideanSpace ℝ (Fin (2 * n))

/-- Embed the two physical positions, with zero frequency tangent, for the
remainder estimate following `app:ch_background:eq:bg-real-symbol`. -/
def remainderPhysicalInclusion (L : P →L[ℝ] E × E) : P →L[ℝ] E × E × E :=
  ((ContinuousLinearMap.fst ℝ E E).comp L).prod
    (((ContinuousLinearMap.snd ℝ E E).comp L).prod 0)

private theorem physical_jet_le (L : P →L[ℝ] E × E)
    (f : E × E × E → ℂ) (hf : ContDiff ℝ ∞ f) (ξ : E) (k : ℕ) (z : P) :
    ‖iteratedFDeriv ℝ k (fun w ↦ f ((L w).1, (L w).2, ξ)) z‖ ≤
      ‖iteratedFDeriv ℝ k f ((L z).1, (L z).2, ξ)‖ *
        ‖remainderPhysicalInclusion L‖ ^ k := by
  have h := norm_iteratedFDeriv_comp_linear_le (remainderPhysicalInclusion L)
    (fun p ↦ f ((0, 0, ξ) + p)) (hf.comp (contDiff_const.add contDiff_id)) k z
  simpa [Function.comp_def, remainderPhysicalInclusion, iteratedFDeriv_comp_add_left'] using h

/-- Shell order minus one controls physical derivatives at every frequency
of norm at least one. This is the high-frequency half of the weighted budget
consumed by `IntegerBounds`, following `app:ch_background:eq:bg-real-symbol`. -/
theorem weighted_physical_jet_le_of_shell
    (c : E → E → E → ℂ)
    (hc : ContDiff ℝ ∞ (fun p : E × E × E ↦ c p.1 p.2.1 p.2.2))
    (L : P →L[ℝ] E × E) (r : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hs : HasAmplitudeShellBound c (-1) r A)
    (ξ : E) (hξ : 1 ≤ ‖ξ‖) (k : ℕ) (hk : k ≤ r) (z : P) :
    (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ k (fun w ↦ c (L w).1 (L w).2 ξ) z‖ ≤
      2 * A * max 1 ‖remainderPhysicalInclusion L‖ ^ r := by
  have hpos : 0 < ‖ξ‖ := lt_of_lt_of_le zero_lt_one hξ
  have hunit : ‖‖ξ‖⁻¹ • ξ‖ = 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
  let f : E × E × E → ℂ := fun q ↦ c q.1 q.2.1 (‖ξ‖ • q.2.2)
  have hf : ContDiff ℝ ∞ f := hc.comp
    (contDiff_fst.prodMk (contDiff_snd.fst.prodMk (contDiff_snd.snd.const_smul ‖ξ‖)))
  have hb := hs ‖ξ‖ hξ ((L z).1, (L z).2, ‖ξ‖⁻¹ • ξ)
    (by simp only [hunit, le_refl]) (by simp only [hunit]; norm_num) k hk
  have hp := physical_jet_le L f hf (‖ξ‖⁻¹ • ξ) k z
  have hcancel : ‖ξ‖ • (‖ξ‖⁻¹ • ξ) = ξ := by
    rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  simp only [f, hcancel] at hp
  have hpow : ‖remainderPhysicalInclusion L‖ ^ k ≤
      max 1 ‖remainderPhysicalInclusion L‖ ^ r := by
    exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hk)
  have hb' : ‖iteratedFDeriv ℝ k f ((L z).1, (L z).2, ‖ξ‖⁻¹ • ξ)‖ ≤
      ‖ξ‖⁻¹ * A := by simpa only [Real.rpow_neg_one] using hb
  calc
    _ ≤ (1 + ‖ξ‖) * ((‖ξ‖⁻¹ * A) * ‖remainderPhysicalInclusion L‖ ^ k) :=
      mul_le_mul_of_nonneg_left (hp.trans
        (mul_le_mul_of_nonneg_right hb' (by positivity))) (by positivity)
    _ ≤ (1 + ‖ξ‖) * ((‖ξ‖⁻¹ * A) * max 1 ‖remainderPhysicalInclusion L‖ ^ r) := by
      gcongr
    _ = ((1 + ‖ξ‖) / ‖ξ‖) * A * max 1 ‖remainderPhysicalInclusion L‖ ^ r := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hA
      exact (div_le_iff₀ hpos).mpr (by linarith)

/-- Combine the shell estimate with a separate low-frequency joint bound.
The result is exactly the weighted coordinate budget of `IntegerBounds`.
The low-frequency premise will be produced from the original amplitude's
mixed jets, with the Taylor shift two; it is not implied by a shell bound.
Source: the error paragraph following `app:ch_background:eq:bg-real-symbol`. -/
theorem weighted_physical_jet_le_of_shell_and_low
    (c : E → E → E → ℂ)
    (hc : ContDiff ℝ ∞ (fun p : E × E × E ↦ c p.1 p.2.1 p.2.2))
    (L : P →L[ℝ] E × E) (r : ℕ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : HasAmplitudeShellBound c (-1) r A)
    (hlow : ∀ p : E × E × E, ‖p.2.2‖ ≤ 1 → ∀ k ≤ r,
      ‖iteratedFDeriv ℝ k (fun q : E × E × E ↦ c q.1 q.2.1 q.2.2) p‖ ≤ B) :
    ∀ ξ k, k ≤ r → ∀ z,
      (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ k
        (fun w ↦ c (L w).1 (L w).2 ξ) z‖ ≤
      2 * max A B * max 1 ‖remainderPhysicalInclusion L‖ ^ r := by
  intro ξ k hk z
  by_cases hξ : 1 ≤ ‖ξ‖
  · exact (weighted_physical_jet_le_of_shell c hc L r hA hs ξ hξ k hk z).trans
      (by gcongr; exact le_max_left _ _)
  · have hj := physical_jet_le L _ hc ξ k z
    have hb := hlow ((L z).1, (L z).2, ξ) (le_of_not_ge hξ) k hk
    have hpow : ‖remainderPhysicalInclusion L‖ ^ k ≤
        max 1 ‖remainderPhysicalInclusion L‖ ^ r :=
      (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) hk)
    calc
      _ ≤ (1 + ‖ξ‖) * (B * ‖remainderPhysicalInclusion L‖ ^ k) :=
        mul_le_mul_of_nonneg_left (hj.trans
          (mul_le_mul_of_nonneg_right hb (by positivity))) (by positivity)
      _ ≤ 2 * (max A B * max 1 ‖remainderPhysicalInclusion L‖ ^ r) := by
        apply mul_le_mul (by linarith [le_of_not_ge hξ]) _ (by positivity) (by positivity)
        exact mul_le_mul (le_max_right _ _) hpow (by positivity) (hB.trans (le_max_right _ _))
      _ = _ := by ring

/-- Ordered coordinate version of the physical-jet conversion, supplying
exactly the weighted budget in `IntegerBounds` for the error following
`app:ch_background:eq:bg-real-symbol`. -/
theorem weighted_coordinate_budget_of_shell_and_low
    (c : E → E → E → ℂ)
    (hc : ContDiff ℝ ∞ (fun p : E × E × E ↦ c p.1 p.2.1 p.2.2))
    (L : P →L[ℝ] E × E) (r : ℕ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : HasAmplitudeShellBound c (-1) r A)
    (hlow : ∀ p : E × E × E, ‖p.2.2‖ ≤ 1 → ∀ k ≤ r,
      ‖iteratedFDeriv ℝ k (fun q : E × E × E ↦ c q.1 q.2.1 q.2.2) p‖ ≤ B) :
    ∀ ξ is, is.length ≤ r → ∀ z,
      (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is
        (fun w ↦ c (L w).1 (L w).2 ξ) z‖ ≤
      2 * max A B * max 1 ‖remainderPhysicalInclusion L‖ ^ r := by
  intro ξ is hi z
  have hcoord := norm_euclideanCoordinateDerivList_le_iteratedFDeriv
    (hc.comp (((ContinuousLinearMap.fst ℝ E E).comp L).contDiff.prodMk
      (((ContinuousLinearMap.snd ℝ E E).comp L).contDiff.prodMk
        (contDiff_const (c := ξ))))) is z
  exact (mul_le_mul_of_nonneg_left hcoord (by positivity)).trans
    (weighted_physical_jet_le_of_shell_and_low c hc L r hA hB hs hlow ξ is.length hi z)

end JanetCartan.ContinuumRow.TransportKernel
