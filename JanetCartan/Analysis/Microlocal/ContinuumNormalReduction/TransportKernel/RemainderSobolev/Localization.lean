module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.RemainderSobolev.ShellToPhysical

/-!
# Fixed physical cutoffs for the actual remainder

Both physical cutoff jets are retained in the weighted derivative budgets
used by the Sobolev estimate following `app:ch_background:eq:bg-real-symbol`.
-/

@[expose] public noncomputable section
open scoped ContDiff
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
namespace JanetCartan.ContinuumRow.TransportKernel
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "P" => EuclideanSpace ℝ (Fin (2 * n))

/-- The localized amplitude used for the error following
`app:ch_background:eq:bg-real-symbol`, retaining output and source cutoffs. -/
def localizedRemainderAmplitude (L : P →L[ℝ] E × E)
    (c : E → E → E → ℂ) (α γ : E → ℝ) (ξ : E) (z : P) : ℂ :=
  α (L z).1 • (γ (L z).2 • c (L z).1 (L z).2 ξ)

/-- Joint smoothness of the literal localized amplitude in the error paragraph
following `app:ch_background:eq:bg-real-symbol`. -/
theorem contDiff_localizedRemainderAmplitude (L : P →L[ℝ] E × E)
    (c : E → E → E → ℂ) (α γ : E → ℝ)
    (hc : ContDiff ℝ ∞ (fun p : E × E × E ↦ c p.1 p.2.1 p.2.2))
    (hα : ContDiff ℝ ∞ α) (hγ : ContDiff ℝ ∞ γ) :
    ContDiff ℝ ∞ (Function.uncurry (localizedRemainderAmplitude L c α γ)) :=
  (hα.comp (L.contDiff.comp contDiff_snd).fst).smul
    ((hγ.comp (L.contDiff.comp contDiff_snd).snd).smul
      (hc.comp ((L.contDiff.comp contDiff_snd).fst.prodMk
        ((L.contDiff.comp contDiff_snd).snd.prodMk contDiff_fst))))

private theorem weighted_smul_jet_le (χ : P → ℝ) (f : P → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (r : ℕ) {B A w : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hw : 0 ≤ w)
    (hχb : ∀ k ≤ r, ∀ z, ‖iteratedFDeriv ℝ k χ z‖ ≤ B)
    (hfb : ∀ k ≤ r, ∀ z, w * ‖iteratedFDeriv ℝ k f z‖ ≤ A)
    (k : ℕ) (hk : k ≤ r) (z : P) :
    w * ‖iteratedFDeriv ℝ k (fun z ↦ χ z • f z) z‖ ≤ 2 ^ r * B * A := by
  calc
    _ ≤ w * ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j χ z‖ * ‖iteratedFDeriv ℝ (k - j) f z‖ :=
      mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_smul_le hχ hf z (by simp)) hw
    _ = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j χ z‖ * (w * ‖iteratedFDeriv ℝ (k - j) f z‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * B * A := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul
        (mul_le_mul_of_nonneg_left (hχb j (by have := Finset.mem_range.mp hj; omega) z)
          (Nat.cast_nonneg _))
        (hfb (k - j) (by omega) z) (by positivity) (by positivity)
    _ = 2 ^ k * B * A := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose k
    _ ≤ _ := by gcongr; norm_num

private theorem cutoff_comp_jet_le (L : P →L[ℝ] E)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (r : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ k ≤ r, ∀ z, ‖iteratedFDeriv ℝ k χ z‖ ≤ B) :
    ∀ k ≤ r, ∀ z, ‖iteratedFDeriv ℝ k (χ ∘ L) z‖ ≤ B * max 1 ‖L‖ ^ r := by
  intro k hk z
  apply (norm_iteratedFDeriv_comp_linear_le L χ hχ k z).trans
  exact mul_le_mul (hb k hk _)
    ((pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hk)) (by positivity) hB

/-- Explicit fixed-cutoff multiplier for the weighted budget in
`app:ch_background:eq:bg-real-symbol`. There is no amplitude norm in it. -/
def remainderLocalizationConstant (L : P →L[ℝ] E × E) (r : ℕ) (Bα Bγ : ℝ) : ℝ :=
  (2 ^ r * (Bα * max 1 ‖(ContinuousLinearMap.fst ℝ E E).comp L‖ ^ r)) *
    (2 ^ r * (Bγ * max 1 ‖(ContinuousLinearMap.snd ℝ E E).comp L‖ ^ r)) *
    (2 * max 1 ‖remainderPhysicalInclusion L‖ ^ r)

/-- Fixed smooth output/source cutoffs preserve the order-minus-one weighted
coordinate budget. The high and low frequency bounds are supplied separately;
`PrimitiveBounds` produces both for the original reflected Taylor remainder.
Source: the error paragraph following `app:ch_background:eq:bg-real-symbol`. -/
theorem weighted_coordinate_budget_localizedRemainderAmplitude
    (L : P →L[ℝ] E × E) (c : E → E → E → ℂ) (α γ : E → ℝ)
    (hc : ContDiff ℝ ∞ (fun p : E × E × E ↦ c p.1 p.2.1 p.2.2))
    (hα : ContDiff ℝ ∞ α) (hγ : ContDiff ℝ ∞ γ)
    (r : ℕ) {Bα Bγ A B : ℝ} (hBα : 0 ≤ Bα) (hBγ : 0 ≤ Bγ)
    (hαb : ∀ k ≤ r, ∀ x, ‖iteratedFDeriv ℝ k α x‖ ≤ Bα)
    (hγb : ∀ k ≤ r, ∀ y, ‖iteratedFDeriv ℝ k γ y‖ ≤ Bγ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : HasAmplitudeShellBound c (-1) r A)
    (hlow : ∀ p : E × E × E, ‖p.2.2‖ ≤ 1 → ∀ k ≤ r,
      ‖iteratedFDeriv ℝ k (fun q : E × E × E ↦ c q.1 q.2.1 q.2.2) p‖ ≤ B) :
    ∀ ξ is, is.length ≤ r → ∀ z,
      (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is
        (localizedRemainderAmplitude L c α γ ξ) z‖ ≤
      remainderLocalizationConstant L r Bα Bγ * max A B := by
  intro ξ is hi z
  let Lx := (ContinuousLinearMap.fst ℝ E E).comp L
  let Ly := (ContinuousLinearMap.snd ℝ E E).comp L
  have hf : ContDiff ℝ ∞ (fun w : P ↦ c (L w).1 (L w).2 ξ) :=
    hc.comp (L.contDiff.fst.prodMk (L.contDiff.snd.prodMk contDiff_const))
  have hw := weighted_physical_jet_le_of_shell_and_low c hc L r hA hB hs hlow ξ
  have hy := weighted_smul_jet_le (γ ∘ Ly) _ (hγ.comp Ly.contDiff) hf r
    (mul_nonneg hBγ (by positivity)) (by positivity) (by positivity : 0 ≤ 1 + ‖ξ‖)
    (cutoff_comp_jet_le Ly γ hγ r hBγ hγb) hw
  have hx := weighted_smul_jet_le (α ∘ Lx) _ (hα.comp Lx.contDiff)
    ((hγ.comp Ly.contDiff).smul hf) r
    (mul_nonneg hBα (by positivity)) (by positivity) (by positivity : 0 ≤ 1 + ‖ξ‖)
    (cutoff_comp_jet_le Lx α hα r hBα hαb) hy is.length hi z
  have hsmooth := (contDiff_localizedRemainderAmplitude L c α γ hc hα hγ).comp
    (contDiff_const (c := ξ) |>.prodMk contDiff_id)
  apply (mul_le_mul_of_nonneg_left
    (norm_euclideanCoordinateDerivList_le_iteratedFDeriv hsmooth is z) (by positivity)).trans
  exact hx.trans_eq (by dsimp [remainderLocalizationConstant, Lx, Ly]; ring)

end JanetCartan.ContinuumRow.TransportKernel
