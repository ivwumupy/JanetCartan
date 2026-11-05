module

public import JanetCartan.Iteration.PhysicalHistory.Increments

/-!
# Uniform Euclidean finite-history estimates

For every admissible physical prefix in `main:lem:history` (paper-v2 §16),
the actual `G + ∑ i, Uᵢ` stays in a prescribed `C^{r_*}` ball once the initial
scale is sufficiently large. At *every* order its seminorm on the chart costs
only `Tⱼ ^ (r - r_*)`, with constants fixed before the scale, history and stage.

There is no second derivative loss: apply the physical L² Bernstein inequality
to each increment at order `r`, split off the baseline decay, and use
`Rᵢ ^ b_* ≤ Tⱼ` only on the excess derivatives when `i < j`. All summands below
are actual entries of the finite prefix. There is no periodization and no
analytic assumption beyond its physical band and L² budgets.
-/

@[expose] public noncomputable section

open Filter
open scoped ContDiff Topology

namespace JanetCartan.PhysicalHistory

open RevisedConvergence

variable {n N j rStar kMin : ℕ} {B R₀ : ℝ}
  {u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)} {ell : Fin j → ℕ}

-- The paper's μ is kMin minus the literal revised derivative loss at rStar.
private theorem margin_pos (horder : RevisedScales.displacementLoss n +
    bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    0 < (kMin : ℝ) - derivativeLoss n rStar := by
  unfold derivativeLoss
  linarith

-- The extra exponent relative to the summable baseline is at most b_*(r-r_*)₊.
private theorem split_power {R : ℝ} (hR : 1 ≤ R) {k : ℕ} (hk : kMin ≤ k) (r : ℕ) :
    R ^ (-(k : ℝ) + derivativeLoss n r) ≤
      (R ^ bandExponent) ^ (r - rStar) * R ^ (-((kMin : ℝ) - derivativeLoss n rStar)) := by
  have hRpos := zero_lt_one.trans_le hR
  rw [← Real.rpow_mul_natCast hRpos.le, ← Real.rpow_add hRpos]
  apply Real.rpow_le_rpow_of_exponent_le hR
  have hr : (r : ℝ) ≤ (rStar : ℝ) + ((r - rStar : ℕ) : ℝ) := by
    exact_mod_cast (show r ≤ rStar + (r - rStar) by omega)
  have hb := mul_le_mul_of_nonneg_left hr (by norm_num [bandExponent] : 0 ≤ bandExponent)
  have hk' : (kMin : ℝ) ≤ k := Nat.cast_le.mpr hk
  unfold derivativeLoss
  linarith

-- Choosing S = 2 gives a uniform high-order constant; S = R₀ gives an
-- explicit low-order majorant tending to zero with R₀.
private theorem sum_decay_le (j : ℕ) {S R₀ μ : ℝ} (hS : 1 < S) (hSR : S ≤ R₀) (hμ : 0 < μ) :
    (∑ i : Fin j, iterationScale R₀ growthExponent i.val ^ (-μ)) ≤ historyBound 1 S growthExponent μ := by
  let a (i : ℕ) := iterationScale R₀ growthExponent i ^ (-μ)
  have hv : 1 < growthExponent := by norm_num [growthExponent]
  have hSpos := zero_lt_one.trans hS
  have ha (i : ℕ) : 0 ≤ a i :=
    Real.rpow_nonneg (Real.rpow_nonneg (hSpos.le.trans hSR) _) _
  have hbound (i : ℕ) : a i ≤ 1 * historyScale S growthExponent i ^ (-μ) := by
    simpa only [a, one_mul, iterationScale, historyScale] using historyScale_neg_pow_antitone hSpos hSR
      (zero_le_one.trans hv.le) hμ.le i
  calc
    _ = ∑ i ∈ Finset.range j, a i := Fin.sum_univ_eq_sum_range a j
    _ ≤ ∑' i, a i := (summable_of_history_bound hS hv hμ zero_le_one ha hbound).sum_le_tsum
      _ (fun i _ ↦ ha i)
    _ ≤ _ := tsum_le_historyBound hS hv hμ zero_le_one ha hbound

private theorem sum_prefix_profile_le (hu : RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell)
    (hB : 1 ≤ B) {S : ℝ} (hS : 1 < S) (hSR : S ≤ R₀)
    (hμ : 0 < (kMin : ℝ) - derivativeLoss n rStar) (K : Set (Euclidean n)) (r : ℕ) :
    (∑ i : Fin j, cNorm K r (u i)) ≤
      (seminormConstant n r B * historyBound 1 S growthExponent ((kMin : ℝ) - derivativeLoss n rStar)) *
        currentCoefficientScale R₀ j ^ (r - rStar) := by
  let μ := (kMin : ℝ) - derivativeLoss n rStar
  let C := seminormConstant n r B
  let T := currentCoefficientScale R₀ j
  let R := iterationScale R₀ growthExponent
  have hR₀ := hS.le.trans hSR
  have hC : 0 ≤ C := seminormConstant_nonneg n r (zero_le_one.trans hB)
  have hT : 0 ≤ T := zero_le_one.trans (one_le_currentCoefficientScale hR₀ j)
  have ht (i : Fin j) : cNorm K r (u i) ≤ (C * T ^ (r - rStar)) * R i.val ^ (-μ) := by
    have hR : 1 ≤ R i.val := one_le_scale hR₀ i.val
    have hband : R i.val ^ bandExponent ≤ T := by
      simpa only [R, T, currentCoefficientScale, scale_windows.2.2.1, iterationScale, historyScale] using historyScale_band_le
        hR₀ (by norm_num [growthExponent] : 1 ≤ growthExponent)
        (by norm_num [bandExponent] : 0 ≤ bandExponent) i.isLt
    calc
      _ ≤ C * R i.val ^ (-(ell i : ℝ) + derivativeLoss n r) :=
        cNorm_prefix_increment_le hu hB hR₀ K r i
      _ ≤ C * ((R i.val ^ bandExponent) ^ (r - rStar) * R i.val ^ (-μ)) :=
        mul_le_mul_of_nonneg_left (split_power hR (hu i).1 r) hC
      _ ≤ C * (T ^ (r - rStar) * R i.val ^ (-μ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (Real.rpow_nonneg (zero_le_one.trans hR) _) hband _)
          (Real.rpow_nonneg (zero_le_one.trans hR) _)) hC
      _ = _ := (mul_assoc ..).symm
  calc
    _ ≤ ∑ i : Fin j, (C * T ^ (r - rStar)) * R i.val ^ (-μ) := Finset.sum_le_sum (fun i _ ↦ ht i)
    _ = (C * T ^ (r - rStar)) * ∑ i : Fin j, R i.val ^ (-μ) := (Finset.mul_sum ..).symm
    _ ≤ (C * T ^ (r - rStar)) * historyBound 1 S growthExponent μ :=
      mul_le_mul_of_nonneg_left (sum_decay_le j hS hSR hμ) (mul_nonneg hC (pow_nonneg hT _))
    _ = _ := by change _ = (C * historyBound 1 S growthExponent μ) * T ^ (r - rStar); ring

/-- `main:eq:history-bernstein`, `new:eq:geometric-sum`: the explicit geometric
bound for the *total* low-order displacement of the actual prefix. The physical
set can be all of `ℝⁿ`. In particular no global boundedness is inferred from a
default value of a supremum: the summands have genuine pointwise Bernstein bounds. -/
theorem sum_prefix_baseline_le (hu : RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell)
    (hB : 1 ≤ B) (hR₀ : 2 ≤ R₀) (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) (K : Set (Euclidean n)) :
    (∑ i : Fin j, cNorm K rStar (u i)) ≤
      historyBound (seminormConstant n rStar B) R₀ growthExponent ((kMin : ℝ) - derivativeLoss n rStar) := by
  have hs := sum_prefix_profile_le hu hB (S := R₀) (by linarith) le_rfl (margin_pos horder) K rStar
  simp only [Nat.sub_self, pow_zero, mul_one] at hs
  exact hs.trans_eq (by unfold historyBound; ring)

/-- `main:eq:displacement-budget`: one initial frequency threshold puts *every*
admissible physical prefix inside the prescribed reference neighborhood. It
precedes the compact set, reference map, length, increments and their orders. -/
theorem exists_initialScale_for_prefix_neighborhood {ε : ℝ}
    (hB : 1 ≤ B) (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) (hε : 0 < ε) :
    ∃ Tref : ℝ, 2 ≤ Tref ∧ ∀ R₀ ≥ Tref, ∀ (K : Set (Euclidean n)) (G : Euclidean n → Euclidean N),
      IsCompact K → ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)) (ell : Fin j → ℕ),
      RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
      cNorm K rStar (RevisedGlobal.finiteMap G u - G) < ε / 2 := by
  have hev := (tendsto_historyBound (seminormConstant n rStar B)
    (by norm_num [growthExponent] : 1 < growthExponent) (margin_pos horder)).eventually
      (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
  obtain ⟨S, hS⟩ := eventually_atTop.1 hev
  refine ⟨max 2 S, le_max_left _ _, ?_⟩
  intro R₀ hR K G hK j u ell hu
  have heq : RevisedGlobal.finiteMap G u - G = fun x ↦ ∑ i, u i x := by
    funext x
    simp only [Pi.sub_apply, RevisedGlobal.finiteMap, add_sub_cancel_left]
  rw [heq]
  apply (cNorm_sum_le (f := fun i ↦ ⇑(u i)) Finset.univ hK (fun i _ ↦ (u i).smooth rStar)).trans_lt
  exact (sum_prefix_baseline_le hu hB ((le_max_left _ _).trans hR) horder K).trans_lt
    (hS R₀ ((le_max_right _ _).trans hR))

/-- `main:eq:history-current` at *all* orders, uniformly over all scales and
admissible physical prefixes of one fixed reference. The exact current map and
coefficient scale are those consumed by `main:prop:current-scale`.
Smoothness of `G` is only needed near the compact chart closure `K`. -/
theorem exists_prefix_derivative_profile {K : Set (Euclidean n)} (hK : IsCompact K)
    {G : Euclidean n → Euclidean N} (hG : ∀ x ∈ K, ContDiffAt ℝ ∞ G x)
    (hB : 1 ≤ B) (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ A : ℕ → ℝ, (∀ r, 0 ≤ A r) ∧ ∀ R₀ : ℝ, 2 ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)) (ell : Fin j → ℕ),
      RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell → ∀ W ⊆ K,
      HasDerivativeProfile W (RevisedGlobal.finiteMap G u) rStar (currentCoefficientScale R₀ j) A := by
  let μ := (kMin : ℝ) - derivativeLoss n rStar
  let M := historyBound 1 2 growthExponent μ
  have hμ : 0 < μ := margin_pos horder
  have hM : 0 ≤ M := div_nonneg (mul_nonneg zero_le_one (Real.rpow_nonneg (by norm_num) _))
    (sub_nonneg.mpr (history_ratio_lt_one (by norm_num : (1 : ℝ) < 2)
      (by norm_num [growthExponent] : 1 < growthExponent) hμ).le)
  refine ⟨fun r ↦ cNorm K r G + seminormConstant n r B * M,
    fun r ↦ add_nonneg (cNorm_nonneg K r G) (mul_nonneg
      (seminormConstant_nonneg n r (zero_le_one.trans hB)) hM), ?_⟩
  intro R₀ hR j u ell hu W hWK r
  let V := fun x ↦ ∑ i, u i x
  let T := currentCoefficientScale R₀ j
  have hV : ContDiff ℝ r V := ContDiff.sum (fun i _ ↦ (u i).smooth r)
  have hGr (x : Euclidean n) (hx : x ∈ K) := (hG x hx).of_le (show (r : WithTop ℕ∞) ≤ ∞ by simp)
  have hT : 1 ≤ T ^ (r - rStar) := one_le_pow₀ (one_le_currentCoefficientScale (by linarith) j)
  calc
    _ ≤ cNorm K r (RevisedGlobal.finiteMap G u) :=
      cNorm_mono_set_of_contDiffAt hWK hK (fun x hx ↦ (hGr x hx).add hV.contDiffAt)
    _ ≤ cNorm K r G + cNorm K r V :=
      cNorm_add_le_of_contDiffAt hK hGr (fun _ _ ↦ hV.contDiffAt)
    _ ≤ cNorm K r G + ∑ i : Fin j, cNorm K r (u i) := add_le_add le_rfl
      (cNorm_sum_le (f := fun i ↦ ⇑(u i)) Finset.univ hK (fun i _ ↦ (u i).smooth r))
    _ ≤ cNorm K r G * T ^ (r - rStar) + (seminormConstant n r B * M) * T ^ (r - rStar) :=
      add_le_add (le_mul_of_one_le_right (cNorm_nonneg K r G) hT)
        (sum_prefix_profile_le hu hB (S := 2) (by norm_num) hR hμ K r)
    _ = _ := (add_mul ..).symm

end JanetCartan.PhysicalHistory
