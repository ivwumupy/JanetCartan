module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.OneHigh
public import JanetCartan.Analysis.ContDiff.Norm.Interpolation
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition.SmoothExtension

/-!
# Finite regularity interpolation for transport primitives

The consumer is the primitive profile input to the explicit masked transport
bounds of `app:ch_regular_base:eq:actual-one-high`. Only derivatives up to the
chosen finite top order are required. The adjacent-order and finite-sequence
arguments specialize `app:lem:elementary-interpolation-jets` to that finite range.
-/

@[expose] public noncomputable section
open scoped BigOperators ContDiff
namespace JanetCartan.FourierIntegral.TransportInterpolation
open CNormInterpolation

/-- Appendix B, `app:lem:elementary-interpolation-jets`: successive absorption
bounds an entry of a nonnegative sequence by its initial entry and an arbitrarily
small multiple of its next entry. The constant depends only on `C`, `n`, and `ε`. -/
private theorem exists_sequence_absorption_bound {C : ℝ} (hC : 0 < C) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ a : ℕ → ℝ, (∀ i, 0 ≤ a i) →
      (∀ i, i + 2 ≤ n + 1 → ∀ s : ℝ, 0 < s → s ≤ 1 →
        a (i + 1) ≤ C * (s⁻¹ * a i + s * a (i + 2))) →
      a n ≤ K * a 0 + ε * a (n + 1) := by
  induction n generalizing ε with
  | zero =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro a ha _
      simpa using (mul_nonneg hε.le (ha 1))
  | succ n ih =>
      let δ : ℝ := min 1 (ε / (2 * C))
      have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
      have hδ1 : δ ≤ 1 := min_le_left _ _
      have hδε : 2 * C * δ ≤ ε := by
        have h := min_le_right 1 (ε / (2 * C))
        have h' : δ * (2 * C) ≤ ε := (le_div_iff₀ (by positivity)).mp h
        nlinarith
      obtain ⟨K, hK, hbound⟩ := ih (ε := δ / (2 * C)) (by positivity)
      refine ⟨2 * C * δ⁻¹ * K, by positivity, ?_⟩
      intro a ha hadj
      have hprev := hbound a ha (fun i hi ↦ hadj i (by omega))
      have hnext := hadj n (by omega) δ hδ hδ1
      -- The previous-order estimate contributes exactly half the next entry.
      have hprev' := mul_le_mul_of_nonneg_left hprev (show 0 ≤ C * δ⁻¹ by positivity)
      have hcancel : C * δ⁻¹ * (δ / (2 * C)) = 1 / 2 := by
        field_simp
      have hsmall := mul_le_mul_of_nonneg_right hδε (ha (n + 2))
      rw [mul_add, ← mul_assoc (C * δ⁻¹) (δ / (2 * C)), hcancel] at hprev'
      change a (n + 1) ≤ 2 * C * δ⁻¹ * K * a 0 + ε * a (n + 2)
      nlinarith

/-- Appendix B, `app:lem:elementary-interpolation-jets`: iterating the absorption
bound controls an entry by the two endpoints, with a constant independent of the
nonnegative sequence. -/
private theorem exists_sequence_endpoint_bound {C : ℝ} (hC : 0 < C) (j d : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℕ → ℝ, (∀ i, 0 ≤ a i) →
      (∀ i, i + 2 ≤ j + d → ∀ s : ℝ, 0 < s → s ≤ 1 →
        a (i + 1) ≤ C * (s⁻¹ * a i + s * a (i + 2))) →
      a j ≤ A * (a 0 + a (j + d)) := by
  induction d generalizing j with
  | zero =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro a ha _
      simpa using (ha 0)
  | succ d ih =>
      obtain ⟨K, hK, hstep⟩ := exists_sequence_absorption_bound hC j zero_lt_one
      obtain ⟨A, hA, hbound⟩ := ih (j + 1)
      refine ⟨K + A, add_pos hK hA, ?_⟩
      intro a ha hadj
      have hs := hstep a ha (fun i hi ↦ hadj i (by omega))
      have hb := hbound a ha (fun i hi ↦ hadj i (by omega))
      have hind : j + 1 + d = j + (d + 1) := by omega
      rw [hind] at hb
      have hn := mul_nonneg hK.le (ha (j + (d + 1)))
      nlinarith

/-- Appendix B, `app:lem:elementary-interpolation-jets`: adjacent-order scale
estimates imply the arbitrary-order two-term scale estimate. The positive constant
is chosen uniformly before the nonnegative sequence and the scale `0 < t ≤ 1`.
No monotonicity premise or smaller scale cutoff is needed. -/
private theorem exists_sequence_scale_estimate {C : ℝ} (hC : 0 < C)
    {R j k : ℕ} (hRj : R < j) (hjk : j < k) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℕ → ℝ, (∀ n, 0 ≤ a n) →
      (∀ n, n + 2 ≤ k → ∀ s : ℝ, 0 < s → s ≤ 1 →
        a (n + 1) ≤ C * (s⁻¹ * a n + s * a (n + 2))) →
      ∀ t : ℝ, 0 < t → t ≤ 1 →
        a j ≤ A * (t ^ ((R : ℝ) - j) * a R + t ^ ((k : ℝ) - j) * a k) := by
  obtain ⟨A, hA, hbound⟩ := exists_sequence_endpoint_bound hC (j - R) (k - j)
  refine ⟨A, hA, ?_⟩
  intro a ha hadj t ht ht1
  -- Normalize the orders relative to the lower endpoint.
  let b : ℕ → ℝ := fun n ↦ t ^ n * a (R + n)
  have hb : ∀ n, 0 ≤ b n := fun n ↦ mul_nonneg (pow_nonneg ht.le n) (ha _)
  have hb_adj : ∀ n, n + 2 ≤ (j - R) + (k - j) → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      b (n + 1) ≤ C * (δ⁻¹ * b n + δ * b (n + 2)) := by
    intro n hn δ hδ hδ1
    have hδt : δ * t ≤ 1 := (mul_le_mul hδ1 ht1 ht.le zero_le_one).trans_eq (mul_one 1)
    have h := mul_le_mul_of_nonneg_left
      (hadj (R + n) (by omega) (δ * t) (mul_pos hδ ht) hδt) (pow_nonneg ht.le (n + 1))
    change t ^ (n + 1) * a (R + (n + 1)) ≤ _
    calc
      t ^ (n + 1) * a (R + (n + 1)) ≤
          t ^ (n + 1) * (C * ((δ * t)⁻¹ * a (R + n) +
            (δ * t) * a (R + n + 2))) := by simpa [Nat.add_assoc] using h
      _ = C * (δ⁻¹ * b n + δ * b (n + 2)) := by
        dsimp [b]
        simp only [pow_succ, Nat.add_assoc]
        field_simp
  have h := hbound b hb hb_adj
  have hsum : j - R + (k - j) = k - R := by omega
  have hRj' : R + (j - R) = j := Nat.add_sub_of_le hRj.le
  have hRk : R + (k - R) = k := Nat.add_sub_of_le (hRj.trans hjk).le
  simp only [b, hsum, hRj', hRk, pow_zero, Nat.add_zero, one_mul] at h
  have hp₀ : t ^ (j - R) * t ^ ((R : ℝ) - j) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht, Nat.cast_sub hRj.le]
    rw [show (j : ℝ) - R + ((R : ℝ) - j) = 0 by ring, Real.rpow_zero]
  have hp₁ : t ^ (j - R) * t ^ ((k : ℝ) - j) = t ^ (k - R) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht,
      ← Real.rpow_natCast, Nat.cast_sub hRj.le, Nat.cast_sub (hRj.trans hjk).le]
    congr 1
    ring
  apply (mul_le_mul_iff_right₀ (pow_pos ht (j - R))).mp
  calc
    t ^ (j - R) * a j ≤ A * (a R + t ^ (k - R) * a k) := h
    _ = t ^ (j - R) *
        (A * (t ^ ((R : ℝ) - j) * a R + t ^ ((k : ℝ) - j) * a k)) := by
      calc
        _ = A * ((t ^ (j - R) * t ^ ((R : ℝ) - j)) * a R +
            (t ^ (j - R) * t ^ ((k : ℝ) - j)) * a k) := by rw [hp₀, hp₁, one_mul]
        _ = _ := by ring

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]

private theorem derivativeSup_succ_le_finite (x : E) {ρ : ℝ} (hρ : 0 < ρ)
    {f : E → F} (n : ℕ) (hf : ContDiff ℝ (n + 2) f)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    derivativeSup (Metric.closedBall x ρ) (n + 1) f ≤
      2 / (t * ρ) * derivativeSup (Metric.closedBall x ρ) n f +
        5 * (t * ρ) * derivativeSup (Metric.closedBall x ρ) (n + 2) f := by
  have hg : ContDiff ℝ 2 (iteratedFDeriv ℝ n f) :=
    hf.iteratedFDeriv_right (by simp [add_comm])
  have hder (k : ℕ) (hk : k ≤ n + 2) (z : E) (hz : z ∈ Metric.closedBall x ρ) :
      ‖iteratedFDeriv ℝ k f z‖ ≤ derivativeSup (Metric.closedBall x ρ) k f :=
    le_csSup (bddAbove_norm_iteratedFDeriv (isCompact_closedBall x ρ) hf hk)
      (Set.mem_image_of_mem _ hz)
  apply csSup_le ((Metric.nonempty_closedBall.mpr hρ.le).image _)
  rintro _ ⟨z, hz, rfl⟩
  dsimp only
  rw [← norm_fderiv_iteratedFDeriv (𝕜 := ℝ) (f := f) (n := n)]
  apply norm_fderiv_le_of_closedBall hρ ht ht1 (hg.differentiable (by norm_num))
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num))
    (hder n (by omega)) ?_ hz
  intro y hy
  rw [norm_fderiv_fderiv_iteratedFDeriv]
  exact hder (n + 2) le_rfl y hy

private theorem cNorm_succ_le_scale_finite (x : E) {ρ : ℝ} (hρ : 0 < ρ)
    {f : E → F} (n : ℕ) (hf : ContDiff ℝ (n + 2) f) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    cNorm (Metric.closedBall x ρ) (n + 1) f ≤
      (1 + 2 / ρ + 5 * ρ) *
        (t⁻¹ * cNorm (Metric.closedBall x ρ) n f +
          t * cNorm (Metric.closedBall x ρ) (n + 2) f) := by
  let s := Metric.closedBall x ρ
  have hnonneg : ∀ i, 0 ≤ cNorm s i f := by
    intro i
    exact Finset.sum_nonneg (fun j _ ↦ derivativeSup_nonneg s j f)
  have hstep : cNorm s (n + 1) f = cNorm s n f + derivativeSup s (n + 1) f :=
    Finset.sum_range_succ _ _
  have hadj := derivativeSup_succ_le_finite x hρ n hf ht ht1
  have h₀ := derivativeSup_le_cNorm s f (n := n) (k := n) le_rfl
  have h₂ := derivativeSup_le_cNorm s f (n := n + 2) (k := n + 2) le_rfl
  have hlow : cNorm s n f ≤ t⁻¹ * cNorm s n f := by
    have hi : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
    simpa using mul_le_mul_of_nonneg_right hi (hnonneg n)
  have hb : cNorm s (n + 1) f ≤
      (1 + 2 / ρ) * (t⁻¹ * cNorm s n f) + 5 * ρ * (t * cNorm s (n + 2) f) := by
    rw [hstep]
    calc
      _ ≤ t⁻¹ * cNorm s n f +
          (2 / (t * ρ) * cNorm s n f + 5 * (t * ρ) * cNorm s (n + 2) f) := by
        apply add_le_add hlow
        exact hadj.trans (add_le_add (mul_le_mul_of_nonneg_left h₀ (by positivity))
          (mul_le_mul_of_nonneg_left h₂ (by positivity)))
      _ = _ := by field_simp; ring
  apply hb.trans
  have hA : 0 ≤ 1 + 2 / ρ := by positivity
  have hB : 0 ≤ 5 * ρ := by positivity
  have hL : 0 ≤ t⁻¹ * cNorm s n f := mul_nonneg (inv_nonneg.mpr ht.le) (hnonneg n)
  have hH : 0 ≤ t * cNorm s (n + 2) f := mul_nonneg ht.le (hnonneg (n + 2))
  dsimp [s] at *
  nlinarith [mul_nonneg hA hH, mul_nonneg hB hL]


/-- Exact finite-order closed-ball interpolation for the primitive profiles in
`app:ch_regular_base:eq:actual-one-high`. The constant is chosen before the map;
no derivatives above the finite top order `k` are assumed. -/
theorem exists_cNorm_interpolation_finite (x : E) {ρ : ℝ} (hρ : 0 < ρ)
    {R j k : ℕ} (hRj : R < j) (hjk : j < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : E → F, ContDiff ℝ k f →
      cNorm (Metric.closedBall x ρ) j f ≤
        C * (cNorm (Metric.closedBall x ρ) R f) ^ (1 - (j - R : ℝ) / (k - R)) *
          (cNorm (Metric.closedBall x ρ) k f) ^ ((j - R : ℝ) / (k - R)) := by
  obtain ⟨A, hA, hscale⟩ := exists_sequence_scale_estimate
    (C := 1 + 2 / ρ + 5 * ρ) (by positivity) hRj hjk
  refine ⟨A + A, by positivity, ?_⟩
  intro f hf
  have hp : 0 < (j - R : ℝ) := sub_pos.mpr (by exact_mod_cast hRj)
  have hq : 0 < (k - j : ℝ) := sub_pos.mpr (by exact_mod_cast hjk)
  have hsum : (j - R : ℝ) + (k - j : ℝ) = (k - R : ℝ) := by ring
  have h := le_mul_rpow_of_small_scale_bounds
    (cNorm_nonneg (Metric.closedBall x ρ) R f)
    (cNorm_mono_order (f := f) (s := Metric.closedBall x ρ) (hRj.trans hjk).le)
    hp hq (t₀ := 1) zero_lt_one (L := A) (H := A) (X := cNorm (Metric.closedBall x ρ) j f) (by
      intro t ht ht1
      have hb := hscale (fun n ↦ cNorm (Metric.closedBall x ρ) n f)
        (fun n ↦ cNorm_nonneg _ n f)
        (fun n hn s hs hs1 ↦ cNorm_succ_le_scale_finite x hρ n
          (hf.of_le (by exact_mod_cast hn)) hs hs1) t ht ht1
      simpa only [neg_sub, mul_add, mul_assoc] using hb)
  simpa only [neg_sub, hsum, Real.one_rpow, mul_one] using h

/-- The finite interpolation estimate on an open buffered chart. This supplies
the local interpolation used for transport primitives in
`app:ch_regular_base:lem:buffered-interpolation`. -/
theorem exists_cNorm_interpolation_finite_on (x : E) {ρ : ℝ} (hρ : 0 < ρ)
    {U : Set E} (hU : IsOpen U) (hball : Metric.closedBall x ρ ⊆ U)
    {R j k : ℕ} (hRj : R < j) (hjk : j < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : E → F, ContDiffOn ℝ k f U →
      cNorm (Metric.closedBall x ρ) j f ≤
        C * (cNorm (Metric.closedBall x ρ) R f) ^ (1 - (j - R : ℝ) / (k - R)) *
          (cNorm (Metric.closedBall x ρ) k f) ^ ((j - R : ℝ) / (k - R)) := by
  obtain ⟨C, hC, hb⟩ := exists_cNorm_interpolation_finite (F := F) x hρ hRj hjk
  refine ⟨C, hC, ?_⟩
  intro f hf
  obtain ⟨g, hg, _, _, hgf⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall x hρ hU hball hf
  have hnorm (r : ℕ) : cNorm (Metric.closedBall x ρ) r g =
      cNorm (Metric.closedBall x ρ) r f := by
    unfold cNorm
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Set.image_congr
    intro y hy
    rw [((hgf y hy).iteratedFDeriv (𝕜 := ℝ) i).self_of_nhds]
  simpa only [hnorm] using hb g hg

/-- Finite buffered low and high derivative bounds imply the exact primitive
profiles consumed by `MaskedProfiles`. Both the baseline `b` and the primitive
shift `σ` are fixed before the output derivative order. Only `b + W` derivatives
are required; no interpolation profile is a hypothesis. Source:
`app:ch_regular_base:lem:buffered-interpolation` and
`app:ch_regular_base:eq:actual-one-high`. -/
theorem exists_transportPrimitiveProfile_finite_on (x : E) {ρ : ℝ} (hρ : 0 < ρ)
    {U : Set E} (hU : IsOpen U) (hball : Metric.closedBall x ρ ⊆ U)
    (b W : ℕ) {B : ℝ} (hB : 1 ≤ B) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (f : E → F), ContDiffOn ℝ (b + W : ℕ) f U →
      ∀ H : ℝ, 1 ≤ H → cNorm (Metric.closedBall x ρ) b f ≤ B →
      cNorm (Metric.closedBall x ρ) (b + W) f ≤ H →
      ∀ k σ δ : ℕ, σ ≤ b + δ → k + δ ≤ W →
        cNorm (Metric.closedBall x ρ) (k + σ) f ≤
          (K * B) * H ^ (((k + δ : ℕ) : ℝ) / W) := by
  classical
  have hconstants : ∀ j : Fin (b + W + 1), ∃ C : ℝ, 1 ≤ C ∧
      ∀ f : E → F, ContDiffOn ℝ (b + W : ℕ) f U → b < j.val → j.val < b + W →
        cNorm (Metric.closedBall x ρ) j f ≤
          C * cNorm (Metric.closedBall x ρ) b f ^ (1 - ((j.val - b : ℕ) : ℝ) / W) *
            cNorm (Metric.closedBall x ρ) (b + W) f ^ (((j.val - b : ℕ) : ℝ) / W) := by
    intro j
    by_cases hj : b < j.val ∧ j.val < b + W
    · obtain ⟨C, hC, hb⟩ := exists_cNorm_interpolation_finite_on (F := F) x hρ hU hball hj.1 hj.2
      refine ⟨max 1 C, le_max_left _ _, ?_⟩
      intro f hf _ _
      have he : ((j.val : ℝ) - b) / ((b + W : ℕ) - b : ℝ) =
          ((j.val - b : ℕ) : ℝ) / W := by
        rw [Nat.cast_sub hj.1.le, Nat.cast_add, add_sub_cancel_left]
      have hi := hb f hf
      rw [he] at hi
      exact hi.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right 1 C) (Real.rpow_nonneg (cNorm_nonneg _ _ _) _))
        (Real.rpow_nonneg (cNorm_nonneg _ _ _) _))
    · exact ⟨1, le_rfl, fun _ _ h₁ h₂ ↦ (hj ⟨h₁, h₂⟩).elim⟩
  choose C hC hb using hconstants
  let K := 1 + ∑ j, C j
  have hK : 1 ≤ K := by
    dsimp [K]
    linarith [Finset.sum_nonneg (fun j _ ↦ zero_le_one.trans (hC j)) (s := Finset.univ)]
  refine ⟨K, hK, ?_⟩
  intro f hf H hH hlow hhigh k σ δ hσ hk
  apply transportPrimitiveProfile_of_interpolation (fun j ↦ cNorm (Metric.closedBall x ρ) j f)
    b σ δ W k B K H (fun j ↦ cNorm_nonneg _ j f)
    (fun _ _ hj ↦ cNorm_mono_order hj) hB hK hH hlow hhigh hσ hk
  intro hbj hjbW
  let j : Fin (b + W + 1) := ⟨k + σ, by omega⟩
  have hCK : C j ≤ K := by
    have := Finset.single_le_sum (fun i _ ↦ zero_le_one.trans (hC i)) (Finset.mem_univ j)
    dsimp [K]
    linarith
  exact (hb j f hf hbj hjbW).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCK (Real.rpow_nonneg (cNorm_nonneg _ _ _) _))
    (Real.rpow_nonneg (cNorm_nonneg _ _ _) _))

/-- Pointwise joint derivative profiles from finite buffered endpoint bounds.
This is the direct primitive input to the three concrete masked transport
estimates in `MaskedProfiles`, with zero additional primitive shift. Fixed jet
losses in the producers remain part of the coefficient index, independently of
the output order (`app:ch_regular_base:eq:actual-one-high`). -/
theorem exists_transportJointJetProfile_finite_on (x : E) {ρ : ℝ} (hρ : 0 < ρ)
    {U : Set E} (hU : IsOpen U) (hball : Metric.closedBall x ρ ⊆ U)
    (b W : ℕ) {B : ℝ} (hB : 1 ≤ B) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (f : E → F), ContDiffOn ℝ (b + W : ℕ) f U →
      ∀ H : ℝ, 1 ≤ H → cNorm (Metric.closedBall x ρ) b f ≤ B →
      cNorm (Metric.closedBall x ρ) (b + W) f ≤ H →
      ∀ k ≤ W, ∀ p ∈ Metric.closedBall x ρ,
        ‖iteratedFDeriv ℝ k f p‖ ≤ (K * B) * H ^ ((k : ℝ) / W) := by
  obtain ⟨K, hK, hprofile⟩ := exists_transportPrimitiveProfile_finite_on
    (F := F) x hρ hU hball b W hB
  refine ⟨K, hK, ?_⟩
  intro f hf H hH hlow hhigh k hk p hp
  have hlocal (y : E) (hy : y ∈ Metric.closedBall x ρ) : ContDiffAt ℝ k f y :=
    (hf.contDiffAt (hU.mem_nhds (hball hy))).of_le (by exact_mod_cast (show k ≤ b + W by omega))
  apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt
    (isCompact_closedBall x ρ) hlocal hp le_rfl).trans
  simpa only [Nat.add_zero] using hprofile f hf H hH hlow hhigh k 0 0 (by omega) hk

end JanetCartan.FourierIntegral.TransportInterpolation
