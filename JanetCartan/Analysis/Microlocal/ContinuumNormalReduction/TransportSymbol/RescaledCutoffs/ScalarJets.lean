module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.PrimitiveNorms
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.FrequencyBounds.RadialCutoff

/-!
# Scalar mask jets after dilation

The fixed scalar masks supply the primitive profiles for the rescaled transport
amplitude in `app:ch_background:prop:bg-frame`, Step 1. Weighted derivatives
absorb arbitrary nonnegative dilations on a positive radial shell.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol

/-- Weighted scalar jets of a fixed smooth mask constant on a positive tail.
Consumed by the high and regularization mask dilation bounds for
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem exists_weighted_scalarMask_bound {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {b c : ℝ} (htail : ∀ x, b ≤ x → f x = c) (j : ℕ) :
    ∃ C > 0, ∀ x : ℝ, 0 ≤ x → ‖iteratedFDeriv ℝ j f x‖ * x ^ j ≤ C := by
  have hcont : Continuous (fun x : ℝ ↦ ‖iteratedFDeriv ℝ j f x‖ * x ^ j) :=
    (hf.continuous_iteratedFDeriv (by simp)).norm.mul (continuous_id.pow j)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) (max 0 b + 1)) hcont.continuousOn
  refine ⟨1 + |C| + ‖c‖, by positivity, ?_⟩
  intro x hx
  by_cases hxb : x ≤ max 0 b + 1
  · have hb := (le_abs_self _).trans (hC x ⟨hx, hxb⟩)
    simpa only [Real.norm_eq_abs] using hb.trans (show C ≤ 1 + |C| + ‖c‖ by
      linarith [le_abs_self C, norm_nonneg c])
  · have hbx : b < x := lt_of_le_of_lt (le_max_right 0 b)
      (by linarith [lt_of_not_ge hxb])
    have he : f =ᶠ[𝓝 x] (fun _ ↦ c) := by
      filter_upwards [Ioi_mem_nhds hbx] with y hy
      exact htail y hy.le
    rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
    by_cases hj : j = 0
    · subst j
      simp only [norm_iteratedFDeriv_zero, pow_zero, mul_one]
      linarith [abs_nonneg C]
    · simp only [iteratedFDeriv_const_of_ne hj, Pi.zero_apply, norm_zero, zero_mul]
      positivity

/-- All finite scalar jets of a dilated fixed mask are uniformly bounded on
`r ≥ ε`. The constant precedes the dilation, and hence also `t/R`.
Source: `app:ch_background:prop:bg-frame`, Step 1. -/
theorem exists_scalarMask_dilation_jet_bound {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {b c : ℝ} (htail : ∀ x, b ≤ x → f x = c) {ε : ℝ} (hε : 0 < ε) (s : ℕ) :
    ∃ C > 0, ∀ (a : ℝ), 0 ≤ a → ∀ r : ℝ, ε ≤ r → ∀ j ≤ s,
      ‖iteratedFDeriv ℝ j (fun y ↦ f (a * y)) r‖ ≤ C := by
  have hb (j : ℕ) := exists_weighted_scalarMask_bound hf htail j
  choose B hB hbound using hb
  let C := 1 + ∑ j ∈ Finset.range (s + 1), B j / ε ^ j
  have hterm (j : ℕ) : 0 ≤ B j / ε ^ j :=
    div_nonneg (hB j).le (pow_nonneg hε.le j)
  refine ⟨C, by
    dsimp [C]
    linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (s + 1)) ↦ hterm j)], ?_⟩
  intro a ha r hr j hj
  have hrpos : 0 < r := hε.trans_le hr
  have he : ‖iteratedFDeriv ℝ j (fun y ↦ f (a * y)) r‖ =
      a ^ j * ‖iteratedFDeriv ℝ j f (a * r)‖ := by
    have hd := congrFun (iteratedFDeriv_comp_const_smul (i := j) a (hf.of_le (by simp))) r
    simpa only [smul_eq_mul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg ha j)] using congrArg norm hd
  rw [he]
  have hweighted := hbound j (a * r) (mul_nonneg ha hrpos.le)
  have hle : a ^ j * ‖iteratedFDeriv ℝ j f (a * r)‖ ≤ B j / ε ^ j := by
    apply (le_div_iff₀ (pow_pos hε j)).mpr
    calc
      _ ≤ a ^ j * ‖iteratedFDeriv ℝ j f (a * r)‖ * r ^ j := by gcongr
      _ = ‖iteratedFDeriv ℝ j f (a * r)‖ * (a * r) ^ j := by rw [mul_pow]; ring
      _ ≤ B j := hweighted
  apply hle.trans
  have hsum := Finset.single_le_sum (fun i _ ↦ hterm i)
    (Finset.mem_range.mpr (by omega : j < s + 1))
  dsimp [C]
  linarith

/-- Uniform finite jets give the baseline-one primitive profile for a scalar
mask. This is used only for fixed masks, before inverse substitution; source:
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem shellJetProfile_of_uniform_scalar_jets {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {s : ℕ} (hs : 2 ≤ s) {C H r : ℝ} (hC : 0 ≤ C) (hH : 1 ≤ H)
    (hb : ∀ j ≤ s, ‖iteratedFDeriv ℝ j f r‖ ≤ C) :
    ShellJetProfile s H C f r := by
  refine ⟨hf.contDiffAt, by simpa using hb 0 (Nat.zero_le s), ?_⟩
  intro j hj hjs
  apply (hb j hjs).trans
  apply le_mul_of_one_le_right hC (Real.one_le_rpow hH ?_)
  apply div_nonneg (sub_nonneg.mpr (by exact_mod_cast hj))
  have : (2 : ℝ) ≤ s := by exact_mod_cast hs
  linarith

/-- The unregularized fixed high mask has uniform primitive profiles after
positive frequency rescaling. In particular the conclusion holds on every
`[ε,L]`. Its zero core is unnecessary away from zero.
Source: `app:ch_background:prop:bg-frame`, Step 1. -/
theorem exists_rescaledHigh_shellJetProfile {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (htail : ∀ r, 2 ≤ r → h r = 1) {ε : ℝ} (hε : 0 < ε)
    (s : ℕ) (hs : 2 ≤ s) :
    ∃ C > 0, ∀ (t H : ℝ), 1 ≤ t → 1 ≤ H → ∀ r : ℝ, ε ≤ r →
      ShellJetProfile s H C (fun y ↦ h (t * y)) r := by
  obtain ⟨C, hC, hb⟩ := exists_scalarMask_dilation_jet_bound hh htail hε s
  exact ⟨C, hC, fun t H ht hH r hr ↦ shellJetProfile_of_uniform_scalar_jets
    (hh.comp (contDiff_const.mul contDiff_id)) hs hC.le hH
    (hb t (zero_le_one.trans ht) r hr)⟩

/-- Uniform profiles of the actual product `h(t r) χ(t r/R)` from the fixed
scalar masks. No norm or jet of a composed mask is assumed. Constants precede
`t`, `R`, and `H`. Compact support of `χ` suffices on a positive radial shell,
so this includes every smooth profile constant near zero.
Source: `app:ch_background:eq:bg-full-complex-amplitude` and bg-frame Step 1. -/
theorem exists_rescaledRegularizedHigh_shellJetProfile
    {h χ : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (htail : ∀ r, 2 ≤ r → h r = 1)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {ε : ℝ} (hε : 0 < ε) (s : ℕ) (hs : 2 ≤ s) :
    ∃ C > 0, ∀ (t R H : ℝ), 1 ≤ t → 1 ≤ R → 1 ≤ H →
      ∀ r : ℝ, ε ≤ r →
      ShellJetProfile s H C (fun y ↦ h (t * y) * χ (t * y / R)) r := by
  obtain ⟨A, hA, ha⟩ := exists_scalarMask_dilation_jet_bound hh htail hε s
  obtain ⟨b, hb, htailχ⟩ := hc.exists_pos_le_norm
  have htailχ' : ∀ x : ℝ, b ≤ x → χ x = 0 := by
    intro x hx
    exact htailχ x (by simpa only [Real.norm_eq_abs, abs_of_nonneg (hb.le.trans hx)] using hx)
  obtain ⟨B, hB, hbb⟩ := exists_scalarMask_dilation_jet_bound hχ htailχ' hε s
  let D (j : ℕ) : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A * B
  have hD (j : ℕ) : 0 ≤ D j := by dsimp [D]; positivity
  let C := 1 + ∑ j ∈ Finset.range (s + 1), D j
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro t R H ht hR hH r hr
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hf : ContDiff ℝ ∞ (fun y : ℝ ↦ h (t * y)) :=
    hh.comp (contDiff_const.mul contDiff_id)
  have hg : ContDiff ℝ ∞ (fun y : ℝ ↦ χ (t * y / R)) :=
    hχ.comp ((contDiff_const.mul contDiff_id).div_const R)
  apply shellJetProfile_of_uniform_scalar_jets (hf.mul hg) hs (by dsimp [C]; positivity) hH
  intro j hj
  apply (norm_iteratedFDeriv_mul_le hf hg r (by simp)).trans
  have hprod : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i (fun y ↦ h (t * y)) r‖ *
      ‖iteratedFDeriv ℝ (j - i) (fun y ↦ χ (t * y / R)) r‖) ≤ D j := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ s := by have := Finset.mem_range.mp hi; omega
    have h₁ := ha t (zero_le_one.trans ht) r hr i hi'
    have h₂ := hbb (t / R) (div_nonneg (zero_le_one.trans ht) hRpos.le)
      r hr (j - i) (by omega)
    have he : (fun y ↦ χ (t * y / R)) = (fun y ↦ χ (t / R * y)) := by
      funext y; congr 1; ring
    rw [he]
    exact mul_le_mul (mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg _)) h₂
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA.le)
  apply hprod.trans
  have hsum := Finset.single_le_sum (fun i _ ↦ hD i)
    (Finset.mem_range.mpr (by omega : j < s + 1))
  dsimp [C]
  linarith

end JanetCartan.ContinuumNormalReduction.TransportSymbol
