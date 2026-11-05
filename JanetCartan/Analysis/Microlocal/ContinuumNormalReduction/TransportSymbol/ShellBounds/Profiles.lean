module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.ShellBounds.Coefficient
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Primitive profile bookkeeping on normalized shells

The consumer is the transport shell density estimate. The baseline-one
partition identity from `app:ch_regular_base:eq:joint-primitive-product`
retains a single common high norm through primitive composition and pairing.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
open FourierIntegral.NormalOneHigh

/-- A primitive's low bound and interpolated positive jets. This contains no
amplitude or density estimate (`app:ch_background:eq:bg-mixed-input`). -/
structure ShellJetProfile {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : ℕ) (H C : ℝ) (f : E → F) (x : E) : Prop where
  smooth : ContDiffAt ℝ ∞ f x
  value : ‖f x‖ ≤ C
  jet : ∀ i, 1 ≤ i → i ≤ s →
    ‖iteratedFDeriv ℝ i f x‖ ≤ C * H ^ (((i : ℝ) - 1) / (s - 1))

namespace ShellJetProfile
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {s : ℕ} {H A B : ℝ} {x : E} {f : E → F} {g : E → G}

/-- Increasing a fixed primitive constant preserves the profile. -/
theorem mono (hf : ShellJetProfile s H A f x) (hAB : A ≤ B) (hH : 0 ≤ H) :
    ShellJetProfile s H B f x :=
  ⟨hf.smooth, hf.value.trans hAB, fun i hi his ↦ (hf.jet i hi his).trans
    (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg hH _))⟩

/-- Pairing primitive arrays adds only their fixed constants. -/
theorem prod (hf : ShellJetProfile s H A f x) (hg : ShellJetProfile s H B g x)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H) :
    ShellJetProfile s H (A + B) (fun y ↦ (f y, g y)) x := by
  refine ⟨hf.smooth.prodMk hg.smooth, ?_, ?_⟩
  · rw [Prod.norm_def]
    exact max_le (hf.value.trans (le_add_of_nonneg_right hB))
      (hg.value.trans (le_add_of_nonneg_left hA))
  · intro i hi his
    rw [iteratedFDeriv_prodMk hf.smooth hg.smooth (by simp),
      ContinuousMultilinearMap.opNorm_prod]
    apply max_le
    · exact (hf.jet i hi his).trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right hB) (Real.rpow_nonneg hH _))
    · exact (hg.jet i hi his).trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hA) (Real.rpow_nonneg hH _))

/-- Composition spends the exact partition budget, retaining the baseline-one
profile rather than multiplying two high norms. -/
theorem comp {g : F → G} (hg : ShellJetProfile s H A g (f x))
    (hf : ShellJetProfile s H B f x) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 < H) :
    ShellJetProfile s H
      (A + ∑ i ∈ Finset.range (s + 1), compositionBudget (fun _ ↦ A) (fun _ ↦ B) i)
      (g ∘ f) x := by
  have hn := compositionBudget_nonneg (fun _ ↦ hA) (fun _ ↦ hB)
  refine ⟨hg.smooth.comp x hf.smooth,
    hg.value.trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ ↦ hn i))), ?_⟩
  intro i hi his
  apply (norm_iteratedFDeriv_comp_le_profile hf.smooth hg.smooth hi his hH
    (fun _ ↦ A) (fun _ ↦ B) (fun _ ↦ hA) hg.jet hf.jet).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hH.le _)
  have hh := Finset.single_le_sum (fun j _ ↦ hn j)
    (Finset.mem_range.mpr (by omega : i < s + 1))
  linarith

/-- A contraction on the values preserves all primitive jet bounds. -/
theorem linear (hf : ShellJetProfile s H A f x) (L : F →L[ℝ] G) (hL : ‖L‖ ≤ 1) :
    ShellJetProfile s H A (L ∘ f) x := by
  refine ⟨L.contDiff.contDiffAt.comp x hf.smooth, ?_, ?_⟩
  · exact ((L.le_opNorm (f x)).trans (by nlinarith [norm_nonneg (f x)])).trans hf.value
  · intro i hi his
    rw [L.iteratedFDeriv_comp_left hf.smooth (by simp)]
    apply (L.norm_compContinuousMultilinearMap_le _).trans
    exact (mul_le_of_le_one_left (norm_nonneg _) hL).trans (hf.jet i hi his)

/-- Projection of a primitive array preserves its profile. -/
theorem fst {f : E → F × G} (hf : ShellJetProfile s H A f x) :
    ShellJetProfile s H A (fun y ↦ (f y).1) x :=
  hf.linear (ContinuousLinearMap.fst ℝ F G) (ContinuousLinearMap.norm_fst_le ..)

/-- Projection of a primitive array preserves its profile. -/
theorem snd {f : E → F × G} (hf : ShellJetProfile s H A f x) :
    ShellJetProfile s H A (fun y ↦ (f y).2) x :=
  hf.linear (ContinuousLinearMap.snd ℝ F G) (ContinuousLinearMap.norm_snd_le ..)
/-- Every order through s is bounded by one common high norm. -/
theorem bound (hf : ShellJetProfile s H A f x) (hA : 0 ≤ A) (hH : 1 ≤ H)
    (hs : 2 ≤ s) (k : ℕ) (hk : k ≤ s) : ‖iteratedFDeriv ℝ k f x‖ ≤ A * H := by
  by_cases hk0 : k = 0
  · subst k
    simpa using hf.value.trans (le_mul_of_one_le_right hA hH)
  · apply (hf.jet k (by omega) hk).trans
    apply mul_le_mul_of_nonneg_left _ hA
    have hspos : (0 : ℝ) < s - 1 := by
      have : (2 : ℝ) ≤ s := by exact_mod_cast hs
      linarith
    calc
      _ ≤ H ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hH
        ((div_le_one hspos).mpr (sub_le_sub_right (by exact_mod_cast hk) 1))
      _ = H := Real.rpow_one H

end ShellJetProfile

/-- Any fixed smooth coordinate operation has uniform primitive profiles on
its compact shell. Its constant is chosen before H and the varying fields.
Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem exists_fixedShellJetProfile
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} (hK : IsCompact K) {f : E → F}
    (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x) (s : ℕ) (hs : 2 ≤ s) :
    ∃ C > 0, ∀ H : ℝ, 1 ≤ H → ∀ x ∈ K, ShellJetProfile s H C f x := by
  have hb (i : ℕ) : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
    apply hK.exists_bound_of_continuousOn
    intro x hx
    exact ((hf x hx).continuousAt_iteratedFDeriv (by simp)).continuousWithinAt
  choose C hC using hb
  let R := 1 + ∑ i ∈ Finset.range (s + 1), |C i|
  have hR : 0 < R := by dsimp [R]; positivity
  have hbound (i : ℕ) (hi : i ≤ s) (x) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ i f x‖ ≤ R := by
    have hh := Finset.single_le_sum (fun j _ ↦ abs_nonneg (C j))
      (Finset.mem_range.mpr (by omega : i < s + 1))
    have hh' := hC i x hx
    dsimp [R]
    linarith [le_abs_self (C i)]
  refine ⟨R, hR, ?_⟩
  intro H hH x hx
  refine ⟨hf x hx, by simpa using hbound 0 (Nat.zero_le s) x hx, ?_⟩
  intro i hi his
  apply (hbound i his x hx).trans
  apply le_mul_of_one_le_right hR.le (Real.one_le_rpow hH ?_)
  apply div_nonneg (sub_nonneg.mpr (by exact_mod_cast hi))
  have : (2 : ℝ) ≤ s := by exact_mod_cast hs
  linarith

/-- Buffered low/high norms produce the primitive profile used by the shell
composition proofs. No derivative shift is added. Source:
`app:ch_regular_base:eq:joint-primitive-product`. -/
theorem exists_shellJetProfile_of_cNorm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) {U : Set E} (hU : IsOpen U)
    (hball : Metric.closedBall x ρ ⊆ U) {s : ℕ} (hs : 2 ≤ s)
    {M T : ℝ} (hM : 0 ≤ M) (hT : 1 ≤ T) :
    ∃ C > 0, ∀ (f : E → F) (H : ℝ), ContDiffOn ℝ ∞ f U → 1 ≤ H →
      cNorm (Metric.closedBall x ρ) 1 f ≤ M →
      1 + cNorm (Metric.closedBall x ρ) s f ≤ T * H →
      ∀ z ∈ Metric.closedBall x ρ, ShellJetProfile s H C f z := by
  obtain ⟨C, hC, hb⟩ := exists_primitiveJet_profile_closedBall (F := F) x hρ hU hball hs hM hT
  refine ⟨M + C, by linarith, ?_⟩
  intro f H hf hH hlo hhi z hz
  obtain ⟨hval, hjet⟩ := hb f H hf hH hlo hhi
  refine ⟨hf.contDiffAt (hU.mem_nhds (hball hz)), (hval z hz).trans (by linarith), ?_⟩
  intro i hi his
  exact (hjet z hz i hi his).trans (mul_le_mul_of_nonneg_right
    (by linarith) (Real.rpow_nonneg (zero_le_one.trans hH) _))

end JanetCartan.ContinuumNormalReduction.TransportSymbol
