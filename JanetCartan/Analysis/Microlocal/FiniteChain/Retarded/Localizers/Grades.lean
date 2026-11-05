module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.Localizers.Nesting
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Uniform grades and physical rescaling of retarded masks

The fixed masks from `app:ch_regular:lem:finite-chain` obey the normalized
joint grades of `app:ch_regular:eq:high-amplitude`. Compact support gives
constants at every order for the same family. Physical covector rescaling
gives exactly one inverse-frequency factor per covector differentiation.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff BigOperators

namespace JanetCartan.FiniteChain.Retarded

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite fixed smooth compactly supported family has a single sequence of
uniform derivative bounds (`app:ch_regular:eq:high-amplitude`). -/
theorem exists_uniform_mask_derivative_bounds {ι : Type*} [Fintype ι]
    (m : ι → CanonicalPhase E → ℝ) (hs : ∀ i, ContDiff ℝ ∞ (m i))
    (hc : ∀ i, HasCompactSupport (m i)) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ n i p, ‖iteratedFDeriv ℝ n (m i) p‖ ≤ C n := by
  classical
  have hb : ∀ n i, ∃ C : ℝ, 0 ≤ C ∧
      ∀ p, ‖iteratedFDeriv ℝ n (m i) p‖ ≤ C := by
    intro n i
    obtain ⟨C, hC, h⟩ := (hc i).exists_bound_iteratedFDeriv (hs i) n
    exact ⟨C, hC, h n le_rfl⟩
  choose B hB hb using hb
  refine ⟨fun n => ∑ i, B n i, fun n => Finset.sum_nonneg (fun i _ => hB n i), ?_⟩
  intro n i p
  exact (hb n i p).trans (Finset.single_le_sum (fun j _ => hB n j) (Finset.mem_univ i))

/-- Fixed normalized derivative bounds imply the joint grade `Cₙ Lⁿ` for
every `L ≥ 1` (`app:ch_regular:eq:high-amplitude`). -/
theorem mask_derivative_grade {m : CanonicalPhase E → ℝ} {C : ℝ} {n : ℕ}
    (hC : 0 ≤ C) (h : ∀ p, ‖iteratedFDeriv ℝ n m p‖ ≤ C)
    {L : ℝ} (hL : 1 ≤ L) (p : CanonicalPhase E) :
    ‖iteratedFDeriv ℝ n m p‖ ≤ C * L ^ n :=
  (h p).trans (le_mul_of_one_le_right hC (one_le_pow₀ hL))

/-- Normalize the covector, leaving the physical base fixed
(`app:ch_regular:eq:high-amplitude`). -/
def normalizeMaskCovector (ρ : ℝ) : CanonicalPhase E →L[ℝ] CanonicalPhase E :=
  (ContinuousLinearMap.fst ℝ (ℝ × E) (ℝ × E)).prod
    (ρ⁻¹ • ContinuousLinearMap.snd ℝ (ℝ × E) (ℝ × E))

/-- Coordinate formula for the normalization map
(`app:ch_regular:eq:high-amplitude`). -/
@[simp] theorem normalizeMaskCovector_apply (ρ : ℝ) (p : CanonicalPhase E) :
    normalizeMaskCovector ρ p = (p.1, ρ⁻¹ • p.2) := rfl

/-- Physical proof mask at frequency `ρ`
(`app:ch_regular:lem:finite-chain`). -/
def physicalMask (ρ : ℝ) (m : CanonicalPhase E → ℝ) : CanonicalPhase E → ℝ :=
  m ∘ normalizeMaskCovector ρ

/-- Physical rescaling preserves smoothness
(`app:ch_regular:eq:high-amplitude`). -/
theorem contDiff_physicalMask {m : CanonicalPhase E → ℝ}
    (hm : ContDiff ℝ ∞ m) (ρ : ℝ) : ContDiff ℝ ∞ (physicalMask ρ m) :=
  hm.comp (normalizeMaskCovector (E := E) ρ).contDiff

/-- A pure base (`false`) or pure joint-covector (`true`) direction, allowing
arbitrary interleavings of mixed derivatives
(`app:ch_regular:eq:high-amplitude`). -/
def maskDirection (covector : Bool) (v : ℝ × E) : CanonicalPhase E :=
  if covector then (0, v) else (v, 0)

omit [NormedSpace ℝ E] in
/-- Pure directions have their original norm
(`app:ch_regular:eq:high-amplitude`). -/
@[simp] theorem norm_maskDirection (b : Bool) (v : ℝ × E) :
    ‖maskDirection b v‖ = ‖v‖ := by
  cases b <;> simp [maskDirection]

/-- The number of covector differentiations in a mixed derivative
(`app:ch_regular:eq:high-amplitude`). -/
def maskCovectorOrder {n : ℕ} (b : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => b i = true)).card

/-- Exact mixed chain rule: each covector direction contributes `ρ⁻¹`, and
each base direction contributes one (`app:ch_regular:eq:high-amplitude`). -/
theorem iteratedFDeriv_physicalMask_mixed {m : CanonicalPhase E → ℝ}
    (hm : ContDiff ℝ ∞ m) (ρ : ℝ) (n : ℕ) (p : CanonicalPhase E)
    (b : Fin n → Bool) (v : Fin n → ℝ × E) :
    iteratedFDeriv ℝ n (physicalMask ρ m) p (fun i => maskDirection (b i) (v i)) =
      (ρ⁻¹) ^ maskCovectorOrder b *
        iteratedFDeriv ℝ n m (normalizeMaskCovector ρ p)
          (fun i => maskDirection (b i) (v i)) := by
  rw [physicalMask, (normalizeMaskCovector ρ).iteratedFDeriv_comp_right hm p
    (show (n : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hd : (fun i => normalizeMaskCovector ρ (maskDirection (b i) (v i))) =
      fun i => (if b i then ρ⁻¹ else 1) • maskDirection (b i) (v i) := by
    funext i
    cases b i <;> simp [maskDirection]
  rw [hd, ContinuousMultilinearMap.map_smul_univ]
  simp [Finset.prod_ite, maskCovectorOrder, smul_eq_mul]

/-- Mixed physical derivative bounds, including the direction norms, with
an explicit positive frequency and one inverse-frequency factor per covector
direction (`app:ch_regular:eq:high-amplitude`). -/
theorem norm_iteratedFDeriv_physicalMask_mixed_le {m : CanonicalPhase E → ℝ}
    (hm : ContDiff ℝ ∞ m) {n : ℕ} {C ρ L : ℝ}
    (hC : 0 ≤ C) (hb : ∀ p, ‖iteratedFDeriv ℝ n m p‖ ≤ C)
    (hρ : 0 < ρ) (hL : 1 ≤ L) (p : CanonicalPhase E)
    (b : Fin n → Bool) (v : Fin n → ℝ × E) :
    ‖iteratedFDeriv ℝ n (physicalMask ρ m) p (fun i => maskDirection (b i) (v i))‖ ≤
      C * L ^ n * (ρ⁻¹) ^ maskCovectorOrder b * ∏ i, ‖v i‖ := by
  rw [iteratedFDeriv_physicalMask_mixed hm, norm_mul,
    Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hρ.le) _)]
  have h := (iteratedFDeriv ℝ n m (normalizeMaskCovector ρ p)).le_opNorm
    (fun i => maskDirection (b i) (v i))
  simp only [norm_maskDirection] at h
  have hg := mask_derivative_grade hC hb hL (normalizeMaskCovector ρ p)
  have hv : 0 ≤ ∏ i, ‖v i‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  calc
    _ ≤ (ρ⁻¹) ^ maskCovectorOrder b * (C * L ^ n * ∏ i, ‖v i‖) :=
      mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_right hg hv))
        (pow_nonneg (inv_nonneg.mpr hρ.le) _)
    _ = _ := by ring

/-- Signed reflection preserves the full derivative norm at the reflected
point, so the same constants work for both signs
(`app:ch_regular:lem:finite-chain`). -/
theorem norm_iteratedFDeriv_signedMask (m : CanonicalPhase E → ℝ)
    (n : ℕ) (p : CanonicalPhase E) :
    ‖iteratedFDeriv ℝ n (signedMask m) p‖ =
      ‖iteratedFDeriv ℝ n m (reflectCovector p)‖ := by
  let r : CanonicalPhase E ≃ₗᵢ[ℝ] CanonicalPhase E :=
    { toLinearEquiv := (LinearEquiv.refl ℝ (ℝ × E)).prodCongr (LinearEquiv.neg ℝ)
      norm_map' := by intro q; change ‖(q.1, -q.2)‖ = ‖q‖; simp [Prod.norm_def] }
  exact r.norm_iteratedFDeriv_comp_right m p n

/-- At frequencies at least one, normalization contracts the full phase norm
(`app:ch_regular:eq:high-amplitude`). -/
theorem norm_normalizeMaskCovector_le {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ‖normalizeMaskCovector (E := E) ρ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  rw [one_mul]
  change ‖(p.1, ρ⁻¹ • p.2)‖ ≤ ‖p‖
  rw [Prod.norm_def, Prod.norm_def, norm_smul]
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hρ))]
  exact max_le (le_max_left _ _)
    ((mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hρ)).trans
      (le_max_right _ _))

/-- Full operator-norm derivative bounds after physical rescaling require
`ρ ≥ 1`; the constants remain independent of `ρ,L`
(`app:ch_regular:eq:high-amplitude`). -/
theorem norm_iteratedFDeriv_physicalMask_le {m : CanonicalPhase E → ℝ}
    (hm : ContDiff ℝ ∞ m) {n : ℕ} {C ρ L : ℝ}
    (hC : 0 ≤ C) (hb : ∀ p, ‖iteratedFDeriv ℝ n m p‖ ≤ C)
    (hρ : 1 ≤ ρ) (hL : 1 ≤ L) (p : CanonicalPhase E) :
    ‖iteratedFDeriv ℝ n (physicalMask ρ m) p‖ ≤ C * L ^ n := by
  rw [physicalMask, (normalizeMaskCovector ρ).iteratedFDeriv_comp_right hm p
    (show (n : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)]
  refine ((iteratedFDeriv ℝ n m (normalizeMaskCovector ρ p)).norm_compContinuousLinearMap_le
    (fun _ => normalizeMaskCovector ρ)).trans ?_
  have hp : (∏ _ : Fin n, ‖normalizeMaskCovector (E := E) ρ‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => norm_normalizeMaskCovector_le hρ)
  exact (mul_le_of_le_one_right (norm_nonneg _) hp).trans (mask_derivative_grade hC hb hL _)

/-- Uniform normalized bounds for a finite buffered family and both signs,
with the very same constants (`app:ch_regular:lem:finite-chain`). -/
theorem exists_bufferedMask_family_bounds {ι : Type*} [Fintype ι]
    {m : ι → CanonicalPhase E → ℝ} {K O : ι → Set (CanonicalPhase E)}
    (hm : ∀ i, IsBufferedMask (m i) (K i) (O i)) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ i (negative : Bool) n p,
        ‖iteratedFDeriv ℝ n (if negative then signedMask (m i) else m i) p‖ ≤ C n := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_mask_derivative_bounds m
    (fun i => (hm i).smooth) (fun i => (hm i).compactSupport)
  refine ⟨C, hC, ?_⟩
  intro i negative n p
  cases negative
  · exact hb n i p
  · simpa only [↓reduceIte, norm_iteratedFDeriv_signedMask] using hb n i (reflectCovector p)

/-- Every finite buffered family, chosen once, has all normalized joint grades,
mixed physical derivative bounds, and full physical operator-norm bounds for
both signs. The constants precede `ρ,L` and are uniform in the family
(`app:ch_regular:eq:high-amplitude`). -/
theorem exists_bufferedMask_family_grades {ι : Type*} [Fintype ι]
    {m : ι → CanonicalPhase E → ℝ} {K O : ι → Set (CanonicalPhase E)}
    (hm : ∀ i, IsBufferedMask (m i) (K i) (O i)) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ i (negative : Bool) n,
        let f := if negative then signedMask (m i) else m i
        (∀ L, 1 ≤ L → ∀ p, ‖iteratedFDeriv ℝ n f p‖ ≤ C n * L ^ n) ∧
        (∀ ρ, 0 < ρ → ∀ L, 1 ≤ L → ∀ p (b : Fin n → Bool) (v : Fin n → ℝ × E),
          ‖iteratedFDeriv ℝ n (physicalMask ρ f) p (fun j => maskDirection (b j) (v j))‖ ≤
            C n * L ^ n * (ρ⁻¹) ^ maskCovectorOrder b * ∏ j, ‖v j‖) ∧
        (∀ ρ, 1 ≤ ρ → ∀ L, 1 ≤ L → ∀ p,
          ‖iteratedFDeriv ℝ n (physicalMask ρ f) p‖ ≤ C n * L ^ n) := by
  obtain ⟨C, hC, hb⟩ := exists_bufferedMask_family_bounds hm
  refine ⟨C, hC, ?_⟩
  intro i negative n
  have hs : ContDiff ℝ ∞ (if negative then signedMask (m i) else m i) := by
    cases negative
    · exact (hm i).smooth
    · exact (hm i).signed.smooth
  exact ⟨fun _ hL => mask_derivative_grade (hC n) (hb i negative n) hL,
    fun _ hρ _ hL => norm_iteratedFDeriv_physicalMask_mixed_le hs (hC n)
      (hb i negative n) hρ hL,
    fun _ hρ _ hL => norm_iteratedFDeriv_physicalMask_le hs (hC n) (hb i negative n) hρ hL⟩

/-- Nested proof masks and all-order derivative constants are selected before
frequency, grade, or differentiation order. Use `mask_derivative_grade` and
`norm_iteratedFDeriv_physicalMask_mixed_le` for the corresponding normalized
and physical grades (`app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:high-amplitude`). -/
theorem exists_nested_bufferedMasks_with_bounds [FiniteDimensional ℝ E]
    (N : ℕ) {K O : Set (CanonicalPhase E)}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ m : Fin N → CanonicalPhase E → ℝ,
      (∀ i, IsBufferedMask (m i) K O) ∧
      (∀ i j, i < j → tsupport (m i) ⊆ interior {p | m j p = 1}) ∧
      ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
        ∀ i (negative : Bool) n p,
          ‖iteratedFDeriv ℝ n (if negative then signedMask (m i) else m i) p‖ ≤ C n := by
  obtain ⟨m, hm, hn⟩ := exists_nested_bufferedMasks N hK hO hKO
  exact ⟨m, hm, hn, exists_bufferedMask_family_bounds hm⟩

end JanetCartan.FiniteChain.Retarded
