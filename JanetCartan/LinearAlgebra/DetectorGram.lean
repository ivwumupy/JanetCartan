module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

/-!
# Positive weighted Gram operators from finite detection

The finite-dimensional implication used in `main:eq:detector-gram` and
`app:ch_seed:eq:seed-frozen-detection` of `paper.tex`: a family with trivial
common kernel, with any prescribed strictly positive weights, has a coercive
Gram operator. The estimates persist under small perturbations and are uniform
on compact parameter sets with continuous detectors and weights.

The geometric construction of the detecting family (including the image
channel and the selected incidence roots) is a separate input. This module
neither constructs those roots nor proves that the manuscript's carriers detect.
The inner-product space can in particular carry the Frobenius inner product.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open Set Metric

namespace JanetCartan.DetectorGram

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The common kernel is trivial: the algebraic input to
`main:eq:detector-gram`, distinct from constructing the geometric detectors. -/
def Detects (f : ι → E →L[ℝ] ℝ) : Prop :=
  ∀ x, (∀ i, f i x = 0) → x = 0

/-- The weighted Gram operator in `main:eq:detector-gram`:
`∑ i, w i • (f i)† ∘ f i`. -/
def weightedGram (f : ι → E →L[ℝ] ℝ) (w : ι → ℝ) : E →L[ℝ] E :=
  ∑ i, w i • (f i).adjoint.comp (f i)

/-- The Gram pairing is the weighted product of detector values
(`main:eq:detector-gram`). -/
theorem inner_weightedGram (f : ι → E →L[ℝ] ℝ) (w : ι → ℝ) (x y : E) :
    ⟪x, weightedGram f w y⟫_ℝ = ∑ i, w i * (f i x * f i y) := by
  simp [weightedGram, inner_sum, real_inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right, mul_comm]

/-- The quadratic form is the weighted sum of squares
(`main:eq:detector-gram`). -/
theorem inner_weightedGram_self (f : ι → E →L[ℝ] ℝ) (w : ι → ℝ) (x : E) :
    ⟪x, weightedGram f w x⟫_ℝ = ∑ i, w i * (f i x) ^ 2 := by
  simp [inner_weightedGram, pow_two]

/-- The weighted Gram form is symmetric (`main:eq:detector-gram`). -/
theorem weightedGram_symmetric (f : ι → E →L[ℝ] ℝ) (w : ι → ℝ) (x y : E) :
    ⟪x, weightedGram f w y⟫_ℝ = ⟪y, weightedGram f w x⟫_ℝ := by
  simp only [inner_weightedGram, mul_comm (f _ x)]

/-- Nonnegative weights give a nonnegative Gram form (`main:eq:detector-gram`). -/
theorem weightedGram_nonneg (f : ι → E →L[ℝ] ℝ) {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (x : E) : 0 ≤ ⟪x, weightedGram f w x⟫_ℝ := by
  rw [inner_weightedGram_self]
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i) (sq_nonneg _)

/-- Detection and positive weights give strict positivity away from zero
(`main:eq:detector-gram`). -/
theorem weightedGram_pos {f : ι → E →L[ℝ] ℝ} (hf : Detects f)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) {x : E} (hx : x ≠ 0) :
    0 < ⟪x, weightedGram f w x⟫_ℝ := by
  have hi : ∃ i, f i x ≠ 0 := by
    by_contra! h
    exact hx (hf x h)
  obtain ⟨i, hi⟩ := hi
  rw [inner_weightedGram_self]
  exact Finset.sum_pos' (fun j _ ↦ mul_nonneg (hw j).le (sq_nonneg _))
    ⟨i, Finset.mem_univ i, mul_pos (hw i) (sq_pos_of_ne_zero hi)⟩

/-- A compact family of positive quadratic forms has a common positive lower
bound (`app:ch_seed:eq:seed-frozen-detection`). No nontriviality of the vector
space or nonemptiness of the parameter set is required. -/
theorem exists_uniform_lower_bound {P : Type*} [TopologicalSpace P]
    {K : Set P} (hK : IsCompact K) (G : P → E →L[ℝ] E)
    (hG : ContinuousOn G K)
    (hpos : ∀ p ∈ K, ∀ x : E, x ≠ 0 → 0 < ⟪x, G p x⟫_ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ K, ∀ x : E, c * ‖x‖ ^ 2 ≤ ⟪x, G p x⟫_ℝ := by
  let S : Set (P × E) := K ×ˢ sphere (0 : E) 1
  have hS : IsCompact S := hK.prod (isCompact_sphere 0 1)
  have hn {x : E} (hx : x ≠ 0) : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have hcont : ContinuousOn (fun z : P × E ↦ ⟪z.2, G z.1 z.2⟫_ℝ) S :=
    continuous_snd.continuousOn.inner
      ((hG.comp continuous_fst.continuousOn (fun _ hz ↦ hz.1)).clm_apply
        continuous_snd.continuousOn)
  rcases S.eq_empty_or_nonempty with hEmpty | hNonempty
  · refine ⟨1, zero_lt_one, ?_⟩
    intro p hp x
    have hx : x = 0 := by
      by_contra hx
      have : (p, ‖x‖⁻¹ • x) ∈ S := ⟨hp, by simpa using hn hx⟩
      simp [hEmpty] at this
    simp [hx]
  · obtain ⟨z, hz, hmin⟩ := hS.exists_isMinOn hNonempty hcont
    have hzNorm : ‖z.2‖ = 1 := by simpa using hz.2
    have hz0 : z.2 ≠ 0 := by intro h; simp [h] at hzNorm
    refine ⟨⟪z.2, G z.1 z.2⟫_ℝ, hpos z.1 hz.1 z.2 hz0, ?_⟩
    intro p hp x
    by_cases hx : x = 0
    · simp [hx]
    have hmem : (p, ‖x‖⁻¹ • x) ∈ S := ⟨hp, by simpa using hn hx⟩
    have h := mul_le_mul_of_nonneg_right (hmin hmem) (sq_nonneg ‖x‖)
    have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have heq : ⟪‖x‖⁻¹ • x, G p (‖x‖⁻¹ • x)⟫_ℝ * ‖x‖ ^ 2 =
        ⟪x, G p x⟫_ℝ := by
      simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
      field_simp
    rwa [heq] at h

/-- Continuous detectors and weights give a continuous Gram operator
(`main:eq:detector-gram`). -/
theorem continuousOn_weightedGram {P : Type*} [TopologicalSpace P] {K : Set P}
    {f : P → ι → E →L[ℝ] ℝ} {w : P → ι → ℝ}
    (hf : ∀ i, ContinuousOn (fun p ↦ f p i) K)
    (hw : ∀ i, ContinuousOn (fun p ↦ w p i) K) :
    ContinuousOn (fun p ↦ weightedGram (f p) (w p)) K := by
  apply continuousOn_finsetSum
  intro i _
  exact (hw i).smul
    ((ContinuousLinearMap.adjoint.continuous.comp_continuousOn (hf i)).clm_comp (hf i))

/-- Positive prescribed weights and detection throughout a compact parameter
set imply a common Gram gap (`app:ch_seed:eq:seed-frozen-detection`). -/
theorem exists_uniform_weightedGram_lower_bound {P : Type*} [TopologicalSpace P]
    {K : Set P} (hK : IsCompact K)
    (f : P → ι → E →L[ℝ] ℝ) (w : P → ι → ℝ)
    (hf : ∀ i, ContinuousOn (fun p ↦ f p i) K)
    (hw : ∀ i, ContinuousOn (fun p ↦ w p i) K)
    (hdet : ∀ p ∈ K, Detects (f p)) (hweight : ∀ p ∈ K, ∀ i, 0 < w p i) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ K, ∀ x : E,
      c * ‖x‖ ^ 2 ≤ ⟪x, weightedGram (f p) (w p) x⟫_ℝ := by
  exact exists_uniform_lower_bound hK _ (continuousOn_weightedGram hf hw)
    (fun p hp _ hx ↦ weightedGram_pos (hdet p hp) (hweight p hp) hx)

/-- A detecting family has a positive uniform Gram gap for any prescribed
strictly positive weights (`main:eq:detector-gram`). -/
theorem exists_weightedGram_lower_bound {f : ι → E →L[ℝ] ℝ} (hf : Detects f)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : E, c * ‖x‖ ^ 2 ≤ ⟪x, weightedGram f w x⟫_ℝ := by
  obtain ⟨c, hc, h⟩ := exists_uniform_weightedGram_lower_bound
    (K := ({()} : Set Unit)) (isCompact_singleton) (fun _ ↦ f) (fun _ ↦ w)
    (fun _ ↦ continuousOn_const) (fun _ ↦ continuousOn_const)
    (fun _ _ ↦ hf) (fun _ _ ↦ hw)
  exact ⟨c, hc, h () (mem_singleton ())⟩

omit [Fintype ι] [FiniteDimensional ℝ E] in
/-- A spanning family of functionals detects every vector
(`main:eq:detector-gram`). In finite dimension, an algebraic linear functional
can be supplied using `LinearMap.toContinuousLinearMap`. -/
theorem detects_of_span_eq_top {f : ι → E →L[ℝ] ℝ}
    (hf : Submodule.span ℝ (Set.range f) = ⊤) : Detects f := by
  intro x hx
  have hzero : ∀ g ∈ Submodule.span ℝ (Set.range f), g x = 0 := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg => obtain ⟨i, rfl⟩ := hg; exact hx i
    | zero => simp
    | add g h hg hh hg' hh' => simp [hg', hh']
    | smul a g hg hg' => simp [hg']
  have h := hzero (innerSL ℝ x) (by rw [hf]; trivial)
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp h

omit [Fintype ι] [FiniteDimensional ℝ E] in
/-- Spanning detector vectors give detection by their inner products
(`app:ch_seed:eq:seed-frozen-detection`). -/
theorem detects_inner_of_span_eq_top {v : ι → E}
    (hv : Submodule.span ℝ (Set.range v) = ⊤) :
    Detects (fun i ↦ innerSL ℝ (v i)) := by
  intro x hx
  have hzero : ∀ y ∈ Submodule.span ℝ (Set.range v), ⟪y, x⟫_ℝ = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hx i
    | zero => simp
    | add y z hy hz hy' hz' => simp [inner_add_left, hy', hz']
    | smul a y hy hy' => simp [real_inner_smul_left, hy']
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp (hzero x (by rw [hv]; trivial))

omit [FiniteDimensional ℝ E] in
/-- Operator norm perturbations lose at most their size from the quadratic
lower bound (`main:eq:detector-gram`). The perturbation need not be symmetric. -/
theorem lower_bound_of_norm_sub_le {G H : E →L[ℝ] E} {c ε : ℝ}
    (hG : ∀ x : E, c * ‖x‖ ^ 2 ≤ ⟪x, G x⟫_ℝ)
    (hpert : ‖H - G‖ ≤ ε) :
    ∀ x : E, (c - ε) * ‖x‖ ^ 2 ≤ ⟪x, H x⟫_ℝ := by
  intro x
  have hop : ‖(G - H) x‖ ≤ ε * ‖x‖ :=
    ((G - H).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (by rwa [norm_sub_rev]) (norm_nonneg x))
  have hi := (real_inner_le_norm x ((G - H) x)).trans
    (mul_le_mul_of_nonneg_left hop (norm_nonneg x))
  simp only [sub_apply, inner_sub_right] at hi
  nlinarith [hG x]

/-- Simultaneously perturbing a finite detecting family and its prescribed
positive weights preserves a positive gap (`main:eq:detector-gram`). The norms
on the two finite function spaces are their supremum norms. -/
theorem exists_weightedGram_perturbation_radius {f : ι → E →L[ℝ] ℝ}
    (hf : Detects f) {w : ι → ℝ} (hw : ∀ i, 0 < w i) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (f' : ι → E →L[ℝ] ℝ) (w' : ι → ℝ),
        ‖f' - f‖ < δ → ‖w' - w‖ < δ →
        ∀ x : E, c * ‖x‖ ^ 2 ≤ ⟪x, weightedGram f' w' x⟫_ℝ := by
  obtain ⟨c, hc, hgap⟩ := exists_weightedGram_lower_bound hf hw
  have hcont : Continuous
      (fun p : (ι → E →L[ℝ] ℝ) × (ι → ℝ) ↦ weightedGram p.1 p.2) := by
    apply continuousOn_univ.mp
    exact continuousOn_weightedGram
      (fun i ↦ ((continuous_apply i).comp continuous_fst).continuousOn)
      (fun i ↦ ((continuous_apply i).comp continuous_snd).continuousOn)
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp (hcont.continuousAt (x := (f, w)))
    (c / 2) (by positivity)
  refine ⟨c / 2, by positivity, δ, hδ, ?_⟩
  intro f' w' hf' hw' x
  have hd : dist (f', w') (f, w) < δ := by
    simpa [Prod.dist_eq, dist_eq_norm, max_lt_iff] using And.intro hf' hw'
  have hop : ‖weightedGram f' w' - weightedGram f w‖ ≤ c / 2 := by
    simpa [dist_eq_norm] using (hclose hd).le
  have h := lower_bound_of_norm_sub_le hgap hop x
  convert h using 1
  ring

/-- Compact uniform detection also admits a uniform operator perturbation
margin (`app:ch_seed:eq:seed-frozen-detection`). This applies to any nearby
operator family, without requiring continuity of that perturbed family. -/
theorem exists_uniform_weightedGram_perturbation_bound
    {P : Type*} [TopologicalSpace P] {K : Set P} (hK : IsCompact K)
    (f : P → ι → E →L[ℝ] ℝ) (w : P → ι → ℝ)
    (hf : ∀ i, ContinuousOn (fun p ↦ f p i) K)
    (hw : ∀ i, ContinuousOn (fun p ↦ w p i) K)
    (hdet : ∀ p ∈ K, Detects (f p)) (hweight : ∀ p ∈ K, ∀ i, 0 < w p i) :
    ∃ c : ℝ, 0 < c ∧ ∀ (H : P → E →L[ℝ] E),
      (∀ p ∈ K, ‖H p - weightedGram (f p) (w p)‖ ≤ c) →
      ∀ p ∈ K, ∀ x : E, c * ‖x‖ ^ 2 ≤ ⟪x, H p x⟫_ℝ := by
  obtain ⟨c, hc, hgap⟩ :=
    exists_uniform_weightedGram_lower_bound hK f w hf hw hdet hweight
  refine ⟨c / 2, by positivity, ?_⟩
  intro H hH p hp x
  have h := lower_bound_of_norm_sub_le (hgap p hp) (hH p hp) x
  convert h using 1
  ring

end JanetCartan.DetectorGram
