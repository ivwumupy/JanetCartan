module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.Seminorms

/-!
# Normalized joint seminorms for the strong graph estimate

For Step 3 of `app:ch_regular_base:thm:actual-calculus`, normalize only the
covector by a radius `R ≥ 1`. The position space can be the product of both
physical positions. The complete function, including all masks, is pulled back.
The seminorm is the supremum over radii of the joint `cNorm` on one fixed ball.
Its finiteness is the symbol-class condition, not automatic for a smooth field.

The interpolation constants below are chosen before the field and its high
seminorms. These are the individual interpolation inputs of
`exists_graph_sobolev_constant_of_weighted_primitives` and its adjoint version.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.FourierIntegral.PrimitiveProfiles

variable {X Ξ F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Covector normalization of the complete primitive, retaining all positions
and masks, in Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
def normalizedField (R : ℝ) (f : X × Ξ → F) : X × Ξ → F :=
  fun p ↦ f (p.1, R • p.2)

/-- The order-zero normalized seminorm convention for
`app:ch_regular_base:eq:fio-input`: the supremum of joint `cNorm`s over radii
at least one. Bounds using this real supremum require boundedness of its range. -/
def normalizedSeminorm (K : Set (X × Ξ)) (j : ℕ) (f : X × Ξ → F) : ℝ :=
  sSup (Set.range fun R : {R : ℝ // 1 ≤ R} ↦ cNorm K j (normalizedField R f))

/-- Finiteness of a normalized symbol seminorm, needed to use its real supremum
in `app:ch_regular_base:eq:fio-input`. This refers to actual differentiated fields. -/
def BoundedNormalizedSeminorm (K : Set (X × Ξ)) (j : ℕ) (f : X × Ξ → F) : Prop :=
  BddAbove (Set.range fun R : {R : ℝ // 1 ≤ R} ↦ cNorm K j (normalizedField R f))

/-- Nonnegativity of the normalized primitive majorant in Step 3. -/
theorem normalizedSeminorm_nonneg (K : Set (X × Ξ)) (j : ℕ) (f : X × Ξ → F) :
    0 ≤ normalizedSeminorm K j f := by
  apply Real.sSup_nonneg
  rintro _ ⟨R, rfl⟩
  exact CNormInterpolation.cNorm_nonneg _ _ _

/-- Every normalized radius is bounded by the same majorant in Step 3. -/
theorem cNorm_normalizedField_le {K : Set (X × Ξ)} {j : ℕ} {f : X × Ξ → F}
    (hb : BoundedNormalizedSeminorm K j f) {R : ℝ} (hR : 1 ≤ R) :
    cNorm K j (normalizedField R f) ≤ normalizedSeminorm K j f :=
  le_csSup hb ⟨⟨R, hR⟩, rfl⟩

/-- A higher finite normalized seminorm bounds every lower order. Source:
Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem BoundedNormalizedSeminorm.mono {K : Set (X × Ξ)} {j k : ℕ}
    {f : X × Ξ → F} (hb : BoundedNormalizedSeminorm K k f) (hjk : j ≤ k) :
    BoundedNormalizedSeminorm K j f := by
  obtain ⟨B, hB⟩ := hb
  refine ⟨B, ?_⟩
  rintro _ ⟨R, rfl⟩
  exact (CNormInterpolation.cNorm_mono K _ hjk).trans (hB ⟨R, rfl⟩)

/-- Monotonicity of the actual normalized primitive majorants used by the
weighted branch estimates in `app:ch_regular_base:eq:fio-input`. -/
theorem normalizedSeminorm_mono {K : Set (X × Ξ)} {j k : ℕ} {f : X × Ξ → F}
    (hb : BoundedNormalizedSeminorm K k f) (hjk : j ≤ k) :
    normalizedSeminorm K j f ≤ normalizedSeminorm K k f := by
  apply Real.sSup_le _ (normalizedSeminorm_nonneg _ _ _)
  rintro _ ⟨R, rfl⟩
  exact (CNormInterpolation.cNorm_mono K _ hjk).trans (cNorm_normalizedField_le hb R.2)

/-- Degree-zero dilation invariance on an open buffered chart identifies the
normalized seminorm with the original joint `cNorm`. In particular the inverse
primitive's boundedness need not be assumed separately once its homogeneity is
proved. Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem normalizedSeminorm_eq_cNorm_of_invariant {K U : Set (X × Ξ)}
    (hU : IsOpen U) (hKU : K ⊆ U) (f : X × Ξ → F)
    (hi : ∀ R : ℝ, 1 ≤ R → Set.EqOn (normalizedField R f) f U) (j : ℕ) :
    BoundedNormalizedSeminorm K j f ∧ normalizedSeminorm K j f = cNorm K j f := by
  have hc (R : {R : ℝ // 1 ≤ R}) : cNorm K j (normalizedField R f) = cNorm K j f := by
    unfold cNorm
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Set.image_congr
    intro p hp
    have he := Filter.eventuallyEq_of_mem (hU.mem_nhds (hKU hp)) (hi R R.2)
    rw [(he.iteratedFDeriv (𝕜 := ℝ) i).self_of_nhds]
  have hr : (Set.range fun R : {R : ℝ // 1 ≤ R} ↦ cNorm K j (normalizedField R f)) =
      {cNorm K j f} := by
    ext a
    constructor
    · rintro ⟨R, rfl⟩
      exact hc R
    · rintro rfl
      exact ⟨⟨1, le_rfl⟩, hc ⟨1, le_rfl⟩⟩
  constructor
  · unfold BoundedNormalizedSeminorm
    rw [hr]
    exact bddAbove_singleton
  · unfold normalizedSeminorm
    rw [hr, csSup_singleton]

variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ Ξ]

/-- Individual normalized interpolation is proved uniformly over radii and
fields. No interpolation assumption is supplied. Source:
`app:ch_regular_base:lem:buffered-interpolation`, used in Step 3. -/
theorem exists_normalizedSeminorm_interpolation (z : X × Ξ) {ρ : ℝ} (hρ : 0 < ρ)
    {U : Set (X × Ξ)} (hU : IsOpen U) (hball : Metric.closedBall z ρ ⊆ U)
    {b j k : ℕ} (hbj : b < j) (hjk : j < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : X × Ξ → F,
      (∀ R : ℝ, 1 ≤ R → ContDiffOn ℝ k (normalizedField R f) U) →
      BoundedNormalizedSeminorm (Metric.closedBall z ρ) k f →
      normalizedSeminorm (Metric.closedBall z ρ) j f ≤
        C * normalizedSeminorm (Metric.closedBall z ρ) b f ^
          (1 - (j - b : ℝ) / (k - b)) *
          normalizedSeminorm (Metric.closedBall z ρ) k f ^ ((j - b : ℝ) / (k - b)) := by
  obtain ⟨C, hC, hi⟩ := TransportInterpolation.exists_cNorm_interpolation_finite_on
    (F := F) z hρ hU hball hbj hjk
  refine ⟨C, hC, ?_⟩
  intro f hf hb
  have hθ : 0 ≤ (j - b : ℝ) / (k - b) := by
    exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hbj.le))
      (sub_nonneg.mpr (by exact_mod_cast (show b ≤ k by omega)))
  have hθ1 : (j - b : ℝ) / (k - b) ≤ 1 := by
    apply (div_le_one (sub_pos.mpr (by exact_mod_cast (show b < k by omega)))).mpr
    exact sub_le_sub_right (by exact_mod_cast hjk.le) _
  have hn (i : ℕ) := normalizedSeminorm_nonneg (Metric.closedBall z ρ) i f
  apply Real.sSup_le _ (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (hn b) _))
    (Real.rpow_nonneg (hn k) _))
  rintro _ ⟨R, rfl⟩
  apply (hi (normalizedField R f) (hf R R.2)).trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (CNormInterpolation.cNorm_nonneg _ _ _)
        (cNorm_normalizedField_le (hb.mono (by omega)) R.2) (sub_nonneg.mpr hθ1)) hC.le
  · exact Real.rpow_le_rpow (CNormInterpolation.cNorm_nonneg _ _ _)
      (cNorm_normalizedField_le hb R.2) hθ
  · exact Real.rpow_nonneg (CNormInterpolation.cNorm_nonneg _ _ _) _
  · exact mul_nonneg hC.le (Real.rpow_nonneg (hn b) _)

/-- One constant supplies all intermediate orders with the exact natural-index
exponents required by `StrongAssembly`. It is independent of the primitive and
its high seminorms. Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem exists_normalizedSeminorm_interpolation_constant
    (z : X × Ξ) {ρ : ℝ} (hρ : 0 < ρ) {U : Set (X × Ξ)}
    (hU : IsOpen U) (hball : Metric.closedBall z ρ ⊆ U) (μ s : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ f : X × Ξ → F,
      (∀ R : ℝ, 1 ≤ R → ContDiffOn ℝ (μ + s : ℕ) (normalizedField R f) U) →
      BoundedNormalizedSeminorm (Metric.closedBall z ρ) (μ + s) f →
      ∀ j : ℕ, μ < j → j < μ + s →
        normalizedSeminorm (Metric.closedBall z ρ) j f ≤
          K * normalizedSeminorm (Metric.closedBall z ρ) μ f ^
            (1 - ((j - μ : ℕ) : ℝ) / s) *
            normalizedSeminorm (Metric.closedBall z ρ) (μ + s) f ^
              (((j - μ : ℕ) : ℝ) / s) := by
  classical
  have hc : ∀ j : Fin (μ + s + 1), ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : X × Ξ → F,
        (∀ R : ℝ, 1 ≤ R → ContDiffOn ℝ (μ + s : ℕ) (normalizedField R f) U) →
        BoundedNormalizedSeminorm (Metric.closedBall z ρ) (μ + s) f →
        μ < j.val → j.val < μ + s →
        normalizedSeminorm (Metric.closedBall z ρ) j f ≤
          C * normalizedSeminorm (Metric.closedBall z ρ) μ f ^
            (1 - ((j.val - μ : ℕ) : ℝ) / s) *
            normalizedSeminorm (Metric.closedBall z ρ) (μ + s) f ^
              (((j.val - μ : ℕ) : ℝ) / s) := by
    intro j
    by_cases hj : μ < j.val ∧ j.val < μ + s
    · obtain ⟨C, hC, hi⟩ := exists_normalizedSeminorm_interpolation
        (F := F) z hρ hU hball hj.1 hj.2
      refine ⟨C, hC.le, ?_⟩
      intro f hf hb _ _
      simpa only [Nat.cast_sub hj.1.le, Nat.cast_add, add_sub_cancel_left] using hi f hf hb
    · exact ⟨0, le_rfl, fun _ _ _ h₁ h₂ ↦ (hj ⟨h₁, h₂⟩).elim⟩
  choose C hC hi using hc
  refine ⟨1 + ∑ j, C j, ?_, ?_⟩
  · linarith [Finset.sum_nonneg (fun j _ ↦ hC j) (s := Finset.univ)]
  · intro f hf hb j hj hj'
    let i : Fin (μ + s + 1) := ⟨j, by omega⟩
    have hCi : C i ≤ 1 + ∑ j, C j := by
      have := Finset.single_le_sum (fun j _ ↦ hC j) (Finset.mem_univ i)
      linarith
    exact (hi i f hf hb hj hj').trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCi (Real.rpow_nonneg (normalizedSeminorm_nonneg _ _ _) _))
      (Real.rpow_nonneg (normalizedSeminorm_nonneg _ _ _) _))

/-- The normalized convention controls the physical frequency-weighted mixed
Fréchet jets with both positions unchanged. Source: Step 3 before
`app:ch_regular_base:eq:fio-input`. Ordered coordinate words specialize this
estimate by choosing their coordinate directions and frequency slots. -/
theorem weighted_mixedJet_le_normalizedSeminorm
    (z : X × Ξ) {ρ : ℝ} {U V : Set (X × Ξ)}
    (hU : IsOpen U) (hV : IsOpen V) (hball : Metric.closedBall z ρ ⊆ U)
    {f : X × Ξ → F} {j : ℕ} (hf : ContDiffOn ℝ j f V)
    (hn : ∀ R : ℝ, 1 ≤ R → ContDiffOn ℝ j (normalizedField R f) U)
    (hb : BoundedNormalizedSeminorm (Metric.closedBall z ρ) j f)
    {R : ℝ} (hR : 1 ≤ R) (p : X × Ξ) (hp : p ∈ Metric.closedBall z ρ)
    (hpV : (p.1, R • p.2) ∈ V) (q : Finset (Fin j)) (v : Fin j → X × Ξ)
    (hv : ∀ i, if i ∈ q then (v i).1 = 0 else (v i).2 = 0)
    (hvnorm : ∀ i, ‖v i‖ ≤ 1) :
    R ^ q.card * ‖iteratedFDeriv ℝ j f (p.1, R • p.2) v‖ ≤
      normalizedSeminorm (Metric.closedBall z ρ) j f := by
  have hlocal (y : X × Ξ) (hy : y ∈ Metric.closedBall z ρ) :=
    (hn R hR).contDiffAt (hU.mem_nhds (hball hy))
  exact (norm_transportMixedJet_weight_le j (lt_of_lt_of_le zero_lt_one hR)
    hV hf p hpV q v hv hvnorm).trans
    ((norm_iteratedFDeriv_le_cNorm_of_contDiffAt
      (isCompact_closedBall z ρ) hlocal hp le_rfl).trans (cNorm_normalizedField_le hb hR))

end JanetCartan.FourierIntegral.PrimitiveProfiles
