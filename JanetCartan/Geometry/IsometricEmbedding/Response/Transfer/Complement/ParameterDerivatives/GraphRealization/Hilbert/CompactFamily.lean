module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.ParameterRealization.L2Family.CompactFamily
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Vector-valued compact families in Lebesgue L²

Vector-valued extension for the complementary graph construction in
`app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.Hilbert

variable {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {K : Set (EuclideanSpace ℝ (Fin n))}
variable (hK : IsCompact K)
variable [CompactSpace K]

/-- Extend a continuous function on the compact spatial set by zero, for
`app:ch_response:thm:response-literal-transfer`. -/
def extendVectorZero (f : C(K, F)) : (EuclideanSpace ℝ (Fin n)) → F :=
  Function.extend Subtype.val f 0

omit [CompactSpace K] [NormedSpace ℝ F] in
/-- The extension retains the original values on the compact set
(`app:ch_response:thm:response-literal-transfer`). -/
lemma extendVectorZero_mem (f : C(K, F)) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K) :
    extendVectorZero f x = f ⟨x, hx⟩ := by
  exact Subtype.coe_injective.extend_apply _ _ ⟨x, hx⟩

omit [CompactSpace K] [NormedSpace ℝ F] in
/-- The extension vanishes off the compact set
(`app:ch_response:thm:response-literal-transfer`). -/
lemma extendVectorZero_notMem (f : C(K, F)) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ K) :
    extendVectorZero f x = 0 := by
  exact Function.extend_apply' _ _ _ (by simpa using hx)

include hK in
omit [NormedSpace ℝ F] in
/-- The extension is in actual Lebesgue L2, by compact support and boundedness
(`app:ch_response:thm:response-literal-transfer`). -/
lemma extendVectorZero_memLp (f : C(K, F)) : MemLp (extendVectorZero f) 2 volume := by
  have hm : StronglyMeasurable (extendVectorZero f) :=
    (MeasurableEmbedding.subtype_coe hK.isClosed.measurableSet).stronglyMeasurable_extend
      f.continuous.stronglyMeasurable stronglyMeasurable_zero
  have hs : HasCompactSupport (extendVectorZero f) := by
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (extendVectorZero_notMem f hn)
  apply hs.memLp_of_bound hm.aestronglyMeasurable ‖f‖
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · rw [extendVectorZero_mem f hx]
    exact f.norm_coe_le_norm _
  · rw [extendVectorZero_notMem f hx, norm_zero]
    exact norm_nonneg _

/-- Zero extension from the uniform norm to actual Lebesgue L2 is bounded
linear. This transfers the compact-family derivatives in
`app:ch_response:thm:response-literal-transfer`. -/
def compactVectorToL2 : C(K, F) →L[ℝ] Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (extendVectorZero_memLp hK f).toLp (extendVectorZero f)
      map_add' := by
        intro f g
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        apply Filter.Eventually.of_forall
        intro x
        by_cases hx : x ∈ K
        · simp [extendVectorZero_mem _ hx]
        · simp [extendVectorZero_notMem _ hx]
      map_smul' := by
        intro a f
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        apply Filter.Eventually.of_forall
        intro x
        by_cases hx : x ∈ K
        · simp [extendVectorZero_mem _ hx]
        · simp [extendVectorZero_notMem _ hx] }
    ‖indicatorConstLp (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) 2
      hK.isClosed.measurableSet hK.measure_lt_top.ne (1 : ℝ)‖
    (fun f ↦ by
      rw [mul_comm]
      change ‖(extendVectorZero_memLp hK f).toLp (extendVectorZero f)‖ ≤ _
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(extendVectorZero_memLp hK f).coeFn_toLp,
        indicatorConstLp_coeFn (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) (p := 2)
          (hs := hK.isClosed.measurableSet)
          (hμs := hK.measure_lt_top.ne) (c := (1 : ℝ))] with x hx hy
      rw [hx, hy]
      by_cases hxK : x ∈ K
      · simp only [extendVectorZero_mem _ hxK, indicator_of_mem hxK, norm_one, mul_one]
        exact f.norm_coe_le_norm _
      · simp [extendVectorZero_notMem _ hxK, indicator_of_notMem hxK])



open JanetCartan.ResponseTransfer.ParameterRealization.L2Family

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {U : Set P} {g : P → EuclideanSpace ℝ (Fin n) → F}

/-- The compact graph output lifted into actual Lebesgue L², with a harmless
zero default for nonsmooth slices outside the parameter neighborhood.
Consumer: `iteratedFDeriv_compactVectorL2Family_ae` in the parameter-complement
paragraph of `app:ch_response:thm:response-literal-transfer`. -/
def compactVectorL2Family (g : P → EuclideanSpace ℝ (Fin n) → F) :
    P → Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  compactVectorToL2 hK ∘ compactFamily (K := K) g

/-- Joint primitive regularity implies smoothness of the L² family on the
original open parameter set (`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiffOn_compactVectorL2Family (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (compactVectorL2Family hK g) U := by
  apply contDiffOn_infty.mpr
  intro k c hc
  exact ((compactVectorToL2 hK).contDiff.contDiffAt.comp c
    (compactFamily_contDiffAt k hU hg hc)).contDiffWithinAt

/-- The L² lift represents the original compact output, rather than a newly
chosen graph (`app:ch_response:thm:response-literal-transfer`). -/
theorem compactVectorL2Family_ae
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ univ))
    (hs : ∀ a ∈ U, ∀ x ∉ K, g a x = 0) {c : P} (hc : c ∈ U) :
    compactVectorL2Family hK g c =ᵐ[volume] g c := by
  filter_upwards [(extendVectorZero_memLp hK (compactFamily g c)).coeFn_toLp] with x hx
  apply hx.trans
  by_cases hxK : x ∈ K
  · rw [extendVectorZero_mem _ hxK]
    exact compactFamily_apply hg hc ⟨x, hxK⟩
  · rw [extendVectorZero_notMem _ hxK, hs c hc x hxK]

/-- All actual L² derivatives have the actual pointwise derivative as a
representative. The uniform-norm differentiation is proved by the shared
compact-family leaf; no L² derivative is assumed
(`app:ch_response:thm:response-literal-transfer`). -/
theorem iteratedFDeriv_compactVectorL2Family_ae (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ univ))
    (hs : ∀ a ∈ U, ∀ x ∉ K, g a x = 0)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ U) :
    iteratedFDeriv ℝ k (compactVectorL2Family hK g) c v =ᵐ[volume]
      fun x ↦ iteratedFDeriv ℝ k (fun a ↦ g a x) c v := by
  have hh := (compactVectorToL2 hK).iteratedFDeriv_comp_left
    (compactFamily_contDiffAt k hU hg hc) (le_refl (k : ℕ∞ω))
  change iteratedFDeriv ℝ k (compactVectorToL2 hK ∘ compactFamily g) c v =ᵐ[volume] _
  rw [hh]
  filter_upwards [(extendVectorZero_memLp hK
    (iteratedFDeriv ℝ k (compactFamily g) c v)).coeFn_toLp] with x hx
  apply hx.trans
  by_cases hxK : x ∈ K
  · rw [extendVectorZero_mem _ hxK]
    have heval := (ContinuousMap.evalCLM ℝ (⟨x, hxK⟩ : K) (M := F)).iteratedFDeriv_comp_left
      (compactFamily_contDiffAt k hU hg hc) (le_refl (k : ℕ∞ω))
    have he : (ContinuousMap.evalCLM ℝ (⟨x, hxK⟩ : K) ∘ compactFamily g) =ᶠ[𝓝 c]
        (fun a ↦ g a x) := by
      filter_upwards [hU.mem_nhds hc] with a ha
      exact compactFamily_apply hg ha ⟨x, hxK⟩
    rw [(he.iteratedFDeriv ℝ k).eq_of_nhds] at heval
    exact (congrArg (fun m ↦ m v) heval).symm
  · rw [extendVectorZero_notMem _ hxK]
    have he : (fun a ↦ g a x) =ᶠ[𝓝 c] fun _ ↦ (0 : F) := by
      filter_upwards [hU.mem_nhds hc] with a ha
      exact hs a ha x hxK
    rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
    cases k <;> simp

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.Hilbert
