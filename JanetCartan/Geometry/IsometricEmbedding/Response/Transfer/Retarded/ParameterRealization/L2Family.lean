module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.ParameterRealization.ClassicalFields
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.ParameterRealization.L2Family.CompactFamily
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.ParameterRealization.L2Family.Extension


/-!
# L2 parameter families

The parameter paragraph of `app:ch_response:thm:response-literal-transfer`.
Classical joint smoothness with a fixed compact spatial support gives smoothness
in actual Lebesgue L2 at every finite order. The evaluated iterated L2 derivative
is the `MemLp.toLp` class of the actual pointwise parameter derivative.

The proof first differentiates in the uniform norm on the compact support, then
composes with bounded linear zero extension into L2. The parent supplies global
`hmem` using `Spaces.jet_memLp`; no norm differentiability is assumed here.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.ParameterRealization
variable {p d : ℕ}

/-- Every actual pointwise parameter derivative is in Lebesgue `L2`, by its
continuity and fixed compact support
(`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterField_memLp {U : Set (Euclidean p)} (hU : IsOpen U)
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K)
    {f : Euclidean p → (ℝ × (Fin d → ℝ)) → ℂ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ univ))
    (hs : ∀ a ∈ U, tsupport (f a) ⊆ K)
    (k : ℕ) (v : Fin k → Euclidean p) {c : Euclidean p} (hc : c ∈ U) :
    MemLp (parameterField f k v c) 2 volume := by
  apply Continuous.memLp_of_hasCompactSupport
  · exact (contDiff_parameterField hU hf k v hc).continuous
  · exact hasCompactSupport_parameterField hU hK hs k v hc

open L2Family
variable {U : Set (Euclidean p)} {K : Set ((Fin d → ℝ) × ℝ)}
  {g : Euclidean p → ((Fin d → ℝ) × ℝ) → ℂ}

private lemma compact_iterated_apply [CompactSpace K] (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ univ))
    (k : ℕ) (v : Fin k → Euclidean p) {c : Euclidean p} (hc : c ∈ U) (x : K) :
    (iteratedFDeriv ℝ k (compactFamily (K := K) g) c v) x =
      iteratedFDeriv ℝ k (fun a ↦ g a x) c v := by
  have hh := (ContinuousMap.evalCLM ℝ x (M := ℂ)).iteratedFDeriv_comp_left
    (compactFamily_contDiffAt k hU hg hc) (le_refl (k : ℕ∞ω))
  have he : ((ContinuousMap.evalCLM ℝ x (M := ℂ)) ∘ compactFamily (K := K) g) =ᶠ[𝓝 c]
      (fun a ↦ g a x) := by
    filter_upwards [hU.mem_nhds hc] with a ha
    exact compactFamily_apply hg ha x
  rw [he.iteratedFDeriv ℝ k |>.eq_of_nhds] at hh
  exact (congrArg (fun m ↦ m v) hh).symm

private lemma differential_zero (hU : IsOpen U)
    (hs : ∀ a ∈ U, tsupport (g a) ⊆ K)
    (k : ℕ) (v : Fin k → Euclidean p) {c : Euclidean p} (hc : c ∈ U)
    {x : (Fin d → ℝ) × ℝ} (hx : x ∉ K) :
    iteratedFDeriv ℝ k (fun a ↦ g a x) c v = 0 := by
  have he : (fun a ↦ g a x) =ᶠ[𝓝 c] (fun _ ↦ (0 : ℂ)) := by
    filter_upwards [hU.mem_nhds hc] with a ha
    exact image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs a ha h))
  rw [he.iteratedFDeriv ℝ k |>.eq_of_nhds]
  cases k with
  | zero => exact iteratedFDeriv_zero_apply _
  | succ k => simp

private lemma extension_differential [CompactSpace K] (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ univ))
    (hs : ∀ a ∈ U, tsupport (g a) ⊆ K)
    (k : ℕ) (v : Fin k → Euclidean p) {c : Euclidean p} (hc : c ∈ U) :
    extendZero (iteratedFDeriv ℝ k (compactFamily (K := K) g) c v) =
      fun x ↦ iteratedFDeriv ℝ k (fun a ↦ g a x) c v := by
  funext x
  by_cases hx : x ∈ K
  · rw [extendZero_mem _ hx]
    exact compact_iterated_apply hU hg k v hc ⟨x, hx⟩
  · rw [extendZero_notMem _ hx, differential_zero hU hs k v hc hx]

/-- The actual pointwise parameter derivative belongs to Lebesgue L2, for every
finite order and every tuple of directions
(`app:ch_response:thm:response-literal-transfer`). This is the representative
used by `iteratedFDeriv_toLp_eq_toLp_parameterDeriv`. -/
theorem memLp_iteratedParameterDeriv (hU : IsOpen U) (hK : IsCompact K)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ univ))
    (hs : ∀ a ∈ U, tsupport (g a) ⊆ K)
    (k : ℕ) (v : Fin k → Euclidean p) {c : Euclidean p} (hc : c ∈ U) :
    MemLp (fun x ↦ iteratedFDeriv ℝ k (fun a ↦ g a x) c v) 2 volume := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [← extension_differential hU hg hs k v hc]
  exact extendZero_memLp hK _

private lemma extension_family [CompactSpace K] (hK : IsCompact K)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ univ))
    (hs : ∀ a ∈ U, tsupport (g a) ⊆ K)
    (hmem : ∀ a, MemLp (g a) 2 volume) {c : Euclidean p} (hc : c ∈ U) :
    compactToL2 hK (compactFamily (K := K) g c) = (hmem c).toLp (g c) := by
  change (extendZero_memLp hK _).toLp _ = _
  apply MemLp.toLp_congr
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · rw [extendZero_mem _ hx]
    exact compactFamily_apply hg hc ⟨x, hx⟩
  · rw [extendZero_notMem _ hx]
    exact (image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs c hc h))).symm

/-- A jointly smooth family with common compact support is smooth into actual
Lebesgue L2 at every finite order
(`app:ch_response:thm:response-literal-transfer`). The global `hmem` supplies
representatives outside the parameter domain; the norm differentiability on
the domain is proved from the classical hypotheses. -/
theorem contDiffAt_toLp_of_contDiffOn_commonCompactSupport (hU : IsOpen U) (hK : IsCompact K)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ univ))
    (hs : ∀ a ∈ U, tsupport (g a) ⊆ K)
    (hmem : ∀ a, MemLp (g a) 2 volume)
    (k : ℕ) {c : Euclidean p} (hc : c ∈ U) :
    ContDiffAt ℝ k (fun a ↦ (hmem a).toLp (g a)) c := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply ((compactToL2 hK).contDiff.contDiffAt.comp c
    (compactFamily_contDiffAt k hU hg hc)).congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hc] with a ha
  exact (extension_family hK hg hs hmem ha).symm

/-- Evaluating the iterated L2 derivative gives exactly the class of the actual
pointwise parameter derivative
(`app:ch_response:thm:response-literal-transfer`). This is the L2 identity
consumed by the parent construction in the closed Sobolev jet completion. -/
theorem iteratedFDeriv_toLp_eq_toLp_parameterDeriv (hU : IsOpen U) (hK : IsCompact K)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ univ))
    (hs : ∀ a ∈ U, tsupport (g a) ⊆ K)
    (hmem : ∀ a, MemLp (g a) 2 volume)
    (k : ℕ) (v : Fin k → Euclidean p) {c : Euclidean p} (hc : c ∈ U) :
    iteratedFDeriv ℝ k (fun a ↦ (hmem a).toLp (g a)) c v =
      (memLp_iteratedParameterDeriv hU hK hg hs k v hc).toLp
        (fun x ↦ iteratedFDeriv ℝ k (fun a ↦ g a x) c v) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have he : (compactToL2 hK ∘ compactFamily (K := K) g) =ᶠ[𝓝 c]
      (fun a ↦ (hmem a).toLp (g a)) := by
    filter_upwards [hU.mem_nhds hc] with a ha
    exact extension_family hK hg hs hmem ha
  have hh := (compactToL2 hK).iteratedFDeriv_comp_left
    (compactFamily_contDiffAt k hU hg hc) (le_refl (k : ℕ∞ω))
  rw [he.iteratedFDeriv ℝ k |>.eq_of_nhds] at hh
  rw [hh]
  change (extendZero_memLp hK _).toLp _ = _
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall (congrFun (extension_differential hU hg hs k v hc))
end JanetCartan.ResponseTransfer.ParameterRealization
