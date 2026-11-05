module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs
public import JanetCartan.Geometry.IsometricEmbedding.Basic

/-!
# One physical output cutoff and chart zero extension

The fixed output cutoff of `app:ch_pairs:prop:pairs-lag-sum`, also used to put
`app:ch_response:prop:response-ambient` into the whole-function-space interface
of `CorrectedAtoms.realCorrectedAtomicFamily`. Only geometric cutoff data are
stored. Smoothness of a response is proved from its actual chart representative.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ResponseSourceExtension

/-- Fixed geometric output data for `app:ch_pairs:prop:pairs-lag-sum`.
The core has a neighborhood on which the cutoff is one. -/
structure OutputCutoff {n : ℕ} (core chart : Set (Euclidean n)) where
  toFun : Euclidean n → ℝ
  smooth : ContDiff ℝ ∞ toFun
  compact : HasCompactSupport toFun
  support_chart : tsupport toFun ⊆ chart
  plateau : core ⊆ interior {x | toFun x = 1}

/-- Construct the output cutoff from the fixed compact core and open validity
chart, before all accuracy orders and samples (`app:ch_pairs:prop:pairs-lag-sum`). -/
theorem nonempty_outputCutoff {n : ℕ} {core chart : Set (Euclidean n)}
    (hc : IsCompact core) (ho : IsOpen chart) (hco : core ⊆ chart) :
    Nonempty (OutputCutoff core chart) := by
  obtain ⟨χ, hs, _, hk, ht, hp⟩ :=
    CompatibleResponse.exists_compact_family_cutoff hc ho hco
  exact ⟨⟨χ, hs, hk, ht, hp⟩⟩

namespace OutputCutoff

variable {n : ℕ} {core chart : Set (Euclidean n)} (χ : OutputCutoff core chart)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Cut off a chart-valued output and extend it by zero. This is a literal
pointwise linear map, with no `Lp.toLp` convention (`main:thm:step`). -/
def zeroExtend : (chart → V) →ₗ[ℝ] (Euclidean n → V) := by
  classical
  exact {
  toFun v x := if hx : x ∈ chart then χ.toFun x • v ⟨x, hx⟩ else 0
  map_add' v w := by
    ext x
    by_cases hx : x ∈ chart <;> simp [hx, smul_add]
  map_smul' a v := by
    ext x
    by_cases hx : x ∈ chart <;> simp [hx, smul_smul, mul_comm] }

/-- The cutoff chart extension is precisely multiplication by the same physical
cutoff whenever a representative is available (`app:ch_pairs:prop:pairs-lag-sum`). -/
theorem zeroExtend_restrict (v : Euclidean n → V) :
    χ.zeroExtend (fun x : chart ↦ v x) = fun x ↦ χ.toFun x • v x := by
  classical
  funext x
  change (if hx : x ∈ chart then χ.toFun x • v x else 0) = _
  split_ifs with hx
  · rfl
  · have hz : χ.toFun x = 0 := by
      by_contra h
      exact hx (χ.support_chart (subset_tsupport _ h))
    simp [hz]

/-- All extended outputs retain the fixed compact support, including algebraic
extensions outside the smooth source domain (`main:thm:step`). -/
theorem tsupport_zeroExtend_subset (v : chart → V) :
    tsupport (χ.zeroExtend v) ⊆ tsupport χ.toFun := by
  apply closure_mono
  intro x hx
  change χ.toFun x ≠ 0
  intro hz
  apply hx
  simp [zeroExtend, hz]

/-- Compact support of the literal cutoff extension
(`app:ch_pairs:prop:pairs-lag-sum`). -/
theorem hasCompactSupport_zeroExtend (v : chart → V) :
    HasCompactSupport (χ.zeroExtend v) :=
  (χ.compact : IsCompact (tsupport χ.toFun)).of_isClosed_subset
    (isClosed_tsupport _) (χ.tsupport_zeroExtend_subset v)

/-- A smooth chart representative gives a globally smooth cutoff zero extension.
Near the chart boundary the output vanishes on a neighborhood, because the
closed support of the fixed cutoff lies inside the chart
(`app:ch_pairs:prop:pairs-lag-sum`). -/
theorem contDiff_zeroExtend_restrict (ho : IsOpen chart) {v : Euclidean n → V}
    (hv : ContDiffOn ℝ ∞ v chart) :
    ContDiff ℝ ∞ (χ.zeroExtend (fun x : chart ↦ v x)) := by
  rw [χ.zeroExtend_restrict]
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ.toFun
  · exact χ.smooth.contDiffAt.smul
      ((hv x (χ.support_chart hx)).contDiffAt (ho.mem_nhds (χ.support_chart hx)))
  · apply (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [hy]

/-- Exact equality on a neighborhood of each core point, preserving every
local derivative (`app:ch_response:prop:response-ambient`). -/
theorem zeroExtend_eventuallyEq (v : Euclidean n → V) {x : Euclidean n}
    (hx : x ∈ core) :
    χ.zeroExtend (fun y : chart ↦ v y) =ᶠ[𝓝 x] v := by
  rw [χ.zeroExtend_restrict]
  filter_upwards [isOpen_interior.mem_nhds (χ.plateau hx)] with y hy
  have h : y ∈ {x | χ.toFun x = 1} := interior_subset hy
  change χ.toFun y = 1 at h
  simp [h]

end OutputCutoff
end JanetCartan.ResponseSourceExtension
