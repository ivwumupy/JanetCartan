module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceGeometry.Domains

/-!
# Fixed ball geometry for raw physical slices

The geometric sets of `app:ch_osc:setup:osc-normal` are fixed before the current
immersion. This constructor proves their geometric fields and retains the full
normalized input support. The inverse image domain, buffer and determinant gap
must still be chosen and proved valid for the canonical phase; those assertions
are fields of `UniformNormalData`, not consequences of this constructor.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.RawPrimary.SliceGeometry
open NormalComparison SliceBounds

private theorem thickening_closedBall_subset_ball {d : ℕ} {r b R : ℝ}
    (hb : 0 ≤ b) (hR : r + b < R) :
    cthickening b (closedBall (0 : Euclidean d) r) ⊆ ball 0 R := by
  rw [(isCompact_closedBall (0 : Euclidean d) r).cthickening_eq_biUnion_closedBall hb]
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
  exact ((dist_triangle x y 0).trans
    (add_le_add (mem_closedBall.mp hxy) (mem_closedBall.mp hy))).trans_lt (by linarith)

/-- The fixed spatial core has a positive closed buffer in the convex open
spatial box (`app:ch_osc:setup:osc-normal`). -/
theorem sliceSpatialCore_buffer {n : ℕ} {a : ℝ} (ha : 0 < a) :
    cthickening (a / 4) (sliceSpatialCore n a) ⊆ sliceSpatialDomain n a :=
  thickening_closedBall_subset_ball (by positivity) (by linarith)

/-- The entire radius-two input core has a positive closed buffer in the
convex input domain (`app:ch_waves:setup:oscillatory`). -/
theorem sliceInputCore_buffer {n : ℕ} :
    cthickening (1 / 4) (sliceInputCore n) ⊆ sliceInputDomain n :=
  thickening_closedBall_subset_ball (by norm_num) (by norm_num)

/-- Fixed sets and elementary buffers for the actual raw-slice construction.
`V`, `β`, and `c` are to be supplied by the canonical transverse inverse
construction. This definition asserts no injectivity, chart-image containment,
or phase estimates (`app:ch_osc:setup:osc-normal`). -/
def sliceNormalGeometry {n : ℕ} (hn : 2 ≤ n) {a e β c : ℝ}
    (ha : 0 < a) (he : 0 < e) (hβ : 0 < β) (hc : 0 < c)
    (V : Set (Euclidean (n - 1))) (hV : IsOpen V) (hVc : IsCompact (closure V)) :
    UniformNormalGeometry (n - 1) (embeddingDimension n * n) where
  dimension_pos := by omega
  rank_pos := by
    have hprod : 2 ≤ n * (n + 1) := by nlinarith
    have hdim : 1 ≤ embeddingDimension n := by unfold embeddingDimension; omega
    nlinarith
  X := sliceSpatialDomain n a
  D := sliceInputDomain n
  X₀ := sliceSpatialCore n a
  D₀ := sliceInputCore n
  V := V
  isOpen_X := isOpen_ball
  isOpen_D := isOpen_ball
  convex_X := convex_ball _ _
  convex_D := convex_ball _ _
  bounded_X := isBounded_ball
  bounded_D := isBounded_ball
  compact_X₀ := isCompact_closedBall _ _
  compact_D₀ := isCompact_closedBall _ _
  isOpen_V := hV
  compact_closure_V := hVc
  ε₀ := e
  spatialBuffer := a / 4
  inputBuffer := 1 / 4
  inverseBuffer := β
  gap := c
  ε₀_pos := he
  spatialBuffer_pos := by positivity
  inputBuffer_pos := by norm_num
  inverseBuffer_pos := hβ
  gap_pos := hc
  spatial_buffer := sliceSpatialCore_buffer ha
  input_buffer := sliceInputCore_buffer

/-- The sharp phase cost for a slice jet and its first epsilon derivative
fits the original raw-family reserve. The analytic cost is proved by
`exists_canonicalSlicePhase_input_budgets` and used by the normal-data assembly
(`app:ch_waves:setup:oscillatory`, `app:ch_waves:thm:wkb`). -/
theorem slicePhaseJetOrder_le_rawReserve {n k : ℕ} (hk : k ≤ 20 * ((n - 1) + 1)) :
    k + 5 ≤ 14 + (rawSliceParameterOrder n + 2) := by
  simp only [rawSliceParameterOrder, rawSliceJetOrder]
  omega

/-- The original immersion profile supplies the fixed low budget required
by the finite slice phase estimates, independently of the frequency scale.
This uses the SAME reserve as `exists_finite_actual_graded_raw_family`
(`app:ch_waves:eq:individual-grading`). -/
theorem slicePhaseBudget_of_derivativeProfile {n N RF : ℕ}
    {K : Set (Euclidean n)} {F : Euclidean n → Euclidean N} {L : ℝ} {AF : ℕ → ℝ}
    (hreserve : 14 + (rawSliceParameterOrder n + 2) ≤ RF)
    (hprofile : HasDerivativeProfile K F RF L AF) :
    cNorm K (20 * ((n - 1) + 1) + 5) F ≤ AF (20 * ((n - 1) + 1) + 5) := by
  have horder := (slicePhaseJetOrder_le_rawReserve (n := n) le_rfl).trans hreserve
  simpa only [Nat.sub_eq_zero_of_le horder, pow_zero, mul_one] using
    hprofile (20 * ((n - 1) + 1) + 5)

end JanetCartan.RawPrimary.SliceGeometry
