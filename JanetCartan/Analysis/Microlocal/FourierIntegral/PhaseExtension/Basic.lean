module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.Kernel
public import JanetCartan.Analysis.Microlocal.Localization.CompactSupport
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Extending a phase across the complement of its buffered chart

The compact graph construction in actual-calculus Step 1 requires a globally
continuous phase. A local conic phase need not satisfy that requirement.
Here a smooth extension is constructed from a closed supported chart inside
its open smoothness domain. The extension agrees on a neighborhood of the
whole closed chart, which may be unbounded in frequency. No regularity at
zero or outside the original chart is assumed. The construction is used only
to realize the supported kernels; no global homogeneous or symbol bounds for
the auxiliary extension are asserted.
-/

@[expose] public noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- A globally smooth auxiliary phase agreeing locally with the original on
every point of a closed buffered chart, including its noncompact conic tail.
This supplies the global continuity required by `LowBounds` while retaining
all original jets on the supported chart. Source:
`app:ch_regular_base:thm:actual-calculus`, Steps 1--2. -/
theorem exists_smooth_phase_extension
    (S : E → E → ℝ) {K O : Set (E × E)}
    (hK : IsClosed K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) O) :
    ∃ S' : E → E → ℝ, ContDiff ℝ ∞ (Function.uncurry S') ∧
      ∀ q ∈ K, Function.uncurry S' =ᶠ[𝓝 q] Function.uncurry S := by
  obtain ⟨U, hU, hKU, hUO⟩ := normal_exists_closure_subset hK hO hKO
  obtain ⟨V, hV, hUV, hVO⟩ := normal_exists_closure_subset isClosed_closure hO hUO
  obtain ⟨χ, hχ, _, hsχ, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV isClosed_closure hUV
  refine ⟨fun x η ↦ χ (x, η) * S x η, ?_, ?_⟩
  · apply Localization.contDiff_of_contDiffOn_support_neighborhood hO
    · exact hχ.contDiffOn.mul hS
    · exact (tsupport_mul_subset_left).trans (by simpa only [tsupport, hsχ] using hVO)
  · intro q hq
    filter_upwards [hU.mem_nhds (hKU hq)] with p hp
    change χ p * S p.1 p.2 = S p.1 p.2
    rw [(hχone p).mp (subset_closure hp), one_mul]

/-- Every phase jet on the buffered chart is unchanged by an extension that
agrees on a neighborhood. This does not assert estimates off the chart.
Source: `app:ch_regular_base:eq:actual-one-high`. -/
theorem phase_jet_eq_of_eventuallyEq {S S' : E → E → ℝ} {q : E × E}
    (h : Function.uncurry S' =ᶠ[𝓝 q] Function.uncurry S) (k : ℕ) :
    iteratedFDeriv ℝ k (Function.uncurry S') q =
      iteratedFDeriv ℝ k (Function.uncurry S) q :=
  (h.iteratedFDeriv ℝ k).eq_of_nhds

/-- The literal full graph integral depends only on phase values where its
amplitude is nonzero. This holds before any convergence argument and retains
all source and frequency cutoffs. Source:
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem graphOperator_phase_congr (S S' : E → E → ℝ) (A : FullAmplitude n r)
    (h : ∀ x y η, A x y η ≠ 0 → S' x η = S x η)
    (v : E → Fin r → ℂ) : graphOperator S' A v = graphOperator S A v := by
  funext x
  unfold graphOperator
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with η
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with y
  by_cases ha : A x y η = 0
  · simp only [ha, Matrix.zero_mulVec, smul_zero]
  · rw [graphOscillation, graphOscillation, h x y η ha]

end JanetCartan.FourierIntegral
