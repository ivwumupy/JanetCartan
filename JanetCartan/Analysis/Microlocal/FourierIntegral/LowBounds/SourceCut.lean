module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.Extension

/-!
# Exact physical source cutting of the pure graph

For actual-calculus Step 1 (`app:ch_regular_base:thm:actual-calculus`), the
source-cut graph is `T.comp Mχ` and its literal Hilbert adjoint is
`Mχ.comp T.adjoint` for a real cutoff. The full source-dependent amplitude
retains this physical factor. Its normal is not identified with the pure normal.
The consumer supplies `T` and its realization from the low-bound construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped ContDiff ComplexInnerProductSpace ENNReal
namespace JanetCartan.FourierIntegral.LowBounds
open FrequencyCutoff
variable {n r : ℕ}
local notation "ℰ" => Euclidean n
local notation "𝒱" => EuclideanSpace ℂ (Fin r)
local notation "ℋ" => Lp 𝒱 2 (volume : Measure ℰ)

/-- The actual real physical source cutoff on the same vector Lebesgue L²;
consumer: the source-cut specialization of actual-calculus Step 1. -/
def sourceCutMultiplier (χ : ℰ → ℝ) (hχ : Continuous χ) (hb : ∀ x, ‖χ x‖ ≤ 1) : ℋ →L[ℂ] ℋ :=
  (ContinuousLinearMap.lsmul ℂ ℂ (E := 𝒱)).holderL volume ∞ 2 2
    ((memLp_top_of_bound (Complex.continuous_ofReal.comp hχ).aestronglyMeasurable 1
      (Eventually.of_forall (fun x ↦ by simpa using hb x))).toLp (fun x ↦ (χ x : ℂ)))

/-- Literal multiplication by the physical cutoff, for
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem sourceCutMultiplier_coeFn (χ : ℰ → ℝ) (hχ : Continuous χ)
    (hb : ∀ x, ‖χ x‖ ≤ 1) (f : ℋ) :
    sourceCutMultiplier χ hχ hb f =ᵐ[volume] fun x ↦ (χ x : ℂ) • f x := by
  let hm : MemLp (fun x ↦ (χ x : ℂ)) ∞ (volume : Measure ℰ) :=
    memLp_top_of_bound (Complex.continuous_ofReal.comp hχ).aestronglyMeasurable 1
      (Eventually.of_forall (fun x ↦ by simpa using hb x))
  filter_upwards [(ContinuousLinearMap.lsmul ℂ ℂ (E := 𝒱)).coeFn_holder
    (r := 2) (hm.toLp (fun x ↦ (χ x : ℂ))) f, hm.coeFn_toLp] with x hx hc
  exact hx.trans (congrArg (fun c : ℂ ↦ c • f x) hc)

/-- The real physical cutoff is contractive (same Step 1). -/
theorem norm_sourceCutMultiplier_le (χ : ℰ → ℝ) (hχ : Continuous χ)
    (hb : ∀ x, ‖χ x‖ ≤ 1) : ‖sourceCutMultiplier (r := r) χ hχ hb‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [sourceCutMultiplier_coeFn χ hχ hb f] with x hx
  rw [hx, norm_smul, Complex.norm_real]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb x)

/-- Reality of the physical source cutoff gives its exact Hilbert adjoint;
consumer: the literal source-cut adjoint in actual-calculus Step 1. -/
theorem sourceCutMultiplier_adjoint (χ : ℰ → ℝ) (hχ : Continuous χ)
    (hb : ∀ x, ‖χ x‖ ≤ 1) :
    (sourceCutMultiplier (r := r) χ hχ hb).adjoint = sourceCutMultiplier χ hχ hb := by
  apply LinearMap.IsSymmetric.clm_adjoint_eq
  intro f g
  change ⟪sourceCutMultiplier χ hχ hb f, g⟫ = ⟪f, sourceCutMultiplier χ hχ hb g⟫
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sourceCutMultiplier_coeFn χ hχ hb f,
    sourceCutMultiplier_coeFn χ hχ hb g] with x hf hg
  rw [hf, hg, inner_smul_left, inner_smul_right]
  simp

/-- The actual cutoff preserves the existing compact smooth test space;
consumer: exact realization of the source-cut graph in Step 1. -/
def sourceCutTest (χ : ℰ → ℝ) (hχ : ContDiff ℝ ∞ χ) (u : graphTestSpace n r) :
    graphTestSpace n r :=
  ⟨fun y ↦ (χ y : ℂ) • u.val y,
    (Complex.ofRealCLM.contDiff.comp hχ).smul u.property.1, u.property.2.smul_left (f := fun y ↦ (χ y : ℂ))⟩

/-- The source-cut test and actual L² multiplier have the same representative
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem sourceCutMultiplier_graphTestToLp (χ : ℰ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hb : ∀ x, ‖χ x‖ ≤ 1) (u : graphTestSpace n r) :
    sourceCutMultiplier χ hχ.continuous hb (graphTestToLp u) =
      graphTestToLp (sourceCutTest χ hχ u) := by
  apply Lp.ext
  filter_upwards [sourceCutMultiplier_coeFn χ hχ.continuous hb (graphTestToLp u),
    (graphTest_memLp u).coeFn_toLp, (graphTest_memLp (sourceCutTest χ hχ u)).coeFn_toLp]
    with x hx hu hc
  exact hx.trans ((congrArg (fun v : 𝒱 ↦ (χ x : ℂ) • v) hu).trans hc.symm)

/-- Exact full-amplitude meaning of the source-cut graph, from the realized
pure graph. The physical source factor is retained in the literal integral;
no pure-normal replacement is made. Source:
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem sourceCutGraph_ae_graphOperator
    (S : ℰ → ℰ → ℝ) (A : ℰ → ℰ → Matrix (Fin r) (Fin r) ℂ)
    (T : ℋ →L[ℂ] ℋ)
    (hT : ∀ u : graphTestSpace n r, T (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η)
        (graphTestToSchwartz u) x))
    (χ : ℰ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hb : ∀ x, ‖χ x‖ ≤ 1)
    (u : graphTestSpace n r) :
    (T.comp (sourceCutMultiplier χ hχ.continuous hb)) (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator S (fun x y η ↦ (χ y : ℂ) • A x η)
        (graphTestToSchwartz u) x) := by
  change T (sourceCutMultiplier χ hχ.continuous hb (graphTestToLp u)) =ᵐ[volume] _
  rw [sourceCutMultiplier_graphTestToLp χ hχ hb u]
  refine (hT (sourceCutTest χ hχ u)).trans (Eventually.of_forall ?_)
  intro x
  exact congrArg (WithLp.toLp 2) (congrFun (graphOperator_source_mul S
    (fun z _ η ↦ A z η) (fun y ↦ (χ y : ℂ)) (graphTestToSchwartz u)) x)

/-- Exact composition formula for the literal Hilbert adjoint of the
source-cut graph; it is not the paper's weighted inverse. Source:
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem sourceCutGraph_adjoint (T : ℋ →L[ℂ] ℋ) (χ : ℰ → ℝ)
    (hχ : Continuous χ) (hb : ∀ x, ‖χ x‖ ≤ 1) :
    (T.comp (sourceCutMultiplier χ hχ hb)).adjoint =
      (sourceCutMultiplier χ hχ hb).comp T.adjoint := by
  rw [ContinuousLinearMap.adjoint_comp, sourceCutMultiplier_adjoint]

/-- Source cutting preserves the established low graph bound (same Step 1). -/
theorem norm_sourceCutGraph_le (T : ℋ →L[ℂ] ℋ) (χ : ℰ → ℝ)
    (hχ : Continuous χ) (hb : ∀ x, ‖χ x‖ ≤ 1) :
    ‖T.comp (sourceCutMultiplier χ hχ hb)‖ ≤ ‖T‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) (norm_sourceCutMultiplier_le χ hχ hb))

/-- The literal source-cut adjoint has the same low bound (same Step 1). -/
theorem norm_sourceCutGraph_adjoint_le (T : ℋ →L[ℂ] ℋ) (χ : ℰ → ℝ)
    (hχ : Continuous χ) (hb : ∀ x, ‖χ x‖ ≤ 1) :
    ‖(T.comp (sourceCutMultiplier χ hχ hb)).adjoint‖ ≤ ‖T‖ := by
  simpa only [LinearIsometryEquiv.norm_map] using norm_sourceCutGraph_le T χ hχ hb

end JanetCartan.FourierIntegral.LowBounds
