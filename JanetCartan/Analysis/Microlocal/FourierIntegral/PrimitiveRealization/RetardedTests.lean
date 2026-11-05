module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.PrimitiveRealization.SourceConjugation
public import JanetCartan.Analysis.Operator.RetardedSobolev.Smooth
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PhysicalCoordinates

/-!
# Characteristic integration on the actual graph test space

The time variable is a selected Euclidean coordinate. The existing coordinate
split and the literal finite-time primitive construct `𝒥 = i J` on the same
compact smooth vector tests used by the graph realizations. Differentiation
keeps the exterior-cutoff term. Nested source plateaux remove that term only
after source multiplication, as required by
`app:ch_regular_base:eq:DJ-identity`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

open Set MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.FourierIntegral

open LowBounds SupportedConjugation RegularSector.Characteristic

variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "L²" => Lp V 2 (volume : Measure E)

/-- The literal source-weighted primitive in the selected canonical time.
Consumer: the integral in `app:ch_regular_base:eq:characteristic-integral`. -/
def graphRetardedPrimitive (t : Fin (d + 1)) (a : ℝ) (χin : E → ℝ)
    (f : E → V) (x : E) : V :=
  ∫ s in a..x t,
    (χin ((coordinateSplit t).symm (s, (coordinateSplit t x).2)) : ℂ) •
      f ((coordinateSplit t).symm (s, (coordinateSplit t x).2))

/-- The buffered characteristic integral, with the manuscript's factor `i`.
Consumer: the exact local product in `app:ch_regular_base:eq:local-exact-product`. -/
def graphRetardedIntegral (t : Fin (d + 1)) (a : ℝ) (χin χout : E → ℝ)
    (f : E → V) (x : E) : V :=
  Complex.I • ((χout x : ℂ) • graphRetardedPrimitive t a χin f x)

/-- Joint smoothness of the actual vector primitive, using the shared moving
endpoint theorem. Source: `app:ch_regular_base:eq:characteristic-integral`. -/
theorem contDiff_graphRetardedPrimitive (t : Fin (d + 1)) (a : ℝ)
    {χin : E → ℝ} {f : E → V} (hin : ContDiff ℝ ∞ χin)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (graphRetardedPrimitive t a χin f) := by
  let e := coordinateSplit t
  have hg : ContDiff ℝ ∞ (fun p : ℝ × Euclidean d ↦
      (χin (e.symm p) : ℂ) • f (e.symm p)) :=
    ((Complex.ofRealCLM.contDiff.comp hin).comp e.symm.contDiff).smul
      (hf.comp e.symm.contDiff)
  exact (RetardedSobolev.contDiff_lowerPrimitive_joint a hg).comp e.contDiff

/-- The buffered primitive is smooth and supported in its exterior cutoff.
Source: `app:ch_regular_base:eq:characteristic-integral`. -/
theorem contDiff_graphRetardedIntegral (t : Fin (d + 1)) (a : ℝ)
    {χin χout : E → ℝ} {f : E → V} (hin : ContDiff ℝ ∞ χin)
    (hout : ContDiff ℝ ∞ χout) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (graphRetardedIntegral t a χin χout f) :=
  ((Complex.ofRealCLM.contDiff.comp hout).smul
    (contDiff_graphRetardedPrimitive t a hin hf)).const_smul Complex.I

/-- The same characteristic integral acts on the existing Euclidean graph
tests; no new canonical measure or test model is introduced.
Source: `app:ch_regular_base:eq:characteristic-integral`. -/
def graphRetardedTest (t : Fin (d + 1)) (a : ℝ) (χin χout : E → ℝ)
    (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hK : HasCompactSupport χout) (u : graphTestSpace (d + 1) r) :
    graphTestSpace (d + 1) r := by
  refine ⟨graphRetardedIntegral t a χin χout u.val,
    contDiff_graphRetardedIntegral t a hin hout u.property.1, ?_⟩
  have hc : HasCompactSupport (fun x ↦ (χout x : ℂ)) :=
    hK.comp_left Complex.ofReal_zero
  have hp : HasCompactSupport (fun x ↦ (χout x : ℂ) •
      graphRetardedPrimitive t a χin u.val x) := hc.smul_right
  exact hp.smul_left (f := fun _ : E ↦ Complex.I)

private theorem partialDeriv_graphRetardedPrimitive (t : Fin (d + 1)) (a : ℝ)
    {χin : E → ℝ} {f : E → V} (hin : ContDiff ℝ ∞ χin)
    (hf : ContDiff ℝ ∞ f) (x : E) :
    partialDeriv (graphRetardedPrimitive t a χin f) x t = (χin x : ℂ) • f x := by
  let e := coordinateSplit t
  let g : ℝ → V := fun s ↦ (χin (e.symm (s, (e x).2)) : ℂ) •
    f (e.symm (s, (e x).2))
  have hg : Continuous g :=
    (((Complex.ofRealCLM.continuous.comp hin.continuous).smul hf.continuous).comp
      (e.symm.continuous.comp (continuous_id.prodMk continuous_const)))
  have hline : HasDerivAt (fun s : ℝ ↦ e.symm (s, (e x).2))
      (EuclideanSpace.single t 1) (x t) := by
    simpa only [e, ContinuousLinearEquiv.coe_coe, Function.comp_def, id_eq,
      coordinateSplit_symm_time] using
      e.symm.hasFDerivAt.comp_hasDerivAt (x t)
        ((hasDerivAt_id (x t)).prodMk (hasDerivAt_const (x t) ((e x).2)))
  have hpoint : e.symm (x t, (e x).2) = x := e.symm_apply_apply x
  have hchain := ((contDiff_graphRetardedPrimitive t a hin hf).differentiable
    (by simp) (e.symm (x t, (e x).2))).hasFDerivAt.comp_hasDerivAt (x t) hline
  have heq : (graphRetardedPrimitive t a χin f ∘ fun s : ℝ ↦ e.symm (s, (e x).2)) =
      fun s ↦ ∫ u in a..s, g u := by
    funext s
    simp only [Function.comp_def, graphRetardedPrimitive,
      coordinateSplit_symm_fst, ContinuousLinearEquiv.apply_symm_apply, e, g]
  rw [heq, hpoint] at hchain
  exact hchain.unique ((hg.integral_hasStrictDerivAt a (x t)).hasDerivAt) |>.trans
    (by simp only [g, hpoint])

/-- Differentiation of `𝒥 = i J` by `D_t = -i ∂_t` retains the actual
exterior-cutoff derivative. It is not a global right-inverse assertion.
Source: `app:ch_regular_base:eq:DJ-identity`. -/
theorem sourceTimeTest_graphRetardedTest (t : Fin (d + 1)) (a : ℝ)
    (χin χout : E → ℝ) (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hK : HasCompactSupport χout) (u : graphTestSpace (d + 1) r) (x : E) :
    (sourceTimeTest t (graphRetardedTest t a χin χout hin hout hK u)).val x =
      (χout x : ℂ) • ((χin x : ℂ) • u.val x) +
        partialDeriv (fun y ↦ (χout y : ℂ)) x t •
          graphRetardedPrimitive t a χin u.val x := by
  change -Complex.I • partialDeriv (graphRetardedIntegral t a χin χout u.val) x t = _
  have ho : DifferentiableAt ℝ (fun y ↦ (χout y : ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp hout).differentiable (by simp) x
  have hp := (contDiff_graphRetardedPrimitive t a hin u.property.1).differentiable
    (by simp) x
  have hd := partialDeriv_graphRetardedPrimitive t a hin u.property.1 x
  dsimp only [partialDeriv] at hd
  change -Complex.I • (fderiv ℝ (fun y ↦ Complex.I • ((χout y : ℂ) •
    graphRetardedPrimitive t a χin u.val y)) x) (EuclideanSpace.single t 1) = _
  have hprod : DifferentiableAt ℝ (fun y ↦ (χout y : ℂ) •
      graphRetardedPrimitive t a χin u.val y) x := ho.smul hp
  rw [fderiv_fun_const_smul hprod Complex.I, fderiv_fun_smul ho hp]
  simp only [smul_apply, add_apply, ContinuousLinearMap.smulRight_apply,
    smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  rw [hd]
  simp only [smul_smul, partialDeriv]

/-- Each scalar coordinate is the existing literal lower retarded integral,
including its factor `i`; this identifies the vector construction with the
shared retarded API (`app:ch_regular_base:eq:characteristic-integral`). -/
theorem graphRetardedIntegral_coordinate (t : Fin (d + 1)) (a : ℝ)
    {χin : E → ℝ} (χout : E → ℝ) {f : E → V}
    (hin : Continuous χin) (hf : Continuous f) (x : E) (k : Fin r) :
    graphRetardedIntegral t a χin χout f x k =
      Complex.I * Retarded.lower a (χin ∘ (coordinateSplit t).symm)
        (χout ∘ (coordinateSplit t).symm)
        (fun p ↦ f ((coordinateSplit t).symm p) k) (coordinateSplit t x) := by
  let e := coordinateSplit t
  have hi : IntervalIntegrable (fun s ↦ (χin (e.symm (s, (e x).2)) : ℂ) •
      f (e.symm (s, (e x).2))) volume a (x t) :=
    (((Complex.continuous_ofReal.comp hin).smul hf).comp
      (e.symm.continuous.comp (continuous_id.prodMk continuous_const))).intervalIntegrable _ _
  have hc := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) k).intervalIntegral_comp_comm hi
  simpa only [graphRetardedIntegral, graphRetardedPrimitive, Retarded.lower,
    Function.comp_def, ContinuousLinearEquiv.symm_apply_apply, PiLp.smul_apply,
    smul_eq_mul, PiLp.proj_apply, coordinateSplit_fst, e] using
      congrArg (fun z : ℂ ↦ Complex.I * ((χout x : ℂ) * z)) hc.symm

/-- The literal lower endpoint is zero, before any graph factor is applied.
Source: `app:ch_regular_base:eq:characteristic-integral`. -/
theorem graphRetardedIntegral_lowerEndpoint (t : Fin (d + 1)) (a : ℝ)
    (χin χout : E → ℝ) (f : E → V) (x : E) (hx : x t = a) :
    graphRetardedIntegral t a χin χout f x = 0 := by
  simp [graphRetardedIntegral, graphRetardedPrimitive, hx]

/-- The characteristic integral is a complex-linear map on the SAME graph
tests. Source: `app:ch_regular_base:eq:QN-definition`. -/
def graphRetardedTestLinearMap (t : Fin (d + 1)) (a : ℝ) (χin χout : E → ℝ)
    (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hK : HasCompactSupport χout) :
    graphTestSpace (d + 1) r →ₗ[ℂ] graphTestSpace (d + 1) r where
  toFun := graphRetardedTest t a χin χout hin hout hK
  map_add' u v := by
    apply Subtype.ext
    funext x
    change graphRetardedIntegral t a χin χout (u.val + v.val) x =
      graphRetardedIntegral t a χin χout u.val x + graphRetardedIntegral t a χin χout v.val x
    have hi (w : graphTestSpace (d + 1) r) : IntervalIntegrable
        (fun s ↦ (χin ((coordinateSplit t).symm (s, (coordinateSplit t x).2)) : ℂ) •
          w.val ((coordinateSplit t).symm (s, (coordinateSplit t x).2))) volume a (x t) :=
      (((Complex.continuous_ofReal.comp hin.continuous).smul w.property.1.continuous).comp
        ((coordinateSplit t).symm.continuous.comp
          (continuous_id.prodMk continuous_const))).intervalIntegrable _ _
    simp only [graphRetardedIntegral, graphRetardedPrimitive, Pi.add_apply, smul_add,
      intervalIntegral.integral_add (hi u) (hi v)]
  map_smul' c u := by
    apply Subtype.ext
    funext x
    change graphRetardedIntegral t a χin χout (c • u.val) x =
      c • graphRetardedIntegral t a χin χout u.val x
    simp only [graphRetardedIntegral, graphRetardedPrimitive, Pi.smul_apply]
    simp_rw [smul_comm _ c, intervalIntegral.integral_smul]
    rw [smul_comm (χout x : ℂ) c, smul_comm Complex.I c]

/-- The nested canonical source mask removes the integration transition term
by its actual plateau. Both source multipliers are retained: the result is
`χs² u`, not `χs u`. This supplies the test-level sandwiched identity in
`app:ch_regular_base:eq:DJ-identity`; no `D_t 𝒥 = I` premise is used. -/
theorem sourceCutTest_sourceTimeTest_graphRetardedTest
    (t : Fin (d + 1)) (a : ℝ) (χin χout χs : E → ℝ)
    (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hs : ContDiff ℝ ∞ χs) (hK : HasCompactSupport χout)
    (hinput : ∀ x ∈ tsupport χs, χin x = 1)
    (houtput : ∀ x ∈ tsupport χs, χout =ᶠ[𝓝 x] fun _ ↦ 1)
    (u : graphTestSpace (d + 1) r) :
    sourceCutTest χs hs
        (sourceTimeTest t (graphRetardedTest t a χin χout hin hout hK
          (sourceCutTest χs hs u))) =
      sourceCutTest χs hs (sourceCutTest χs hs u) := by
  apply Subtype.ext
  funext x
  change (χs x : ℂ) •
    (sourceTimeTest t (graphRetardedTest t a χin χout hin hout hK
      (sourceCutTest χs hs u))).val x =
    (χs x : ℂ) • (sourceCutTest χs hs u).val x
  by_cases hx : χs x = 0
  · simp [hx]
  have hxs : x ∈ tsupport χs := subset_tsupport χs hx
  have ho : χout x = 1 := (houtput x hxs).eq_of_nhds
  have hd : partialDeriv (fun y ↦ (χout y : ℂ)) x t = 0 := by
    have he : (fun y ↦ (χout y : ℂ)) =ᶠ[𝓝 x] fun _ ↦ (1 : ℂ) :=
      (houtput x hxs).mono (fun y hy ↦ by simp only [hy, Complex.ofReal_one])
    rw [partialDeriv, he.fderiv_eq, fderiv_const_apply (𝕜 := ℝ) (1 : ℂ)]
    rfl
  rw [sourceTimeTest_graphRetardedTest, hinput x hxs, ho, hd]
  simp only [Complex.ofReal_one, one_smul, zero_smul, add_zero]

/-- The same exact nesting identity after inclusion in actual Euclidean L²
and composition with any realized graph. The graph low constructor supplies
`T`; no action of a time derivative on arbitrary L² data is asserted here.
Source: `app:ch_regular_base:eq:DJ-identity`. -/
theorem sourceCutGraph_sourceTimeTest_graphRetardedTest
    (t : Fin (d + 1)) (a : ℝ) (χin χout χs : E → ℝ)
    (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hs : ContDiff ℝ ∞ χs) (hK : HasCompactSupport χout)
    (hb : ∀ x, ‖χs x‖ ≤ 1)
    (hinput : ∀ x ∈ tsupport χs, χin x = 1)
    (houtput : ∀ x ∈ tsupport χs, χout =ᶠ[𝓝 x] fun _ ↦ 1)
    (T : L² →L[ℂ] L²) (u : graphTestSpace (d + 1) r) :
    (T ∘L sourceCutMultiplier χs hs.continuous hb)
        (graphTestToLp (sourceTimeTest t (graphRetardedTest t a χin χout hin hout hK
          (sourceCutTest χs hs u)))) =
      (T ∘L sourceCutMultiplier χs hs.continuous hb)
        (sourceCutMultiplier χs hs.continuous hb (graphTestToLp u)) := by
  simp only [ContinuousLinearMap.comp_apply]
  rw [sourceCutMultiplier_graphTestToLp χs hs hb,
    sourceCutMultiplier_graphTestToLp χs hs hb,
    sourceCutMultiplier_graphTestToLp χs hs hb]
  rw [sourceCutTest_sourceTimeTest_graphRetardedTest t a χin χout χs hin hout hs hK
    hinput houtput]

end JanetCartan.FourierIntegral
