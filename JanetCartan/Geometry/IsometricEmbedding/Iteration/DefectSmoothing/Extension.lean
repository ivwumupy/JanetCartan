module

public import JanetCartan.Analysis.Extension.Ball
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Periodization
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Defs
public import JanetCartan.Geometry.IsometricEmbedding.Calculus

/-!
# The fixed tensor extension for the actual defect

`main:lem:smoothing`: the Seeley formula is fixed by the local domain, before
any order, target or history. The codomain is the actual real Frobenius tensor
space. Periodization uses the existing centered representative, and all jets
agree on the closed core for inputs smooth on the larger chart.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius Topology
open Set Filter Metric

namespace JanetCartan.DefectSmoothing

variable {n : ℕ}

/-- The one fixed collar in `main:lem:smoothing`, strictly inside the chart. -/
def extensionParameters (D : LocalDomain) : BallExtension.Parameters (Euclidean n) where
  center := 0
  radius := D.coreRadius
  radius_pos := D.coreRadius_pos
  width := min (D.coreRadius / 4) ((D.chartRadius - D.coreRadius) / 2)
  width_pos := lt_min (by linarith [D.coreRadius_pos])
    (by linarith [D.coreRadius_lt_chartRadius])
  width_lt := (min_le_left _ _).trans_lt (by linarith [D.coreRadius_pos])

/-- The actual real tensor extension in `main:lem:smoothing`. Every exterior
sum is finite by the compact radial cutoff; regularity is asserted only for
smooth inputs below. -/
def tensorExtension (D : LocalDomain) (f : MetricField n) : MetricField n :=
  (extensionParameters D).seeleyExtension f

/-- Exact closed-core restriction in `main:lem:smoothing`. -/
theorem tensorExtension_eqOn (D : LocalDomain) (f : MetricField n) :
    EqOn (tensorExtension D f) f (D.core n) :=
  (extensionParameters D).seeleyExtension_eq_on_closedBall f

/-- The same extension depends only on the actual core data (`main:lem:smoothing`). -/
theorem tensorExtension_congr (D : LocalDomain) {f g : MetricField n}
    (h : EqOn f g (D.core n)) : tensorExtension D f = tensorExtension D g :=
  (extensionParameters D).seeleyExtension_congr h

/-- The fixed compact support lies strictly inside the chart (`main:lem:smoothing`). -/
theorem tsupport_tensorExtension_subset (D : LocalDomain) (f : MetricField n) :
    tsupport (tensorExtension D f) ⊆ D.chart n := by
  apply ((extensionParameters D).tsupport_seeleyExtension_subset f).trans
  apply closedBall_subset_ball
  change D.coreRadius + min (D.coreRadius / 4)
    ((D.chartRadius - D.coreRadius) / 2) / 2 < D.chartRadius
  linarith [min_le_right (D.coreRadius / 4) ((D.chartRadius - D.coreRadius) / 2),
    D.coreRadius_lt_chartRadius]

/-- Smoothness uses the actual smooth-input extension theorem (`main:lem:smoothing`). -/
theorem contDiff_tensorExtension (D : LocalDomain) {f : MetricField n}
    (hf : ContDiffOn ℝ ∞ f (D.core n)) : ContDiff ℝ ∞ (tensorExtension D f) :=
  (extensionParameters D).contDiff_seeleyExtension hf

private def transposeLinear : MetricTensor n →ₗ[ℝ] MetricTensor n where
  toFun := Matrix.transpose
  map_add' := Matrix.transpose_add
  map_smul' _ _ := rfl

/-- Symmetry is preserved even when it is only known on the core
(`main:lem:smoothing`); the tensor entries remain real by construction. -/
theorem tensorExtension_isSymm (D : LocalDomain) {f : MetricField n}
    (hf : ∀ x ∈ D.core n, (f x).IsSymm) (x : Euclidean n) :
    (tensorExtension D f x).IsSymm := by
  have h := (extensionParameters D).seeleyExtension_map transposeLinear f
  have hc : EqOn (transposeLinear ∘ f) f (D.core n) := fun y hy ↦ hf y hy
  have he := (extensionParameters D).seeleyExtension_congr hc
  exact congrFun (h.symm.trans he) x

/-- Tensor periodization uses exactly the scalar amplitude representative
(`main:lem:smoothing`, `app:ch_osc:lem:osc-amplitude`). -/
def tensorPeriodization (f : MetricField n) : Torus n → MetricTensor n :=
  f ∘ AmplitudeBound.centeredTorusRepresentative

/-- Compact tensor periodization agrees locally throughout the closed cell,
so no boundary jet is lost (`main:lem:smoothing`). -/
theorem tensorPeriodization_eventuallyEq {r : ℝ} (hr : r < 1 / 2)
    {f : MetricField n} (hs : tsupport f ⊆ ball 0 r)
    {x : Euclidean n} (hx : x ∈ fundamentalCell n) :
    periodicLift (tensorPeriodization f) =ᶠ[𝓝 x] f := by
  have hentry (i j : Fin n) :
      ∀ᶠ y in 𝓝 x, periodicLift (tensorPeriodization f) y i j = f y i j := by
    let a : Euclidean n → ℂ := fun y ↦ (f y i j : ℂ)
    have ha : AmplitudeBound.SupportedInCenteredBox r a := by
      intro y hy k
      have hyf : f y ≠ 0 := by
        intro h
        apply hy
        simp [a, h]
      have hyr : ‖y‖ < r := by
        simpa using hs (subset_tsupport f (Function.mem_support.mpr hyf))
      have hk : |y k| ≤ ‖y‖ := PiLp.norm_apply_le y k
      exact hk.trans hyr.le
    exact (AmplitudeBound.periodicLift_amplitudePeriodization_eventuallyEq hr ha hx).mono
      (fun y hy ↦ Complex.ofReal_injective hy)
  filter_upwards [eventually_all.mpr (fun i ↦ eventually_all.mpr (hentry i))] with y hy
  exact funext (fun i ↦ funext (hy i))

/-- Smooth tensor periodization, with the existing unit-torus convention
(`main:lem:smoothing`). -/
theorem isSmoothPeriodic_tensorPeriodization {r : ℝ} (hr : r < 1 / 2)
    {f : MetricField n} (hs : tsupport f ⊆ ball 0 r) (hf : ContDiff ℝ ∞ f) :
    IsSmoothPeriodic (tensorPeriodization f) := by
  have hd : ContDiff ℝ ∞ (periodicLift (tensorPeriodization f)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    obtain ⟨y, hy, k, rfl⟩ := exists_mem_fundamentalCell_add_integerTranslation x
    have hlocal := hf.contDiffAt.congr_of_eventuallyEq
      (tensorPeriodization_eventuallyEq hr hs hy)
    have hlocal' : ContDiffAt ℝ ∞ (periodicLift (tensorPeriodization f))
        ((y + integerTranslation k) - integerTranslation k) := by
      simpa only [add_sub_cancel_right] using hlocal
    have hcomp := hlocal'.comp (y + integerTranslation k)
      (contDiffAt_id.sub (contDiffAt_const (c := integerTranslation k)))
    convert hcomp using 1
    funext z
    exact (periodicLift_periodic (tensorPeriodization f) k).sub_eq z |>.symm
  have hq : IsOpenQuotientMap (@torusQuotient n) :=
    (IsOpenQuotientMap.piMap (fun _ : Fin n ↦
      QuotientAddGroup.isOpenQuotientMap_mk)).comp
        (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  exact ⟨hq.isQuotientMap.continuous_iff.mpr hd.continuous, hd⟩

/-- One extension to the unit torus for all orders, targets and histories
(`main:lem:smoothing`). -/
def extendToTorus (D : LocalDomain) (f : MetricField n) : Torus n → MetricTensor n :=
  tensorPeriodization (tensorExtension D f)

/-- Additivity of the fixed real extension (`main:lem:smoothing`). The Seeley
sums are pointwise finite. Smoothness of its output still requires the smooth
core-input hypothesis of `isSmoothPeriodic_extendToTorus`. -/
theorem extendToTorus_add (D : LocalDomain) (f g : MetricField n) :
    extendToTorus D (f + g) = extendToTorus D f + extendToTorus D g := by
  funext z
  exact congrFun ((extensionParameters D).seeleyExtension.map_add f g) _

/-- Real homogeneity of the same fixed extension (`main:lem:smoothing`);
no summability or smoothness claim is made for arbitrary input functions. -/
theorem extendToTorus_smul (D : LocalDomain) (a : ℝ) (f : MetricField n) :
    extendToTorus D (a • f) = a • extendToTorus D f := by
  funext z
  exact congrFun ((extensionParameters D).seeleyExtension.map_smul a f) _

/-- Smoothness of the concrete torus extension (`main:lem:smoothing`). -/
theorem isSmoothPeriodic_extendToTorus (D : LocalDomain) {f : MetricField n}
    (hf : ContDiffOn ℝ ∞ f (D.core n)) : IsSmoothPeriodic (extendToTorus D f) :=
  isSmoothPeriodic_tensorPeriodization D.chartRadius_lt_half
    (tsupport_tensorExtension_subset D f) (contDiff_tensorExtension D hf)

/-- The core is inside the fundamental cell (`main:lem:smoothing`). -/
theorem core_subset_fundamentalCell (D : LocalDomain) : D.core n ⊆ fundamentalCell n := by
  intro x hx i
  have hnorm : ‖x‖ ≤ D.coreRadius := by simpa [LocalDomain.core] using hx
  have hi : |x i| ≤ ‖x‖ := PiLp.norm_apply_le x i
  exact abs_le.mp (hi.trans (hnorm.trans (by linarith [D.coreRadius_lt_chartRadius,
    D.chartRadius_lt_half])))

/-- Exact core agreement of the same torus extension (`main:lem:smoothing`). -/
theorem periodicLift_extendToTorus_eqOn (D : LocalDomain) (f : MetricField n) :
    EqOn (periodicLift (extendToTorus D f)) f (D.core n) := by
  intro x hx
  exact (tensorPeriodization_eventuallyEq D.chartRadius_lt_half
    (tsupport_tensorExtension_subset D f) (core_subset_fundamentalCell D hx)).self_of_nhds
      |>.trans (tensorExtension_eqOn D f hx)

/-- All ambient jets agree even on the core sphere, using smoothness on the
larger open chart and uniqueness of one-sided jets (`main:lem:smoothing`). -/
theorem iteratedFDeriv_extendToTorus_eqOn (D : LocalDomain) {f : MetricField n}
    (hf : ContDiffOn ℝ ∞ f (D.chart n)) (r : ℕ) :
    EqOn (iteratedFDeriv ℝ r (periodicLift (extendToTorus D f)))
      (iteratedFDeriv ℝ r f) (D.core n) := by
  have hsub : D.core n ⊆ D.chart n := closedBall_subset_ball D.coreRadius_lt_chartRadius
  have he := isSmoothPeriodic_extendToTorus D (hf.mono hsub)
  intro x hx
  have hu : UniqueDiffOn ℝ (D.core n) := (extensionParameters D).uniqueDiffOn_closedBall
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv hu
    (he.2.contDiffAt.of_le (by simp)) hx,
    ← iteratedFDerivWithin_eq_iteratedFDeriv hu
      ((hf.contDiffAt (isOpen_ball.mem_nhds (hsub hx))).of_le (by simp)) hx]
  exact (periodicLift_extendToTorus_eqOn D f).iteratedFDerivWithin r hx

/-- The extension preserves real symmetry (`main:lem:smoothing`). -/
theorem extendToTorus_isSymm (D : LocalDomain) {f : MetricField n}
    (hf : ∀ x ∈ D.core n, (f x).IsSymm) (z : Torus n) :
    (extendToTorus D f z).IsSymm := tensorExtension_isSymm D hf _

end JanetCartan.DefectSmoothing
