module

public import JanetCartan.Analysis.Fourier.Periodic.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Periodization inside a larger physical box

The fixed larger torus in `app:ch_osc:lem:osc-amplitude`. Choosing centered
representatives gives a measurable construction. A support gap gives equality
on a neighborhood of the closed fundamental cell, including its boundary.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace JanetCartan.AmplitudeBound

variable {n : ℕ}

/-- Centered measurable representative for the auxiliary torus in
`app:ch_osc:lem:osc-amplitude`. -/
def centeredTorusRepresentative (z : Torus n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) (z i) : ℝ))

/-- The representative is in the closed physical cell (`app:ch_osc:lem:osc-amplitude`). -/
theorem centeredTorusRepresentative_mem (z : Torus n) :
    centeredTorusRepresentative z ∈ fundamentalCell n := by
  intro i
  have h := (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) (z i)).property
  change -(1 / 2 : ℝ) ≤ (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) (z i) : ℝ) ∧
    (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) (z i) : ℝ) ≤ 1 / 2
  constructor
  · exact h.1
  · linarith [h.2]

/-- Representatives project to their torus point (`app:ch_osc:lem:osc-amplitude`). -/
@[simp] theorem torusQuotient_centeredTorusRepresentative (z : Torus n) :
    torusQuotient (centeredTorusRepresentative z) = z := by
  funext i
  exact AddCircle.coe_equivIco

/-- Measurability of centered representatives (`app:ch_osc:lem:osc-amplitude`). -/
theorem measurable_centeredTorusRepresentative :
    Measurable (centeredTorusRepresentative (n := n)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).measurable.comp
  exact Measurable.of_eval fun i ↦ measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco (1 : ℝ) (-(1 / 2 : ℝ))).measurable.comp
      (measurable_pi_apply i))

/-- Unit-torus periodization of a physical amplitude supported in the interior
of the centered cell (`app:ch_osc:lem:osc-amplitude`). -/
def amplitudePeriodization (f : EuclideanSpace ℝ (Fin n) → ℂ) : Torus n → ℂ :=
  f ∘ centeredTorusRepresentative

/-- The physical support condition in `app:ch_osc:lem:osc-amplitude`, expressed
coordinatewise. No regularity or bounds are included in this condition. -/
def SupportedInCenteredBox (r : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  ∀ x, f x ≠ 0 → ∀ i, |x i| ≤ r

private theorem eq_of_torusQuotient_eq_of_box {r : ℝ}
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ i, |x i| < 1 - r)
    (hy : ∀ i, |y i| ≤ r) (hxy : torusQuotient x = torusQuotient y) : x = y := by
  ext i
  have he : ((x i - y i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub, show (x i : AddCircle (1 : ℝ)) = (y i : AddCircle (1 : ℝ))
      from congrFun hxy i, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp he
  have hx' := abs_lt.mp (hx i)
  have hy' := abs_le.mp (hy i)
  have hk' : (k : ℝ) = x i - y i := by simpa using hk
  have hlo : (-1 : ℤ) < k := by exact_mod_cast (show (-1 : ℝ) < k by linarith)
  have hhi : k < (1 : ℤ) := by exact_mod_cast (show (k : ℝ) < 1 by linarith)
  have : k = 0 := by omega
  simp only [this, Int.cast_zero] at hk'
  linarith

/-- The lift equals the physical amplitude on the larger open box with radius
`1-r`; this includes a neighborhood of the entire cell when `r < 1/2`
(`app:ch_osc:lem:osc-amplitude`). -/
theorem periodicLift_amplitudePeriodization_eq_of_lt {r : ℝ} (hr : r < 1 / 2)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hs : SupportedInCenteredBox r f)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ∀ i, |x i| < 1 - r) :
    periodicLift (amplitudePeriodization f) x = f x := by
  let y := centeredTorusRepresentative (torusQuotient x)
  have hy : ∀ i, |y i| < 1 - r := by
    intro i
    have h := centeredTorusRepresentative_mem (torusQuotient x) i
    apply (abs_le.mpr h).trans_lt
    linarith
  have hq : torusQuotient y = torusQuotient x := torusQuotient_centeredTorusRepresentative _
  change f y = f x
  by_cases hfx : f x = 0
  · by_cases hfy : f y = 0
    · exact hfy.trans hfx.symm
    · have he := eq_of_torusQuotient_eq_of_box hx (hs y hfy) hq.symm
      rw [he]
  · have he := eq_of_torusQuotient_eq_of_box hy (hs x hfx) hq
    rw [he]

/-- Local equality at every point of the closed fundamental cell, needed to
transfer all derivatives (`app:ch_osc:lem:osc-amplitude`). -/
theorem periodicLift_amplitudePeriodization_eventuallyEq {r : ℝ} (hr : r < 1 / 2)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hs : SupportedInCenteredBox r f)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ fundamentalCell n) :
    periodicLift (amplitudePeriodization f) =ᶠ[𝓝 x] f := by
  have hmem : ∀ᶠ y in 𝓝 x, ∀ i, |y i| < 1 - r := by
    apply eventually_all.mpr
    intro i
    apply (isOpen_lt ((EuclideanSpace.proj i).continuous.abs) continuous_const).mem_nhds
    exact (abs_le.mpr (hx i)).trans_lt (by linarith)
  exact hmem.mono fun y hy ↦ periodicLift_amplitudePeriodization_eq_of_lt hr hs hy

/-- Equality throughout the closed cell, including all faces
(`app:ch_osc:lem:osc-amplitude`). -/
theorem periodicLift_amplitudePeriodization_eq {r : ℝ} (hr : r < 1 / 2)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hs : SupportedInCenteredBox r f)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ fundamentalCell n) :
    periodicLift (amplitudePeriodization f) x = f x :=
  (periodicLift_amplitudePeriodization_eventuallyEq hr hs hx).self_of_nhds

/-- Periodizing a smooth supported amplitude gives a smooth periodic field
(`app:ch_osc:lem:osc-amplitude`). -/
theorem isSmoothPeriodic_amplitudePeriodization {r : ℝ} (hr : r < 1 / 2)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hs : SupportedInCenteredBox r f)
    (hf : ContDiff ℝ ∞ f) : IsSmoothPeriodic (amplitudePeriodization f) := by
  have hd : ContDiff ℝ ∞ (periodicLift (amplitudePeriodization f)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    obtain ⟨y, hy, k, rfl⟩ := exists_mem_fundamentalCell_add_integerTranslation x
    have hlocal := hf.contDiffAt.congr_of_eventuallyEq
      (periodicLift_amplitudePeriodization_eventuallyEq hr hs hy)
    have hlocal' : ContDiffAt ℝ ∞ (periodicLift (amplitudePeriodization f))
        ((y + integerTranslation k) - integerTranslation k) := by
      simpa only [add_sub_cancel_right] using hlocal
    have hcomp := hlocal'.comp (y + integerTranslation k)
      (contDiffAt_id.sub (contDiffAt_const (c := integerTranslation k)))
    convert hcomp using 1
    funext z
    exact (periodicLift_periodic (amplitudePeriodization f) k).sub_eq z |>.symm
  have hq : IsOpenQuotientMap (@torusQuotient n) :=
    (IsOpenQuotientMap.piMap (fun _ : Fin n ↦
      QuotientAddGroup.isOpenQuotientMap_mk)).comp
        (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  exact ⟨hq.isQuotientMap.continuous_iff.mpr hd.continuous, hd⟩

/-- Joint strong measurability survives periodization, so the external parameter
can remain a frequency or an integration variable (`app:ch_osc:lem:osc-amplitude`). -/
theorem stronglyMeasurable_amplitudePeriodization {X : Type*} [MeasurableSpace X]
    {b : X → EuclideanSpace ℝ (Fin n) → ℂ}
    (hb : StronglyMeasurable (Function.uncurry b)) :
    StronglyMeasurable (Function.uncurry (fun ξ ↦ amplitudePeriodization (b ξ))) :=
  hb.comp_measurable (measurable_fst.prodMk
    (measurable_centeredTorusRepresentative.comp measurable_snd))

/-- Zeroth order bounds transfer with the identical constant
(`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_amplitudePeriodization_le {f : EuclideanSpace ℝ (Fin n) → ℂ} {A : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ A) (z : Torus n) : ‖amplitudePeriodization f z‖ ≤ A :=
  hf _

end JanetCartan.AmplitudeBound
