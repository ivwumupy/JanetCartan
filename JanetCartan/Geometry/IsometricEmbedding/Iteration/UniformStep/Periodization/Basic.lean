module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Periodization
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.Measure
public import JanetCartan.Geometry.IsometricEmbedding.Basic

/-!
# Periodization of the physical correction fields

The vector version of the existing amplitude periodization, for `main:thm:step`.
The support gap gives local equality on the entire closed cell. In particular,
this construction does not identify a compact field with a global periodic lift.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace JanetCartan.UniformStep.Periodization

variable {n N : ℕ}

/-- The centered-representative construction for the real fields in
`main:eq:metric-ledger`, using the same representative as `amplitudePeriodization`. -/
def vectorPeriodization (f : Euclidean n → Euclidean N) : Torus n → Euclidean N :=
  f ∘ AmplitudeBound.centeredTorusRepresentative

/-- Coordinatewise complex amplitude periodization gives exactly the real vector
construction used in `main:thm:step`. -/
theorem vectorPeriodization_coordinate (f : Euclidean n → Euclidean N) (i : Fin N)
    (z : Torus n) :
    (vectorPeriodization f z i : ℂ) =
      AmplitudeBound.amplitudePeriodization (fun x ↦ (f x i : ℂ)) z := rfl

/-- The physical and periodic fields agree locally even on the cell faces;
this supplies all physical jets for `main:eq:metric-ledger`. -/
theorem vectorPeriodization_eventuallyEq {r : ℝ} (hr : r < 1 / 2)
    {f : Euclidean n → Euclidean N}
    (hs : tsupport f ⊆ {x | ∀ i, |x i| ≤ r})
    {x : Euclidean n} (hx : x ∈ fundamentalCell n) :
    periodicLift (vectorPeriodization f) =ᶠ[𝓝 x] f := by
  have hcoord (i : Fin N) :
      ∀ᶠ y in 𝓝 x, periodicLift (vectorPeriodization f) y i = f y i := by
    have ha : AmplitudeBound.SupportedInCenteredBox r (fun y ↦ (f y i : ℂ)) := by
      intro y hy
      apply hs (subset_tsupport f ?_)
      intro h
      apply hy
      simp [h]
    exact (AmplitudeBound.periodicLift_amplitudePeriodization_eventuallyEq hr ha hx).mono
      (fun _ hy ↦ Complex.ofReal_injective hy)
  filter_upwards [eventually_all.mpr hcoord] with y hy
  ext i
  exact hy i

/-- Smoothness of the actual real periodization for `main:thm:step`, proved from
the physical field and its support gap. -/
theorem isSmoothPeriodic_vectorPeriodization {r : ℝ} (hr : r < 1 / 2)
    {f : Euclidean n → Euclidean N}
    (hs : tsupport f ⊆ {x | ∀ i, |x i| ≤ r}) (hf : ContDiff ℝ ∞ f) :
    IsSmoothPeriodic (vectorPeriodization f) := by
  have hd : ContDiff ℝ ∞ (periodicLift (vectorPeriodization f)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    obtain ⟨y, hy, k, rfl⟩ := exists_mem_fundamentalCell_add_integerTranslation x
    have hlocal := hf.contDiffAt.congr_of_eventuallyEq
      (vectorPeriodization_eventuallyEq hr hs hy)
    have hlocal' : ContDiffAt ℝ ∞ (periodicLift (vectorPeriodization f))
        ((y + integerTranslation k) - integerTranslation k) := by
      simpa only [add_sub_cancel_right] using hlocal
    have hcomp := hlocal'.comp (y + integerTranslation k)
      (contDiffAt_id.sub (contDiffAt_const (c := integerTranslation k)))
    convert hcomp using 1
    funext z
    exact (periodicLift_periodic (vectorPeriodization f) k).sub_eq z |>.symm
  have hq : IsOpenQuotientMap (@torusQuotient n) :=
    (IsOpenQuotientMap.piMap (fun _ : Fin n ↦
      QuotientAddGroup.isOpenQuotientMap_mk)).comp
        (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  exact ⟨hq.isQuotientMap.continuous_iff.mpr hd.continuous, hd⟩

/-- Exact transfer of every ambient jet of the cut field on the cell
(`main:eq:joint-physical-profile`). -/
theorem iteratedFDeriv_vectorPeriodization_eq {r : ℝ} (hr : r < 1 / 2)
    {f : Euclidean n → Euclidean N}
    (hs : tsupport f ⊆ {x | ∀ i, |x i| ≤ r}) (j : ℕ)
    {x : Euclidean n} (hx : x ∈ fundamentalCell n) :
    iteratedFDeriv ℝ j (periodicLift (vectorPeriodization f)) x =
      iteratedFDeriv ℝ j f x :=
  ((vectorPeriodization_eventuallyEq hr hs hx).iteratedFDeriv ℝ j).self_of_nhds

/-- A support gap puts the support strictly inside the integration cell
(`main:eq:step-L2`). -/
theorem support_subset_halfOpenCell {F : Type*} [Zero F]
    {f : Euclidean n → F} {r : ℝ} (hr : r < 1 / 2)
    (hs : tsupport f ⊆ {x | ∀ i, |x i| ≤ r}) :
    Function.support f ⊆ PeriodicLocalL2.halfOpenCell n := by
  intro x hx i
  have hi := abs_le.mp (hs (subset_tsupport f hx) i)
  exact ⟨by linarith [hi.1], by linarith [hi.2]⟩

/-- Literal L² transfer from physical Lebesgue measure to normalized Haar
measure, for the same cut field in `main:eq:step-L2`. -/
theorem periodicL2Norm_vectorPeriodization {r : ℝ} (hr : r < 1 / 2)
    {f : Euclidean n → Euclidean N}
    (hs : tsupport f ⊆ {x | ∀ i, |x i| ≤ r}) :
    periodicL2Norm (vectorPeriodization f) = Real.sqrt (∫ x, ‖f x‖ ^ 2) := by
  unfold periodicL2Norm vectorPeriodization
  simp only [Function.comp_apply]
  rw [PeriodicLocalL2.integral_representative (fun x ↦ ‖f x‖ ^ 2)]
  congr 1
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hf : f x = 0 := by
    by_contra h
    exact hx (support_subset_halfOpenCell hr hs h)
  simp [hf]

end JanetCartan.UniformStep.Periodization
