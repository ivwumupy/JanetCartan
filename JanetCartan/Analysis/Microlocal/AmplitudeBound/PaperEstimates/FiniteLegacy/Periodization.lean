module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.FiniteLegacy.PeriodicCalculus

/-!
# Finite regularity through physical periodization

The fixed-box periodization for `app:ch_osc:lem:osc-amplitude` preserves the
specified finite derivative order and the original coordinate derivative bounds.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Topology
namespace JanetCartan.AmplitudeBound.FiniteLegacy
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Physical periodization needs only the given finite regularity
(`app:ch_osc:lem:osc-amplitude`). -/
theorem periodization_contDiff {r : ℝ} (hr : r < 1 / 2)
    {f : E → ℂ} (hs : SupportedInCenteredBox r f) {m : ℕ}
    (hf : ContDiff ℝ m f) :
    Continuous (amplitudePeriodization f) ∧
      ContDiff ℝ m (periodicLift (amplitudePeriodization f)) := by
  have hd : ContDiff ℝ m (periodicLift (amplitudePeriodization f)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    obtain ⟨y,hy,k,rfl⟩ := exists_mem_fundamentalCell_add_integerTranslation x
    have hlocal := hf.contDiffAt.congr_of_eventuallyEq
      (periodicLift_amplitudePeriodization_eventuallyEq hr hs hy)
    have hlocal' : ContDiffAt ℝ m (periodicLift (amplitudePeriodization f))
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
  exact ⟨hq.isQuotientMap.continuous_iff.mpr hd.continuous,hd⟩

/-- Coordinate derivatives of exactly the specified order obey the dilation
rule (`app:ch_osc:lem:osc-amplitude`). -/
theorem coordinateDerivList_comp_smul_of_finite {f : E → ℂ}
    (is : List (Fin n)) (hf : ContDiff ℝ is.length f) (ℓ : ℝ) :
    euclideanCoordinateDerivList is (fun z ↦ f (ℓ • z)) =
      fun z ↦ ℓ ^ is.length • euclideanCoordinateDerivList is f (ℓ • z) := by
  induction is with
  | nil => simp [euclideanCoordinateDerivList]
  | cons i is ih =>
    funext z
    simp only [euclideanCoordinateDerivList,ih (hf.of_le (by simp))]
    have hg : ContDiff ℝ 1 (euclideanCoordinateDerivList is f) :=
      contDiff_euclideanCoordinateDerivList is
        (by simpa [List.length_cons,add_comm] using hf)
    have hd := hg.differentiable (by norm_num)
    have hc := (hd (ℓ • z)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).const_smul ℓ)
    have hcc : HasFDerivAt
        (fun w ↦ ℓ ^ is.length • euclideanCoordinateDerivList is f (ℓ • w))
        ((ℓ ^ is.length) • (fderiv ℝ (euclideanCoordinateDerivList is f) (ℓ • z)).comp
          (ℓ • ContinuousLinearMap.id ℝ E)) z := by
      convert hc.const_smul (ℓ ^ is.length) using 1
      funext w
      simp
    rw [hcc.fderiv]
    simp [pow_succ,mul_smul]

/-- An ordered derivative bound survives periodization with finite regularity
(`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_coordinateDerivList_periodization_of_finite {r : ℝ} (hr : r < 1 / 2)
    {f : E → ℂ} (hs : SupportedInCenteredBox r f) (is : List (Fin n))
    (hf : ContDiff ℝ is.length f) {A : ℝ}
    (hA : ∀ x, ‖euclideanCoordinateDerivList is f x‖ ≤ A) (z : Torus n) :
    ‖periodicCoordinateDerivList is (amplitudePeriodization f) z‖ ≤ A := by
  have hl := periodicLift_coordinateDerivList_eq_of_finite is
    (periodization_contDiff hr hs hf).2
  have he := (congrFun hl (centeredTorusRepresentative z)).trans
    ((euclideanCoordinateDerivList_eventuallyEq
      (periodicLift_amplitudePeriodization_eventuallyEq hr hs
        (centeredTorusRepresentative_mem z)) is).self_of_nhds)
  have he' : periodicCoordinateDerivList is (amplitudePeriodization f) z =
      euclideanCoordinateDerivList is f (centeredTorusRepresentative z) := by
    simpa only [periodicLift,Function.comp_apply,torusQuotient_centeredTorusRepresentative] using he
  rw [he']
  exact hA _

/-- The original fixed-box periodization retains its finite regularity
(`app:ch_osc:lem:osc-amplitude`). -/
theorem box_periodization_contDiff {f : E → ℂ} {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2) (hs : SupportedInCenteredBox R f)
    {m : ℕ} (hf : ContDiff ℝ m f) :
    Continuous (boxAmplitudePeriodization ℓ f) ∧
      ContDiff ℝ m (periodicLift (boxAmplitudePeriodization ℓ f)) :=
  periodization_contDiff hR (supportedInCenteredBox_comp_smul hℓ hs)
    (hf.comp (contDiff_const_smul ℓ))

/-- The exact original box-scaling loss requires only the indicated derivative
order (`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_coordinateDerivList_box_of_finite {f : E → ℂ} {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2) (hs : SupportedInCenteredBox R f)
    (is : List (Fin n)) (hf : ContDiff ℝ is.length f) {A : ℝ}
    (hA : ∀ z, ‖euclideanCoordinateDerivList is f z‖ ≤ A) (z : Torus n) :
    ‖periodicCoordinateDerivList is (boxAmplitudePeriodization ℓ f) z‖ ≤ |ℓ| ^ is.length * A := by
  apply norm_coordinateDerivList_periodization_of_finite hR
    (supportedInCenteredBox_comp_smul hℓ hs) is (hf.comp (contDiff_const_smul ℓ))
  intro x
  rw [coordinateDerivList_comp_smul_of_finite is hf,norm_smul,Real.norm_eq_abs,abs_pow]
  exact mul_le_mul_of_nonneg_left (hA _) (by positivity)

/-- The finite-order pure derivatives have the same box factor as the smooth
amplitude theorem (`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_pureDeriv_box_of_finite {d : ℕ}
    {f : EuclideanSpace ℝ (Fin (2*d)) → ℂ} {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2) (hs : SupportedInCenteredBox R f)
    (hf : ContDiff ℝ (2*(d+1) : ℕ) f) {A : ℝ} (hA : 0 ≤ A)
    (hderiv : ∀ i z,
      ‖euclideanCoordinateDerivList (List.replicate (2*(d+1)) i) f z‖ ≤ A)
    (i : Fin (2*d)) (z : Torus (2*d)) :
    ‖periodicCoordinateDerivList (List.replicate (2*(d+1)) i)
      (boxAmplitudePeriodization ℓ f) z‖ ≤ boxDerivativeFactor d ℓ * A := by
  apply (norm_coordinateDerivList_box_of_finite hℓ hR hs _
    (by simpa only [List.length_replicate] using hf) (hderiv i) z).trans
  apply mul_le_mul_of_nonneg_right _ hA
  simp only [List.length_replicate,boxDerivativeFactor]
  linarith

end JanetCartan.AmplitudeBound.FiniteLegacy
