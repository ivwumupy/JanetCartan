module

public import JanetCartan.Analysis.Operator.RetardedSobolev.Spaces.Completion
public import Mathlib.Analysis.Normed.Group.Quotient

/-!
# Supported and restriction spaces

The supported/restriction pairs of `app:ch_osc:prop:osc-retarded-tube`.
Supported spaces close the compactly supported tests inside the open set in the
ambient derivative norm. Restriction spaces are quotients by the kernel of
restriction to local L². These definitions make no distribution identification.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.RetardedSobolev.Spaces

/-- A nonempty open Cartesian rectangle with a specified positive buffer
(`app:ch_osc:setup:osc-retarded`). -/
structure BufferedRectangle (d : ℕ) where
  timeLower : ℝ
  timeUpper : ℝ
  lower : Fin d → ℝ
  upper : Fin d → ℝ
  time_lt : timeLower < timeUpper
  transverse_lt : ∀ i, lower i < upper i
  buffer : ℝ
  buffer_pos : 0 < buffer

/-- The inner open rectangle (`app:ch_osc:setup:osc-retarded`). -/
def BufferedRectangle.carrier {d : ℕ} (R : BufferedRectangle d) : Set (ℝ × (Fin d → ℝ)) :=
  Ioo R.timeLower R.timeUpper ×ˢ Set.pi univ (fun i ↦ Ioo (R.lower i) (R.upper i))

/-- The larger rectangle supplies the explicit buffer
(`app:ch_osc:setup:osc-retarded`). -/
def BufferedRectangle.outer {d : ℕ} (R : BufferedRectangle d) : Set (ℝ × (Fin d → ℝ)) :=
  Ioo (R.timeLower - R.buffer) (R.timeUpper + R.buffer) ×ˢ
    Set.pi univ (fun i ↦ Ioo (R.lower i - R.buffer) (R.upper i + R.buffer))

/-- The rectangle used for the supported/restriction pair is open
(`app:ch_osc:setup:osc-retarded`). -/
theorem BufferedRectangle.isOpen_carrier {d : ℕ} (R : BufferedRectangle d) :
    IsOpen R.carrier :=
  isOpen_Ioo.prod (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo)

/-- The closure of the inner rectangle lies inside its explicit larger buffer
(`app:ch_osc:setup:osc-retarded`). -/
theorem BufferedRectangle.closure_carrier_subset_outer {d : ℕ} (R : BufferedRectangle d) :
    closure R.carrier ⊆ R.outer := by
  simp only [carrier, outer, closure_prod_eq, closure_pi_set,
    closure_Ioo R.time_lt.ne]
  intro x hx
  refine ⟨⟨by linarith [hx.1.1, R.buffer_pos], by linarith [hx.1.2, R.buffer_pos]⟩, ?_⟩
  intro i hi
  have h := hx.2 i hi
  dsimp only at h ⊢
  rw [closure_Ioo (R.transverse_lt i).ne] at h
  exact ⟨by linarith [h.1, R.buffer_pos], by linarith [h.2, R.buffer_pos]⟩

/-- Test fields compactly supported inside the prescribed open set
(`app:ch_osc:prop:osc-retarded-tube`). -/
def supportedTests {d : ℕ} (U : Set (ℝ × (Fin d → ℝ))) : Submodule ℂ (Test d) where
  carrier := {f | tsupport (f : (ℝ × (Fin d → ℝ)) → ℂ) ⊆ U}
  zero_mem' := by simp
  add_mem' hf hg := (tsupport_add _ _).trans (union_subset hf hg)
  smul_mem' c f hf := by
    apply Subset.trans _ hf
    exact closure_mono (Function.support_smul_subset_right _ _)

/-- The supported positive space is the closure of the compactly supported tests
in the ambient Sobolev norm (`app:ch_osc:prop:osc-retarded-tube`). -/
def supportedSubmodule {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) :
    Submodule ℂ (Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ))) :=
  ((ofTest m volume).comp (supportedTests U).subtype).range.topologicalClosure

/-- Supported nonnegative integer Sobolev space
(`app:ch_osc:prop:osc-retarded-tube`). -/
abbrev Supported {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) :=
  supportedSubmodule m U

instance {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) :
    NormedAddCommGroup (Supported m U) := Submodule.normedAddCommGroup _

instance {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) :
    NormedSpace ℂ (Supported m U) := Submodule.normedSpace _

instance {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) : CompleteSpace (Supported m U) :=
  inferInstanceAs (CompleteSpace
    ((ofTest m volume).comp (supportedTests U).subtype).range.topologicalClosure)

/-- The inclusion of supported tests into their closure
(`app:ch_osc:prop:osc-retarded-tube`). -/
def supportedOfTest {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) :
    supportedTests U →ₗ[ℂ] Supported m U :=
  ((ofTest m volume).comp (supportedTests U).subtype).codRestrict _ fun f ↦
    ((ofTest m volume).comp (supportedTests U).subtype).range.le_topologicalClosure
      (LinearMap.mem_range_self _ f)

/-- Supported tests are dense in the supported completion
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem denseRange_supportedOfTest {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) :
    DenseRange (supportedOfTest m U) := by
  exact ((denseRange_inclusion_iff
    (s := Set.range ((ofTest m volume).comp (supportedTests U).subtype)) subset_closure).2
      subset_rfl).comp Set.rangeFactorization_surjective.denseRange
        (continuous_inclusion subset_closure)

/-- Classical restriction into local L², with the coordinate swap used by the
energy formulas (`app:ch_osc:prop:osc-retarded-tube`). -/
def testRestriction {d : ℕ} (U : Set (ℝ × (Fin d → ℝ))) :
    Test d →ₗ[ℂ] Lp ℂ 2 (volume.restrict (Prod.swap ⁻¹' U)) :=
  (LinearMap.proj (zeroIndex d 0)).comp (jetMap 0 (volume.restrict (Prod.swap ⁻¹' U)))

/-- Local L² restriction is bounded by every ambient derivative norm
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem norm_testRestriction_le {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) (f : Test d) :
    ‖testRestriction U f‖ ≤ ‖ofTest m volume f‖ := by
  calc
    ‖testRestriction U f‖ ≤ ‖jetMap m volume f (zeroIndex d m)‖ := by
      change ‖(jet_memLp (volume.restrict (Prod.swap ⁻¹' U)) (zeroIndex d 0) f).toLp _‖ ≤
        ‖(jet_memLp volume (zeroIndex d m) f).toLp _‖
      simp only [Lp.norm_toLp, jet_zeroIndex]
      apply ENNReal.toReal_mono
      · simpa only [jet_zeroIndex] using (jet_memLp volume (zeroIndex d m) f).eLpNorm_ne_top
      · exact eLpNorm_restrict_le _ _ _ _
    _ ≤ ‖ofTest m volume f‖ := norm_le_pi_norm _ _

/-- Restriction of the completion into local L²
(`app:ch_osc:prop:osc-retarded-tube`). -/
def localRestriction {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) :
    Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
      Lp ℂ 2 (volume.restrict (Prod.swap ⁻¹' U)) :=
  (testRestriction U).extendOfNorm (ofTest m volume)

/-- The completed restriction agrees with the literal classical restriction
(`app:ch_osc:prop:osc-retarded-tube`). -/
@[simp] theorem localRestriction_ofTest {d : ℕ} (m : ℕ)
    (U : Set (ℝ × (Fin d → ℝ))) (f : Test d) :
    localRestriction m U (ofTest m volume f) = testRestriction U f :=
  LinearMap.extendOfNorm_eq (denseRange_ofTest m volume)
    ⟨1, fun f ↦ by simpa using norm_testRestriction_le m U f⟩ f

/-- The closed space of ambient elements with zero restriction
(`app:ch_osc:prop:osc-retarded-tube`). -/
def restrictionKernel {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) :
    Submodule ℂ (Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ))) :=
  (localRestriction m U).toLinearMap.ker

instance {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) :
    IsClosed (restrictionKernel m U : Set (Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)))) :=
  (localRestriction m U).isClosed_ker

/-- The positive restriction space has the quotient norm from the ambient
Sobolev completion (`app:ch_osc:prop:osc-retarded-tube`). -/
abbrev Restriction {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) :=
  Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)) ⧸ restrictionKernel m U

/-- Canonical restriction to the quotient (`app:ch_osc:prop:osc-retarded-tube`). -/
def restrict {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) :
    Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ] Restriction m U :=
  (restrictionKernel m U).mkQL

/-- The equivalence relation is exactly equality of local L² restrictions
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem restrict_eq_iff {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ)))
    (u v : Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ))) :
    restrict m U u = restrict m U v ↔ localRestriction m U u = localRestriction m U v := by
  change Submodule.Quotient.mk u = Submodule.Quotient.mk v ↔ _
  rw [Submodule.Quotient.eq]
  change localRestriction m U (u - v) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- Two smooth fields represent the same restriction precisely when they agree
almost everywhere in the open set (`app:ch_osc:prop:osc-retarded-tube`). -/
theorem restrict_ofTest_eq_iff {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ)))
    (f g : Test d) :
    restrict m U (ofTest m volume f) = restrict m U (ofTest m volume g) ↔
      (fun p ↦ f.val (p.2, p.1)) =ᵐ[volume.restrict (Prod.swap ⁻¹' U)]
        (fun p ↦ g.val (p.2, p.1)) := by
  rw [restrict_eq_iff, localRestriction_ofTest, localRestriction_ofTest]
  change (jet_memLp _ (zeroIndex d 0) f).toLp _ =
    (jet_memLp _ (zeroIndex d 0) g).toLp _ ↔ _
  rw [MemLp.toLp_eq_toLp_iff]
  simp only [jet_zeroIndex]

/-- Restricted smooth ambient tests are dense in the quotient
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem denseRange_restrict_ofTest {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) :
    DenseRange (fun f : Test d ↦ restrict m U (ofTest m volume f)) :=
  ((restrictionKernel m U).mkQ_surjective.denseRange).comp
    (denseRange_ofTest m volume) (restrict m U).continuous

end JanetCartan.RetardedSobolev.Spaces
