module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SourceExtension
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# The fixed compact smooth source domain

The real source domain for `app:ch_response:thm:response-compatible-choice`.
Membership records ordinary smooth functions with compact support in the fixed
source set. Lebesgue `L²` membership is proved, rather than encoded through the
zero convention of `toLp`. The consumer is the actual `ambientExtension`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PrimarySourceAdmission

/-- The compact smooth supported real metric sources on which the fixed response
is extended (`app:ch_response:thm:response-compatible-choice`). -/
def compactSmoothSources {n : ℕ} (S : Set (Euclidean n)) :
    Submodule ℝ (MetricField n) where
  carrier := {h | ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ tsupport h ⊆ S}
  zero_mem' := ⟨contDiff_const, by simp [HasCompactSupport], by simp⟩
  add_mem' := fun hf hg ↦ ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
    (tsupport_add _ _).trans (union_subset hf.2.2 hg.2.2)⟩
  smul_mem' := by
    intro a f hf
    have hs : tsupport (a • f) ⊆ tsupport f :=
      tsupport_smul_subset_right (fun _ : Euclidean n ↦ a) f
    exact ⟨hf.1.const_smul a,
      (hf.2.1 : IsCompact (tsupport f)).of_isClosed_subset (isClosed_tsupport _) hs,
      hs.trans hf.2.2⟩

/-- Membership exposes the actual smoothness and support assertions
(`app:ch_response:thm:response-compatible-choice`). -/
@[simp] theorem mem_compactSmoothSources_iff {n : ℕ} {S : Set (Euclidean n)}
    {h : MetricField n} : h ∈ compactSmoothSources S ↔
      ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ tsupport h ⊆ S := Iff.rfl

/-- Actual source-domain members lie in the original Lebesgue `L²` space
(`app:ch_response:thm:response-compatible-choice`). -/
theorem memLp_of_mem_compactSmoothSources {n : ℕ} {S : Set (Euclidean n)}
    {h : MetricField n} (hh : h ∈ compactSmoothSources S) : MemLp h 2 volume := by
  change ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ tsupport h ⊆ S at hh
  exact hh.1.continuous.memLp_of_hasCompactSupport hh.2.1

/-- A chart-smooth tensor becomes globally smooth after the fixed source cutoff.
The closed support buffer supplies regularity at the chart boundary
(`app:ch_response:cor:current-atoms`). -/
theorem contDiff_cutoff_of_support_subset {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {χ : Euclidean n → ℝ} {v : Euclidean n → V} {O : Set (Euclidean n)}
    (hχ : ContDiff ℝ ∞ χ) (ho : IsOpen O) (hv : ContDiffOn ℝ ∞ v O)
    (hs : tsupport χ ⊆ O) : ContDiff ℝ ∞ (fun x ↦ χ x • v x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.smul ((hv x (hs hx)).contDiffAt (ho.mem_nhds (hs hx)))
  · apply (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [hy]

/-- Multiplication after taking the full strain retains exactly the original
source support (`app:ch_response:cor:current-atoms`). -/
theorem cutoff_mem_compactSmoothSources {n : ℕ} {χ : Euclidean n → ℝ}
    {v : MetricField n} {O : Set (Euclidean n)}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (ho : IsOpen O) (hv : ContDiffOn ℝ ∞ v O) (hs : tsupport χ ⊆ O) :
    (fun x ↦ χ x • v x) ∈ compactSmoothSources (tsupport χ) := by
  change ContDiff ℝ ∞ (fun x ↦ χ x • v x) ∧
    HasCompactSupport (fun x ↦ χ x • v x) ∧ _
  exact ⟨contDiff_cutoff_of_support_subset hχ ho hv hs,
    hc.smul_right (f' := v), tsupport_smul_subset_left χ v⟩

/-- Replacing a chart representative on a neighborhood of the entire source
support preserves the literal cutoff strain, including all correction terms
(`app:ch_response:cor:current-atoms`). -/
theorem cutoff_complexStrain_eq_of_eventuallyEq {n N : ℕ}
    (F : Euclidean n → Euclidean N) (χ : Euclidean n → ℝ)
    {W Z : Euclidean n → EuclideanSpace ℂ (Fin N)}
    (he : ∀ x ∈ tsupport χ, W =ᶠ[𝓝 x] Z) :
    (fun x ↦ χ x • WKB.complexLinearizedMetric F W x) =
      (fun x ↦ χ x • WKB.complexLinearizedMetric F Z x) := by
  funext x
  by_cases hx : x ∈ tsupport χ
  · rw [(ResponseSourceExtension.complexLinearizedMetric_eventuallyEq F
      (he x hx)).self_of_nhds]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- A harmless globally smooth compact extension exists on the full original
source support. Its literal cut-off strain is unchanged; the source cutoff is
never shrunk (`app:ch_response:cor:current-atoms`). -/
theorem exists_extension_preserving_cutoff_strain {n N : ℕ}
    (F : Euclidean n → Euclidean N) (χ : Euclidean n → ℝ)
    (hc : HasCompactSupport χ) {O : Set (Euclidean n)} (ho : IsOpen O)
    (hs : tsupport χ ⊆ O) (W : Euclidean n → EuclideanSpace ℂ (Fin N))
    (hW : ContDiffOn ℝ ∞ W O) :
    ∃ Z : Euclidean n → EuclideanSpace ℂ (Fin N),
      ContDiff ℝ ∞ Z ∧ HasCompactSupport Z ∧ tsupport Z ⊆ O ∧
      (∀ x ∈ tsupport χ, Z =ᶠ[𝓝 x] W) ∧
      (fun x ↦ χ x • WKB.complexLinearizedMetric F Z x) =
        (fun x ↦ χ x • WKB.complexLinearizedMetric F W x) := by
  obtain ⟨ψ⟩ := ResponseSourceExtension.nonempty_outputCutoff hc ho hs
  let Z := ψ.zeroExtend (fun x : O ↦ W x)
  have he : ∀ x ∈ tsupport χ, Z =ᶠ[𝓝 x] W :=
    fun _ hx ↦ ψ.zeroExtend_eventuallyEq W hx
  exact ⟨Z, ψ.contDiff_zeroExtend_restrict ho hW,
    ψ.hasCompactSupport_zeroExtend _,
    (ψ.tsupport_zeroExtend_subset _).trans ψ.support_chart,
    he, cutoff_complexStrain_eq_of_eventuallyEq F χ he⟩

end JanetCartan.PrimarySourceAdmission
