module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicAmplitude.Normalized
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.SymbolBounds

/-!
# Smooth conic amplitudes with the actual low-frequency collar

Use the fixed sector mask on the initial spatial covector. It removes the
singularity at zero and the boundary of the positive section, while retaining
the same local amplitude, both times, and its physical support. Consumers are
the global amplitude inputs of `EvolutionIntegral` and the supported columns
of `CompleteResidual` (`app:ch_regular_base:eq:energy-complete-residual`).
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ConicAmplitude
open FiniteMasks AmplitudeBounds

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedSpace ℝ F]

/-- The literal conic amplitude with its fixed spatial frequency collar.
No physical cutoff is moved through a differentiated factor
(`app:ch_regular_base:lem:retarded-kernel`). -/
def collared (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ) (a : Euclidean d → ℝ)
    (f : TwoTimePoint (Euclidean d) → F) (q : TwoTimePoint (Euclidean d)) : F :=
  (conicMask a q.2.2.2 : ℂ) • extend ℓ o f q

/-- The actual collared amplitude vanishes on the closed unit frequency ball.
This does not require the homogeneous amplitude to be smooth at zero. -/
theorem collared_eq_zero (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    (a : Euclidean d → ℝ) (f : TwoTimePoint (Euclidean d) → F)
    {q : TwoTimePoint (Euclidean d)} (hq : ‖q.2.2.2‖ ≤ 1) :
    collared ℓ o a f q = 0 := by
  simp [collared, conicMask_eq_zero hq]

/-- Closed frequency support of the actual amplitude retains every angular
shoulder and excludes zero (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem tsupport_collared_frequency (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    (a : Euclidean d → ℝ) (f : TwoTimePoint (Euclidean d) → F) :
    tsupport (collared ℓ o a f) ⊆ {q | q.2.2.2 ∈ tsupport (conicMask a)} := by
  intro q hq
  by_contra hn
  have hz := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
    (continuous_snd.snd.snd.continuousAt : ContinuousAt
      (fun p : TwoTimePoint (Euclidean d) ↦ p.2.2.2) q)
  apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hq
  filter_upwards [hz] with p hp
  simp only [Function.comp_apply, Pi.zero_apply] at hp
  simp [collared, hp]

/-- A positive angular section contains the full closed frequency support,
including the low-frequency shoulder. This is derived from the fixed mask. -/
theorem collared_section_pos (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    (a : Euclidean d → ℝ) (f : TwoTimePoint (Euclidean d) → F)
    (ha : ∀ η ∈ tsupport a, 0 < ℓ η)
    {q : TwoTimePoint (Euclidean d)} (hq : q ∈ tsupport (collared ℓ o a f)) :
    0 < ℓ q.2.2.2 := by
  exact conicMask_tsupport_subset_cone a ha
    (fun η hη t ht ↦ by
      change 0 < ℓ (t • η)
      simpa only [map_smul, smul_eq_mul] using mul_pos ht hη)
    (tsupport_collared_frequency ℓ o a f hq)

/-- Global smoothness is constructed from the globally smooth buffered local
matrix and the fixed angular mask. No regularity at the zero covector or at
the section boundary is assumed (`energy-complete-residual`). -/
theorem contDiff_collared [IsScalarTower ℝ ℂ F] (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    {a : Euclidean d → ℝ} (ha : ContDiff ℝ ∞ a)
    (hapos : ∀ η ∈ tsupport a, 0 < ℓ η)
    {f : TwoTimePoint (Euclidean d) → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (collared ℓ o a f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hq : q ∈ tsupport (collared ℓ o a f)
  · have hp := collared_section_pos ℓ o a f hapos hq
    have he := (contDiffOn_extend ℓ o isOpen_univ hf.contDiffOn).contDiffAt
      ((ConicPhase.isOpen_domain ℓ isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)
    exact ((Complex.ofRealCLM.contDiff.comp
      ((contDiff_conicMask ha).comp contDiff_snd.snd.snd)).contDiffAt).smul he
  · exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hq)

/-- On a high-frequency angular plateau the collared amplitude has exactly
the original conic germ, hence all its derivatives are unchanged. -/
theorem collared_eventuallyEq_extend (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    (a : Euclidean d → ℝ) (f : TwoTimePoint (Euclidean d) → F)
    {q : TwoTimePoint (Euclidean d)}
    (ha : conicMask a =ᶠ[𝓝 q.2.2.2] (fun _ ↦ 1)) :
    collared ℓ o a f =ᶠ[𝓝 q] extend ℓ o f := by
  filter_upwards [ha.comp_tendsto (continuous_snd.snd.snd.continuousAt :
    ContinuousAt (fun p : TwoTimePoint (Euclidean d) ↦ p.2.2.2) q)] with p hp
  simp only [Function.comp_apply] at hp
  simp [collared, hp]

/-- The lower source-time buffer of the original matrix is retained exactly
after conic continuation and the low-frequency collar (`retarded-kernel`). -/
theorem collared_lower_buffer (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    (a : Euclidean d → ℝ) {f : TwoTimePoint (Euclidean d) → F} (b : ℝ)
    (hf : ∀ q, q.2.1 ≤ b → f q = 0) :
    ∀ q, q.2.1 ≤ b → collared ℓ o a f q = 0 := by
  intro q hq
  simp [collared, extend, hf (ConicPhase.normalize ℓ q) hq]

end JanetCartan.RegularSector.Characteristic.ConicAmplitude
