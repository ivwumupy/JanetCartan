module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Supported
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.Smooth.Correction

/-!
# Admitting the original tensor sources to the fixed smooth inverse

The accepted `FixedDomainInverse.DirectSmooth` constructor acts on local L²
classes with every Sobolev order. This module admits the actual compact smooth
tensor sources after the original stress projection and source cutoff. The
consumer is the canonical ambient completion of that same fixed smooth solver
in `app:ch_response:prop:response-ambient` and its corrected atoms.

The source domain, measure, stress frame and cutoff are supplied once. In
particular, the admission map makes no choice of inverse or smooth representative.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.CorrectedAtoms
open PrimarySourceAdmission AmbientResponse FixedDomainInverse LocalSobolev

variable {n : ℕ} (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)

/-- The literal cutoff stress source, with the Euclidean value type used by
the fixed L² inverse (`app:ch_response:eq:response-full-map`). -/
def euclideanCutoffStressSource : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean n) where
  toFun h x := WithLp.toLp 2 (cutoffSource η (stressSource Q h) x)
  map_add' h k := by
    ext x i
    change cutoffSource η (stressSource Q (h + k)) x i = _
    simp only [map_add, Pi.add_apply]
    rfl
  map_smul' a h := by
    ext x i
    change cutoffSource η (stressSource Q (a • h)) x i = _
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
    rfl

/-- Stress projection and the unchanged source cutoff preserve the original
tensor support (`app:ch_response:prop:response-ambient`). -/
theorem tsupport_euclideanCutoffStressSource_subset (h : MetricField n) :
    tsupport (euclideanCutoffStressSource Q η h) ⊆ tsupport h := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  have hz : stressSource Q h x = 0 := by
    ext i
    change (1 / 2 : ℝ) * tensorPairing (Q x i) (h x) = 0
    simp [hx, tensorPairing]
  simp [euclideanCutoffStressSource, cutoffSource, hz]

variable {S U W : Set (Euclidean n)} (hU : IsOpen U)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)

include hU hQ hη hSU

/-- The original support buffer makes the actual projected source globally
smooth; no global extension of the stress frame is required
(`app:ch_response:prop:response-ambient`). -/
theorem contDiff_euclideanCutoffStressSource (h : compactSmoothSources S) :
    ContDiff ℝ ∞ (euclideanCutoffStressSource Q η h) := by
  have he : ContDiff ℝ ∞ (stressSource Q h) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport (h : MetricField n)
    · exact (contDiffOn_stressSource hQ h.property.1.contDiffOn).contDiffAt
        (hU.mem_nhds (hSU (h.property.2.2 hx)))
    · apply (contDiffAt_const (c := (0 : Fin n → ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      ext i
      change (1 / 2 : ℝ) * tensorPairing (Q y i) ((h : MetricField n) y) = 0
      simp [hy, tensorPairing]
  exact PiLp.contDiff_toLp.comp (hη.smul he)

/-- The full projected source is genuinely L² for Lebesgue measure, before
restriction to the inverse domain (`app:ch_regular:thm:exact-correction`). -/
theorem memLp_euclideanCutoffStressSource (h : compactSmoothSources S) :
    MemLp (euclideanCutoffStressSource Q η h) 2 volume :=
  (contDiff_euclideanCutoffStressSource Q η hU hQ hη hSU h).continuous.memLp_of_hasCompactSupport
    (h.property.2.1.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_euclideanCutoffStressSource_subset Q η h))

/-- Every Sobolev order of the same actual source is supplied by its classical
compactly supported jets (`app:ch_regular:thm:exact-correction`). -/
theorem memRestrictionSobolev_euclideanCutoffStressSource
    (h : compactSmoothSources S) (s : ℕ) :
    MemRestrictionSobolev W s
      (((memLp_euclideanCutoffStressSource Q η hU hQ hη hSU h).restrict W).toLp
        (euclideanCutoffStressSource Q η h)) := by
  have hd := contDiff_euclideanCutoffStressSource Q η hU hQ hη hSU h
  have hc : HasCompactSupport (euclideanCutoffStressSource Q η h) :=
    h.property.2.1.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_euclideanCutoffStressSource_subset Q η h)
  exact ⟨{
    toFun := euclideanCutoffStressSource Q η h
    jet := fun j ↦ iteratedFDeriv ℝ j (euclideanCutoffStressSource Q η h)
    weakJet := Mollification.hasWeakJetOn_of_contDiff volume (hd.of_le (by simp)) univ
    memLp_fun := memLp_euclideanCutoffStressSource Q η hU hQ hη hSU h
    memLp_jet := fun j _ ↦ (hd.continuous_iteratedFDeriv (by simp)).memLp_of_hasCompactSupport
      (hc.iteratedFDeriv j)
    restrict_eq := (MemLp.coeFn_toLp _).symm }⟩

/-- One linear admission of all original compact tensor sources to the SAME
fixed inverse's smooth-source submodule. No representative or inverse is chosen
per atom, scalar or accuracy (`app:ch_response:cor:current-atoms`). -/
def cutoffStressSmoothSource : compactSmoothSources S →ₗ[ℝ] smoothSource W (Euclidean n) where
  toFun h := ⟨((memLp_euclideanCutoffStressSource Q η hU hQ hη hSU h).restrict W).toLp _,
    memRestrictionSobolev_euclideanCutoffStressSource Q η hU hQ hη hSU h⟩
  map_add' h k := by
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add]
    exact MemLp.toLp_add _ _
  map_smul' a h := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, map_smul]
    exact MemLp.toLp_const_smul a _

/-- Admission represents exactly the original cutoff stress field for the
inverse's restricted Lebesgue measure (`app:ch_response:eq:response-full-map`). -/
theorem cutoffStressSmoothSource_coeFn (h : compactSmoothSources S) :
    (cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h : LocalL2 W (Euclidean n))
      =ᵐ[volume.restrict W] euclideanCutoffStressSource Q η h :=
  MemLp.coeFn_toLp ((memLp_euclideanCutoffStressSource Q η hU hQ hη hSU h).restrict W)

/-- On the original support buffer the inverse's zero extension is the exact
whole-space source, including both the stress projection and its supplied
cutoff (`app:ch_regular:eq:exact-physical`). -/
theorem zeroExtend_cutoffStressSmoothSource_coeFn (hW : MeasurableSet W)
    (hSW : S ⊆ W) (h : compactSmoothSources S) :
    SmallSupport.zeroExtend hW
      (cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h : LocalL2 W (Euclidean n))
      =ᵐ[volume] euclideanCutoffStressSource Q η h := by
  apply (SmallSupport.zeroExtend_coeFn hW _).trans
  apply ((ae_eq_restrict_iff_indicator_ae_eq hW).mp
    (cutoffStressSmoothSource_coeFn Q η hU hQ hη hSU h)).trans
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ W
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx]
    exact (image_eq_zero_of_notMem_tsupport (fun hs ↦ hx
      (hSW (h.property.2.2 (tsupport_euclideanCutoffStressSource_subset Q η h hs))))).symm

end JanetCartan.CorrectedAtoms
