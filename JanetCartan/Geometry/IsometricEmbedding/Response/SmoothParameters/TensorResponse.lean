module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SmoothParameters.JointRegularity
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Strain
public import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# Applying the same real response to tensor source families

The finite component reduction for `app:ch_response:prop:response-ambient`.
The fixed physical coordinate chart and both real quadratures are retained.
All component maps below are compositions of the ONE supplied real response;
none is an independently selected inverse. This connects the scalar Lebesgue
jet realization to the metric sources used by CorrectedAtoms.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.ResponseSmoothParameters
open RetardedSobolev.Spaces ResponseSourceExtension PrimarySourceAdmission

variable {d n N : ℕ}

/-- Insert one scalar test into a tensor entry in the fixed physical chart
(`app:ch_response:prop:response-ambient`). The source coordinates are unchanged
through every parameter and physical derivative. -/
def tensorTestSource (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n) (i j : Fin n) :
    Test d →ₗ[ℂ] (Euclidean n → Matrix (Fin n) (Fin n) ℂ) where
  toFun u x := Matrix.single i j (u.val (e.symm x))
  map_add' u v := by funext x; exact Matrix.single_add _ _ _ _
  map_smul' a u := by funext x; exact (Matrix.smul_single a i j _).symm

/-- One component of the SAME real response, complexified only by applying it
to the two original real quadratures (`app:ch_response:prop:response-ambient`).
This definition makes the quantitative producer input unambiguous. -/
def tensorComponentResponse (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    (S : Set (Euclidean n))
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N)) (i j : Fin n) :
    supportedTests (e ⁻¹' S) →ₗ[ℝ] (Euclidean n → EuclideanSpace ℂ (Fin N)) :=
  (((complexifyResponse B).comp (tensorTestSource e i j)).comp
    (supportedTests (e ⁻¹' S)).subtype).restrictScalars ℝ

/-- Each component source has both quadratures in the original compact smooth
source domain (`app:ch_response:cor:current-atoms`). This discharges the domain
and spatial smoothness obligations for the actual fixed ambient response. -/
theorem tensorTestSource_quadratures_mem
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    {S : Set (Euclidean n)} (hS : IsCompact S) (i j : Fin n)
    (u : supportedTests (e ⁻¹' S)) :
    tensorFieldRealPart (tensorTestSource e i j u.val) ∈ compactSmoothSources S ∧
    tensorFieldImagPart (tensorTestSource e i j u.val) ∈ compactSmoothSources S := by
  have hu : ContDiff ℝ ∞ (tensorTestSource e i j u.val) :=
    ((Matrix.singleLinearMap ℝ i j : ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ).toContinuousLinearMap).contDiff.comp
      (u.val.property.1.comp e.symm.contDiff)
  have hz (x : Euclidean n) (hx : x ∉ S) : tensorTestSource e i j u.val x = 0 := by
    have hux : u.val.val (e.symm x) = 0 :=
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (by simpa using u.property h)
    simp [tensorTestSource, hux]
  have hr : ContDiff ℝ ∞ (tensorFieldRealPart (tensorTestSource e i j u.val)) :=
    contDiffOn_univ.mp (contDiffOn_tensorFieldRealPart hu.contDiffOn)
  have hi : ContDiff ℝ ∞ (tensorFieldImagPart (tensorTestSource e i j u.val)) :=
    contDiffOn_univ.mp (contDiffOn_tensorFieldImagPart hu.contDiffOn)
  have hsr : tsupport (tensorFieldRealPart (tensorTestSource e i j u.val)) ⊆ S := by
    apply closure_minimal _ hS.isClosed
    intro x hx
    by_contra hn
    apply hx
    change (fun a b ↦ (tensorTestSource e i j u.val x a b).re) = 0
    rw [hz x hn]
    rfl
  have hsi : tsupport (tensorFieldImagPart (tensorTestSource e i j u.val)) ⊆ S := by
    apply closure_minimal _ hS.isClosed
    intro x hx
    by_contra hn
    apply hx
    change (fun a b ↦ (tensorTestSource e i j u.val x a b).im) = 0
    rw [hz x hn]
    rfl
  exact ⟨⟨hr, hS.of_isClosed_subset (isClosed_tsupport _) hsr, hsr⟩,
    ⟨hi, hS.of_isClosed_subset (isClosed_tsupport _) hsi, hsi⟩⟩

/-- The actual tensor source has a jointly smooth finite scalar-test
decomposition in the fixed physical chart (`app:ch_response:cor:current-atoms`).
The decomposition agrees exactly on the parameter domain and uses its original
compact source support. It is shared by the joint regularity and derivative
commutation deductions. -/
theorem exists_supported_tensor_components
    {p : ℕ} (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    {S : Set (Euclidean n)} (hS : IsCompact S) {U : Set (Euclidean p)}
    (f : Euclidean p → Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hf : ContDiffOn ℝ ∞ (fun w : Euclidean n × Euclidean p ↦ f w.2 w.1) (univ ×ˢ U))
    (hs : ∀ a ∈ U, tsupport (f a) ⊆ S) :
    ∃ g : (Fin n × Fin n) → Euclidean p → supportedTests (e ⁻¹' S),
      (∀ ij, ContDiffOn ℝ ∞ (fun w ↦ (g ij w.1).val.val w.2) (U ×ˢ univ)) ∧
      ∀ a ∈ U, f a = ∑ ij : Fin n × Fin n, tensorTestSource e ij.1 ij.2 (g ij a).val := by
  classical
  have hK : IsCompact (e ⁻¹' S) := e.toHomeomorph.isCompact_preimage.mpr hS
  let entry (ij : Fin n × Fin n) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun A := A ij.1 ij.2
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
  have hscalar (ij : Fin n × Fin n) : ContDiffOn ℝ ∞
      (fun w : Euclidean p × (ℝ × (Fin d → ℝ)) ↦ f w.1 (e w.2) ij.1 ij.2)
      (U ×ˢ univ) :=
    (entry ij).contDiff.comp_contDiffOn
      (hf.comp ((e.contDiff.comp contDiff_snd).prodMk contDiff_fst).contDiffOn
        (fun w hw ↦ ⟨mem_univ _, hw.1⟩))
  have hss (ij : Fin n × Fin n) (a : Euclidean p) (ha : a ∈ U) :
      tsupport (fun x ↦ f a (e x) ij.1 ij.2) ⊆ e ⁻¹' S := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    have hz : f a (e x) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hn (hs a ha h)
    exact hx (congrArg (fun A ↦ A ij.1 ij.2) hz)
  let tests (ij : Fin n × Fin n) (a : Euclidean p) : supportedTests (e ⁻¹' S) :=
    if ha : a ∈ U then
      ⟨⟨fun x ↦ f a (e x) ij.1 ij.2,
        (hscalar ij).comp_contDiff (contDiff_const.prodMk contDiff_id)
          (fun _ ↦ ⟨ha, mem_univ _⟩),
        hK.of_isClosed_subset (isClosed_tsupport _) (hss ij a ha)⟩, hss ij a ha⟩
    else 0
  refine ⟨tests, fun ij ↦ ?_, fun a ha ↦ ?_⟩
  · apply (hscalar ij).congr
    intro w hw
    simp only [tests, dite_eq_left hw.1]
  · funext x
    simpa only [Fintype.sum_prod_type, Finset.sum_apply, tensorTestSource,
      LinearMap.coe_mk, AddHom.coe_mk, tests, dite_eq_left ha, e.apply_symm_apply]
      using Matrix.matrix_eq_sum_single (f a x)

/-- Joint tensor-source regularity implies joint regularity of the SAME real
response. The only analytic inputs are its ordinary spatial smoothness on
`compactSmoothSources S` and its finite Sobolev-to-uniform estimates in the
fixed coordinate chart (`app:ch_response:thm:response-literal-transfer`).
The estimates belong to `both-fixed-inverse` and its ambient coefficient
profiles; their constants precede every test and parameter. -/
theorem contDiffOn_tensorResponse
    {p : ℕ} {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n) (c : Euclidean p ≃L[ℝ] Z)
    {S L O : Set (Euclidean n)} (hS : IsCompact S) (hL : IsCompact L)
    (hO : IsOpen O) (hOL : O ⊆ L) {V : Set Z} (hV : IsOpen V)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (hBreg : ∀ h : compactSmoothSources S, ContDiff ℝ ∞ (B h))
    (hB : ∀ i j : Fin n, ∀ q : ℕ, ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : supportedTests (e ⁻¹' S), ∀ x ∈ L,
        ‖iteratedFDeriv ℝ q (tensorComponentResponse e S B i j u) x‖ ≤
          C * ‖ofTest s volume u.val‖)
    (f : Z → Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hf : ContDiffOn ℝ ∞ (fun w : Euclidean n × Z ↦ f w.2 w.1) (univ ×ˢ V))
    (hs : ∀ a ∈ V, tsupport (f a) ⊆ S) :
    ContDiffOn ℝ ∞ (fun w : Euclidean n × Z ↦ complexifyResponse B (f w.2) w.1)
      (O ×ˢ V) := by
  classical
  let U := c ⁻¹' V
  have hU : IsOpen U := hV.preimage c.continuous
  have hK : IsCompact (e ⁻¹' S) := e.toHomeomorph.isCompact_preimage.mpr hS
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hsource : ContDiffOn ℝ ∞
      (fun w : Euclidean n × Euclidean p ↦ f (c w.2) w.1) (univ ×ˢ U) :=
    hf.comp (contDiffOn_fst.prodMk (c.contDiff.comp_contDiffOn contDiffOn_snd))
      (fun w hw ↦ ⟨mem_univ _, hw.2⟩)
  obtain ⟨tests, ht, he⟩ := exists_supported_tensor_components e hS
    (fun a ↦ f (c a)) hsource (fun a ha ↦ hs (c a) ha)
  have hcomponent (ij : Fin n × Fin n) : ContDiffOn ℝ ∞
      (fun w : Euclidean n × Z ↦
        tensorComponentResponse e S B ij.1 ij.2 (tests ij (c.symm w.2)) w.1) (O ×ˢ V) := by
    have hr (u : supportedTests (e ⁻¹' S)) :
        ContDiff ℝ ∞ (tensorComponentResponse e S B ij.1 ij.2 u) := by
      obtain ⟨hre, him⟩ := tensorTestSource_quadratures_mem e hS ij.1 ij.2 u
      exact contDiff_complexifyResponse B _ (hBreg ⟨_, hre⟩) (hBreg ⟨_, him⟩)
    have hh := contDiffOn_joint_supportedResponse hU hK hO hOL
      (tensorComponentResponse e S B ij.1 ij.2) hr (hB ij.1 ij.2) (tests ij) (ht ij)
    exact hh.comp (f := fun w : Euclidean n × Z ↦ (c.symm w.2, w.1))
      ((c.symm.contDiff.comp contDiff_snd).prodMk contDiff_fst).contDiffOn
      (fun w hw ↦ ⟨by simpa [U] using hw.2, hw.1⟩)
  have hsum : ContDiffOn ℝ ∞
      (fun w : Euclidean n × Z ↦ ∑ ij : Fin n × Fin n,
        tensorComponentResponse e S B ij.1 ij.2 (tests ij (c.symm w.2)) w.1) (O ×ˢ V) :=
    ContDiffOn.sum fun ij _ ↦ hcomponent ij
  apply hsum.congr
  intro w hw
  have hdecomp : f w.2 = ∑ ij : Fin n × Fin n,
      tensorTestSource e ij.1 ij.2 (tests ij (c.symm w.2)).val := by
    simpa only [c.apply_symm_apply] using he (c.symm w.2) (by simpa [U] using hw.2)
  rw [hdecomp, map_sum]
  simp only [Finset.sum_apply, tensorComponentResponse,
    LinearMap.restrictScalars_apply, LinearMap.comp_apply, Submodule.subtype_apply]

end JanetCartan.ResponseSmoothParameters
