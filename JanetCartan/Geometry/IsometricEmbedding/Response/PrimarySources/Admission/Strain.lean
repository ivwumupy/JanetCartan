module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Supported
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.FullRegularity

/-!
# Smoothness and admission of the full cut-off strain

The source of `app:ch_response:cor:current-atoms` is cut off *after* taking the
complete ambient strain. Only local smoothness on the original support buffer
is required. These lemmas feed the retained-family construction in `Admission`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PrimarySourceAdmission
open ResponseSourceExtension

/-- Local smoothness of the complete complex strain
(`app:ch_waves:eq:exact-half-strain`). -/
theorem contDiffOn_complexLinearizedMetric {n N : ℕ}
    {F : Euclidean n → Euclidean N} {W : Euclidean n → EuclideanSpace ℂ (Fin N)}
    {O : Set (Euclidean n)} (ho : IsOpen O)
    (hF : ContDiffOn ℝ ∞ F O) (hW : ContDiffOn ℝ ∞ W O) :
    ContDiffOn ℝ ∞ (WKB.complexLinearizedMetric F W) O := by
  let L : (Fin n → Fin n → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ := LinearMap.id
  let C : (Fin n → Fin n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    ⟨L, L.continuous_of_finiteDimensional⟩
  apply C.contDiff.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  have hf (i : Fin n) (k : Fin N) :
      ContDiffOn ℝ ∞ (fun x ↦ (partialDeriv F x i k : ℂ)) O :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (contDiffOn_euclidean.mp (contDiffOn_partialDeriv ho hF i) k)
  have hw (i : Fin n) (k : Fin N) :
      ContDiffOn ℝ ∞ (fun x ↦ partialDeriv W x i k) O :=
    (contDiffOn_piLp 2).mp
      ((hW.fderiv_of_isOpen ho (by simp)).clm_apply contDiffOn_const) k
  exact ContDiffOn.sum (s := Finset.univ) (fun k _ ↦ ((hf i k).mul (hw j k)).add ((hw i k).mul (hf j k)))

/-- The real tensor quadrature is smooth in the Frobenius topology
(`app:ch_response:cor:current-atoms`). -/
theorem contDiffOn_tensorFieldRealPart {n : ℕ}
    {h : Euclidean n → Matrix (Fin n) (Fin n) ℂ} {O : Set (Euclidean n)}
    (hh : ContDiffOn ℝ ∞ h O) : ContDiffOn ℝ ∞ (tensorFieldRealPart h) O := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] MetricTensor n :=
    { toFun := fun a i j ↦ (a i j).re
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  exact (⟨L, L.continuous_of_finiteDimensional⟩ : _ →L[ℝ] _).contDiff.comp_contDiffOn hh

/-- The imaginary tensor quadrature is smooth with the same norms
(`app:ch_response:cor:current-atoms`). -/
theorem contDiffOn_tensorFieldImagPart {n : ℕ}
    {h : Euclidean n → Matrix (Fin n) (Fin n) ℂ} {O : Set (Euclidean n)}
    (hh : ContDiffOn ℝ ∞ h O) : ContDiffOn ℝ ∞ (tensorFieldImagPart h) O := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] MetricTensor n :=
    { toFun := fun a i j ↦ (a i j).im
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  exact (⟨L, L.continuous_of_finiteDimensional⟩ : _ →L[ℝ] _).contDiff.comp_contDiffOn hh

/-- Both literal quadratures belong to the fixed compact smooth source space.
No extension of the raw atom outside its chart is assumed
(`app:ch_response:cor:current-atoms`). -/
theorem cutoff_strain_quadratures_mem {n N : ℕ}
    {F : Euclidean n → Euclidean N} {W : Euclidean n → EuclideanSpace ℂ (Fin N)}
    {χ : Euclidean n → ℝ} {O : Set (Euclidean n)}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (ho : IsOpen O)
    (hF : ContDiffOn ℝ ∞ F O) (hW : ContDiffOn ℝ ∞ W O) (hs : tsupport χ ⊆ O) :
    tensorFieldRealPart (fun x ↦ χ x • WKB.complexLinearizedMetric F W x) ∈
      compactSmoothSources (tsupport χ) ∧
    tensorFieldImagPart (fun x ↦ χ x • WKB.complexLinearizedMetric F W x) ∈
      compactSmoothSources (tsupport χ) := by
  have h := contDiffOn_complexLinearizedMetric ho hF hW
  have hr := cutoff_mem_compactSmoothSources hχ hc ho (contDiffOn_tensorFieldRealPart h) hs
  have hi := cutoff_mem_compactSmoothSources hχ hc ho (contDiffOn_tensorFieldImagPart h) hs
  have er : tensorFieldRealPart (fun x ↦ χ x • WKB.complexLinearizedMetric F W x) =
      (fun x ↦ χ x • tensorFieldRealPart (WKB.complexLinearizedMetric F W) x) := by
    ext x i j
    simp [tensorFieldRealPart]
  have ei : tensorFieldImagPart (fun x ↦ χ x • WKB.complexLinearizedMetric F W x) =
      (fun x ↦ χ x • tensorFieldImagPart (WKB.complexLinearizedMetric F W) x) := by
    ext x i j
    simp [tensorFieldImagPart]
  exact ⟨er.symm ▸ hr, ei.symm ▸ hi⟩

end JanetCartan.PrimarySourceAdmission
