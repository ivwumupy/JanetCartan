module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalAmbientResponse
public import JanetCartan.Analysis.Microlocal.Localization.CompactSupport

/-! The original full response inherits support from the native solver and
incoming tensor. No new response cutoff is inserted. The actual paired-solver
output support is a separate native operator obligation; when supplied, these
identities give the global compact smoothness needed by the sampled Schwartz
primary (`main:prop:current-waves`, `app:ch_response:eq:response-full-map`). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalAmbientResponse
open CorrectedAtoms PrimarySourceAdmission AmbientResponse FixedDomainInverse

/-- Canonical completion is local in the first jet of its covector and in
its tensor value, even where the background geometry has not been regularized. -/
theorem completedVariation_tsupport_subset {n N : ℕ}
    (F : Euclidean n → Euclidean N) (u : Euclidean n → Euclidean n) (h : MetricField n) :
    tsupport (completedVariation F u h) ⊆ tsupport u ∪ tsupport h := by
  apply closure_minimal _ ((isClosed_tsupport u).union (isClosed_tsupport h))
  intro x hx
  by_contra hout
  have hu : x ∉ tsupport u := fun hu ↦ hout (Or.inl hu)
  have hh : x ∉ tsupport h := fun hh ↦ hout (Or.inr hh)
  have hu0 : u x = 0 := image_eq_zero_of_notMem_tsupport hu
  have hh0 : h x = 0 := image_eq_zero_of_notMem_tsupport hh
  have hdu (j : Fin n) : fderiv ℝ (fun y ↦ u y j) x = 0 := by
    have hg : (fun y ↦ u y j) =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hu] with y hy
      simp [hy]
    rw [hg.fderiv_eq]
    simp
  have hc : symmCovariantDeriv F u x = 0 := by
    ext i j
    simp [symmCovariantDeriv, partialDeriv, hdu, hu0]
  have ht : tangentLift F u x = 0 := by
    simp [tangentLift, hu0]
  exact hx (by simp [completedVariation, ht, hc, hh0])

variable {n N : ℕ} (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S U W : Set (Euclidean n)} (hU : IsOpen U)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)
    (solver : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v))

/-- Exact original solver support passes through the uncut ambient extension.
The support hypothesis concerns the native solver, not a recut output. -/
theorem uncutAmbientExtension_tsupport_subset {K : Set (Euclidean n)}
    (hS : S ⊆ K)
    (hs : ∀ v, tsupport (solver v) ⊆ K) (h : compactSmoothSources S) :
    tsupport (uncutAmbientExtension F Q η hU hQ hη hSU solver hsolver h) ⊆ K := by
  rw [uncutAmbientExtension_apply]
  exact (completedVariation_tsupport_subset F _ _).trans
    (union_subset (hs _) (h.property.2.2.trans hS))

/-- The unchanged native compact output gives a globally compact smooth
ambient response. Regularity of the background is required only on the actual
open output neighborhood, never outside it. -/
theorem uncutAmbientExtension_compact_smooth {K Ω : Set (Euclidean n)}
    (hK : IsCompact K) (hS : S ⊆ K) (hKΩ : K ⊆ Ω)
    (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ ∞ F Ω)
    (hi : IsImmersionOn F Ω) (hrank : HasFullNormalRankOn F Ω)
    (hs : ∀ v, tsupport (solver v) ⊆ K) (h : compactSmoothSources S) :
    ContDiff ℝ ∞ (uncutAmbientExtension F Q η hU hQ hη hSU solver hsolver h) ∧
      HasCompactSupport (uncutAmbientExtension F Q η hU hQ hη hSU solver hsolver h) := by
  have hsupport := uncutAmbientExtension_tsupport_subset F Q η hU hQ hη hSU solver hsolver hS hs h
  refine ⟨Localization.contDiff_of_contDiffOn_support_neighborhood hΩ
    (uncutAmbientExtension_contDiffOn F Q η hU hQ hη hSU solver hsolver hΩ hF hi hrank h)
    (hsupport.trans hKΩ),?_⟩
  exact hK.of_isClosed_subset (isClosed_tsupport _) hsupport

end JanetCartan.PhysicalPrimary.OriginalAmbientResponse
