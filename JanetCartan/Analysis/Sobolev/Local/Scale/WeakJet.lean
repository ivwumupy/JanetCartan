module

public import JanetCartan.Analysis.Extension.Mollification.WeakContraction

/-!
# Linear operations on whole-space weak jets

The integration-by-parts identities underlying the restriction spaces in
`app:not:fourier` are preserved by linear operations.
-/

@[expose] public noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace JanetCartan.Mollification

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E}

/-- Addition preserves the whole-space weak derivative identity
(`app:not:fourier`). Integrability of each test pairing follows from compact support. -/
theorem HasWeakFDerivOn.add_univ {f g : E → F} {f' g' : E → E →L[ℝ] F}
    (hf : HasWeakFDerivOn μ f f' univ) (hg : HasWeakFDerivOn μ g g' univ) :
    HasWeakFDerivOn μ (fun x ↦ f x + g x) (fun x ↦ f' x + g' x) univ := by
  refine ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, ?_⟩
  intro ψ hψ hc hs v
  have hψd : Continuous (fun x ↦ fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψdc : HasCompactSupport (fun x ↦ fderiv ℝ ψ x v) :=
    (hc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ ↦ L v) rfl
  have hi (q : E → F) (hq : LocallyIntegrableOn q univ μ) :
      Integrable (fun x ↦ fderiv ℝ ψ x v • q x) μ :=
    (locallyIntegrableOn_univ.mp hq).integrable_smul_left_of_hasCompactSupport hψd hψdc
  have hi' (q : E → E →L[ℝ] F) (hq : LocallyIntegrableOn q univ μ) :
      Integrable (fun x ↦ ψ x • q x v) μ := by
    simpa using (ContinuousLinearMap.apply ℝ F v).integrable_comp
      ((locallyIntegrableOn_univ.mp hq).integrable_smul_left_of_hasCompactSupport
        hψ.continuous hc)
  simp only [add_apply, smul_add]
  rw [integral_add (hi' f' hf.2.1) (hi' g' hg.2.1),
    integral_add (hi f hf.1) (hi g hg.1), hf.2.2 ψ hψ hc hs v, hg.2.2 ψ hψ hc hs v,
    neg_add]

/-- Whole-space weak jets add componentwise (`app:not:fourier`). -/
theorem HasWeakJetOn.add_univ {f g : E → F}
    {J K : (j : ℕ) → E → E [×j]→L[ℝ] F} {s : ℕ}
    (hf : HasWeakJetOn μ f J univ s) (hg : HasWeakJetOn μ g K univ s) :
    HasWeakJetOn μ (fun x ↦ f x + g x) (fun j x ↦ J j x + K j x) univ s := by
  refine ⟨?_, fun j hj ↦ ?_⟩
  · ext x v
    simp [hf.1, hg.1, iteratedFDeriv_zero_apply]
  · simpa only [comp_def, map_add] using (hf.2 j hj).add_univ (hg.2 j hj)

omit [BorelSpace E] in
/-- Real scalar multiplication preserves every weak-jet identity
(`app:not:fourier`). -/
theorem HasWeakJetOn.smul {f : E → F}
    {J : (j : ℕ) → E → E [×j]→L[ℝ] F} {U : Set E} {s : ℕ}
    (hf : HasWeakJetOn μ f J U s) (c : ℝ) :
    HasWeakJetOn μ (fun x ↦ c • f x) (fun j x ↦ c • J j x) U s := by
  refine ⟨?_, fun j hj ↦ ?_⟩
  · ext x v
    simp [hf.1, iteratedFDeriv_zero_apply]
  · simpa only [comp_def, map_smul] using (hf.2 j hj).smul c

/-- The zero function has the zero weak jet at every order (`app:not:fourier`). -/
theorem hasWeakJetOn_zero [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] (U : Set E) (s : ℕ) :
    HasWeakJetOn μ (fun _ ↦ (0 : F)) (fun _ _ ↦ 0) U s := by
  refine ⟨?_, fun j _ ↦ ?_⟩
  · ext x v
    simp
  · convert (hasWeakFDerivOn_of_contDiff μ
      (contDiff_const : ContDiff ℝ 1 (fun _ : E ↦ (0 : E [×j]→L[ℝ] F))) U) using 1
    ext x v w
    simp

end JanetCartan.Mollification
