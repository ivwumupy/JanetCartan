module

public import JanetCartan.Analysis.Sobolev.Local.Comparison.Intrinsic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Uniqueness of local weak jets

The integration-by-parts identities in `app:ch_regular_base:lem:ball-extension`
determine a locally integrable weak derivative almost everywhere on an open set,
even when the represented functions agree only almost everywhere there. Iteration
gives uniqueness of every finite weak jet. In particular, the intrinsic auxiliary
Sobolev norm of `app:not:fourier` is independent of the chosen weak data, and its
infimum definition equals the norm of any such data.

The uniqueness argument only needs local integrability, already included in the
weak-derivative identities; local L² membership is used in the intrinsic data.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Function
open scoped Topology ContDiff

namespace JanetCartan.Mollification

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem integrable_test_smul {f : E → F} {U : Set E}
    (hf : LocallyIntegrableOn f U μ) {ψ : E → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    Integrable (fun x ↦ ψ x • f x) μ := by
  have hi : Integrable ((tsupport ψ).indicator f) μ :=
    (integrable_indicator_iff hc.measurableSet).mpr (hf.integrableOn_compact_subset hs hc)
  convert hi.smul_of_top_right (hψ.memLp_top_of_hasCompactSupport hc μ) using 1
  funext x
  by_cases hx : x ∈ tsupport ψ
  · simp [hx]
  · simp [hx, image_eq_zero_of_notMem_tsupport hx]

variable [CompleteSpace F]

/-- Weak derivatives of almost-everywhere equal functions agree almost everywhere
on an open set (`app:ch_regular_base:lem:ball-extension`). The conclusion concerns
the whole continuous-linear-map field, with one common exceptional null set. -/
theorem HasWeakFDerivOn.ae_eq {f g : E → F} {D D' : E → E →L[ℝ] F}
    {U : Set E} (hf : HasWeakFDerivOn μ f D U) (hg : HasWeakFDerivOn μ g D' U)
    (hU : IsOpen U) (hfg : f =ᵐ[μ.restrict U] g) : D =ᵐ[μ.restrict U] D' := by
  have hfg' := (ae_restrict_iff' hU.measurableSet).mp hfg
  have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.2.1.sub hg.2.1)
  have hzero : ∀ᵐ x ∂μ, x ∈ U → (D - D') x = 0 := by
    apply hz
    intro ψ hψ hc hs
    have hi := integrable_test_smul hf.2.1 hψ.continuous hc hs
    have hi' := integrable_test_smul hg.2.1 hψ.continuous hc hs
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub hi hi', sub_eq_zero]
    ext v
    rw [ContinuousLinearMap.integral_apply hi, ContinuousLinearMap.integral_apply hi']
    simp only [smul_apply]
    rw [hf.2.2 ψ hψ hc hs v, hg.2.2 ψ hψ hc hs v]
    congr 1
    apply integral_congr_ae
    filter_upwards [hfg'] with x hx
    by_cases hxU : x ∈ U
    · rw [hx hxU]
    · have hd : fderiv ℝ ψ x = 0 := by
        apply notMem_support.mp
        exact fun h ↦ hxU (hs (support_fderiv_subset ℝ h))
      simp [hd]
  apply (ae_restrict_iff' hU.measurableSet).mpr
  filter_upwards [hzero] with x hx hxU
  exact sub_eq_zero.mp (hx hxU)

/-- Every order of a finite weak jet is determined almost everywhere by the local
class of its represented function (`app:ch_regular_base:lem:ball-extension`). -/
theorem HasWeakJetOn.ae_eq {f g : E → F}
    {J K : (j : ℕ) → E → E [×j]→L[ℝ] F} {U : Set E} {m : ℕ}
    (hf : HasWeakJetOn μ f J U m) (hg : HasWeakJetOn μ g K U m)
    (hU : IsOpen U) (hfg : f =ᵐ[μ.restrict U] g) :
    ∀ j ≤ m, J j =ᵐ[μ.restrict U] K j := by
  intro j hj
  induction j with
  | zero =>
    rw [hf.1, hg.1]
    filter_upwards [hfg] with x hx
    ext v
    simp only [iteratedFDeriv_zero_apply, hx]
  | succ j ih =>
    have he := (hf.2 j (by omega)).ae_eq (hg.2 j (by omega)) hU (ih (by omega))
    filter_upwards [he] with x hx
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F).injective hx

end JanetCartan.Mollification

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {U : Set (EuclideanSpace ℝ (Fin n))} {m : ℕ} {u : LocalL2 U F}

namespace IntrinsicSobolevData

/-- Intrinsic weak data for the same local L² class have the same jets almost
everywhere on an open domain (`app:not:fourier`). -/
theorem jet_ae_eq (d e : IntrinsicSobolevData U m u) (hU : IsOpen U)
    (j : ℕ) (hj : j ≤ m) : d.jet j =ᵐ[volume.restrict U] e.jet j :=
  d.weakJet.ae_eq e.weakJet hU (d.restrict_eq.trans e.restrict_eq.symm) j hj

/-- The auxiliary intrinsic jet norm is independent of the weak representative
on an open domain (`app:not:fourier`). -/
theorem jetNorm_eq (d e : IntrinsicSobolevData U m u) (hU : IsOpen U) :
    d.jetNorm = e.jetNorm := by
  unfold jetNorm jetL2Norm
  apply Finset.sum_congr rfl
  intro j hj
  rw [eLpNorm_congr_ae (d.jet_ae_eq e hU j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))]

end IntrinsicSobolevData

/-- The infimum defining the intrinsic Sobolev norm equals the jet norm of any
representing data on an open domain (`app:not:fourier` and
`app:ch_regular_base:lem:ball-extension`). -/
theorem intrinsicSobolevNorm_eq_jetNorm (hU : IsOpen U) (d : IntrinsicSobolevData U m u) :
    intrinsicSobolevNorm U m u = d.jetNorm := by
  apply le_antisymm (intrinsicSobolevNorm_le d)
  apply le_csInf
  · exact ⟨d.jetNorm, d, rfl⟩
  · rintro _ ⟨e, rfl⟩
    exact le_of_eq (d.jetNorm_eq e hU)

end JanetCartan.LocalSobolev
