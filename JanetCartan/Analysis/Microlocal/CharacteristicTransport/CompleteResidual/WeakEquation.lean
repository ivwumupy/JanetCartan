module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.WeakLimit
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Identifying the weak physical action almost everywhere

The local equation consumed by `FixedDomainInverse.exact_physical_localSobolev_ae`
uses the same uncut output as the tested equation. A supplied weak derivative
(in particular, the derivative furnished by local H¹ regularity) identifies its
physical action. This does not infer a classical derivative from strong L²
convergence. Source: `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace JanetCartan.CharacteristicTransport.CompleteResidual

variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "FV" => Fin q → ℂ

/-- The physical operator evaluated on a supplied weak derivative, with the
full zeroth-order term (`app:ch_regular_base:eq:energy-complete-residual`). -/
def physicalWeakApply (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ) (u : E → FV) (du : E → E →L[ℝ] FV)
    (x : E) (i : Fin q) : ℂ :=
  (∑ a, ∑ j, A x a i j • du x (EuclideanSpace.single a 1) j) +
    ∑ j, B x i j • u x j

/-- Classical and weak physical actions use the same coefficient convention
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem physicalWeakApply_fderiv
    (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ) (u : E → FV) :
    physicalWeakApply A B u (fderiv ℝ u) = WKB.firstOrderApply
      (fun x a ↦ ((A x a).map Complex.ofReal).mulVecLin)
      (fun x ↦ ((B x).map Complex.ofReal).mulVecLin) u := by
  funext x i
  simp [physicalWeakApply, WKB.firstOrderApply, Matrix.mulVec, dotProduct,
    partialDeriv, Complex.real_smul]

private theorem integrable_test_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {f : E → F} (hf : LocallyIntegrableOn f U volume) {φ : E → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    Integrable (fun x ↦ φ x • f x) := by
  have hi : Integrable ((tsupport φ).indicator f) :=
    (integrable_indicator_iff hc.measurableSet).mpr (hf.integrableOn_compact_subset hs hc)
  convert hi.smul_of_top_right (hφ.memLp_top_of_hasCompactSupport hc volume) using 1
  funext x
  by_cases hx : x ∈ tsupport φ
  · simp [hx]
  · simp [hx, image_eq_zero_of_notMem_tsupport hx]

/-- The weak derivative supplied by Sobolev regularity gives the same formal
test action. The identity follows from the definition of weak derivative,
tested against the actual coefficient times the test; no successful physical
equation is assumed (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem integral_physicalWeakApply_eq_physicalTestAction
    (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    {U : Set E} {u : E → FV} {du : E → E →L[ℝ] FV}
    (hw : Mollification.HasWeakFDerivOn volume u du U)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ U) (i : Fin q) :
    (∫ x, φ x • physicalWeakApply A B u du x i) = physicalTestAction A B u φ i := by
  let ev (a : Fin n) := ContinuousLinearMap.apply ℝ FV (EuclideanSpace.single a (1 : ℝ))
  have hdu (a : Fin n) : LocallyIntegrableOn (fun x ↦ du x (EuclideanSpace.single a 1)) U volume :=
    (ev a).locallyIntegrableOn_comp hw.2.1
  have huc (j : Fin q) : LocallyIntegrableOn (fun x ↦ u x j) U volume :=
    (ContinuousLinearMap.proj j : FV →L[ℝ] ℂ).locallyIntegrableOn_comp hw.1
  have hdc (a : Fin n) (j : Fin q) :
      LocallyIntegrableOn (fun x ↦ du x (EuclideanSpace.single a 1) j) U volume :=
    (ContinuousLinearMap.proj j : FV →L[ℝ] ℂ).locallyIntegrableOn_comp (hdu a)
  have hiA (a : Fin n) (j : Fin q) : Integrable
      (fun x ↦ (φ x * A x a i j) • du x (EuclideanSpace.single a 1) j) :=
    integrable_test_smul (hdc a j) (hφ.mul (hA a i j)).continuous hc.mul_right
      (tsupport_mul_subset_left.trans hs)
  have hiB (j : Fin q) : Integrable (fun x ↦ (φ x * B x i j) • u x j) :=
    integrable_test_smul (huc j) (hφ.mul (hB i j)).continuous hc.mul_right
      (tsupport_mul_subset_left.trans hs)
  have hparts (a : Fin n) (j : Fin q) :
      (∫ x, (φ x * A x a i j) • du x (EuclideanSpace.single a 1) j) =
        -(∫ x, partialDeriv (fun y ↦ φ y * A y a i j) x a • u x j) := by
    let ψ := fun x ↦ φ x * A x a i j
    have hψ : ContDiff ℝ ∞ ψ := hφ.mul (hA a i j)
    have hψs : tsupport ψ ⊆ U := tsupport_mul_subset_left.trans hs
    have hdψs : tsupport (fun x ↦ partialDeriv ψ x a) ⊆ U :=
      (tsupport_comp_subset (g := fun L : E →L[ℝ] ℝ ↦ L (EuclideanSpace.single a 1))
        (f := fderiv ℝ ψ) rfl).trans ((tsupport_fderiv_subset ℝ).trans hψs)
    let L : FV →L[ℝ] ℂ := ContinuousLinearMap.proj j
    have hp := congrArg L (hw.2.2 ψ hψ hc.mul_right hψs (EuclideanSpace.single a 1))
    have hi₁ := integrable_test_smul (hdu a) hψ.continuous hc.mul_right hψs
    have hi₂ := integrable_test_smul hw.1
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.mul_right.fderiv_apply ℝ (EuclideanSpace.single a 1)) hdψs
    rw [map_neg, ← L.integral_comp_comm hi₁, ← L.integral_comp_comm hi₂] at hp
    exact hp
  simp only [physicalWeakApply, smul_add, Finset.smul_sum, ← mul_smul]
  rw [integral_add (integrable_finsetSum _ (fun a _ ↦
      integrable_finsetSum _ (fun j _ ↦ hiA a j)))
    (integrable_finsetSum _ (fun j _ ↦ hiB j)),
    integral_finsetSum _ (fun a _ ↦ integrable_finsetSum _ (fun j _ ↦ hiA a j)),
    integral_finsetSum _ (fun j _ ↦ hiB j)]
  simp_rw [integral_finsetSum _ (fun j _ ↦ hiA _ j), hparts]
  simp only [physicalTestAction, Finset.sum_neg_distrib]

/-- A tested equation for the same output with an actual weak derivative is an
almost-everywhere physical equation on the open measurement domain. In the
parametrix consumer, the derivative is furnished by the graph/PDO H¹ estimates
for smooth sources (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem physicalWeakApply_ae_eq_of_test
    (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    {U : Set E} (hU : IsOpen U) {u g : E → FV} {du : E → E →L[ℝ] FV}
    (hw : Mollification.HasWeakFDerivOn volume u du U)
    (hg : LocallyIntegrableOn g U volume)
    (htest : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∀ i, physicalTestAction A B u φ i = ∫ x, φ x • g x i) :
    physicalWeakApply A B u du =ᵐ[volume.restrict U] g := by
  have hP (i : Fin q) : LocallyIntegrableOn (fun x ↦ physicalWeakApply A B u du x i) U volume := by
    apply (locallyIntegrableOn_iff hU.isLocallyClosed).mpr
    intro K hKU hK
    have huK := hw.1.integrableOn_compact_subset hKU hK
    have hdK := hw.2.1.integrableOn_compact_subset hKU hK
    apply Integrable.add
    · apply integrable_finsetSum
      intro a _
      apply integrable_finsetSum
      intro j _
      let L := (ContinuousLinearMap.proj j : FV →L[ℝ] ℂ).comp
        (ContinuousLinearMap.apply ℝ FV (EuclideanSpace.single a (1 : ℝ)))
      exact IntegrableOn.continuousOn_smul (L.integrable_comp hdK)
        (hA a i j).continuous.continuousOn hK
    · apply integrable_finsetSum
      intro j _
      exact IntegrableOn.continuousOn_smul
        ((ContinuousLinearMap.proj j : FV →L[ℝ] ℂ).integrable_comp huK)
        (hB i j).continuous.continuousOn hK
  have he (i : Fin q) : ∀ᵐ x ∂volume, x ∈ U → physicalWeakApply A B u du x i = g x i := by
    have hgc := (ContinuousLinearMap.proj i : FV →L[ℝ] ℂ).locallyIntegrableOn_comp hg
    have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero ((hP i).sub hgc)
    have hzero : ∀ᵐ x ∂volume, x ∈ U → physicalWeakApply A B u du x i - g x i = 0 := by
      apply hz
      intro φ hφ hc hs
      simp only [Pi.sub_apply, smul_sub]
      rw [integral_sub (integrable_test_smul (hP i) hφ.continuous hc hs)
        (integrable_test_smul hgc hφ.continuous hc hs),
        integral_physicalWeakApply_eq_physicalTestAction A B hA hB hw hφ hc hs,
        htest φ hφ hc hs i]
      exact sub_self _
    filter_upwards [hzero] with x hx hxU
    exact sub_eq_zero.mp (hx hxU)
  apply (ae_restrict_iff' hU.measurableSet).mpr
  filter_upwards [ae_all_iff.mpr he] with x hx hxU
  exact funext fun i ↦ hx i hxU

end JanetCartan.CharacteristicTransport.CompleteResidual
