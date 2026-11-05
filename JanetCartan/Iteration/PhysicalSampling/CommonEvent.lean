module

public import JanetCartan.Iteration.PhysicalSampling.OriginalBounds
public import JanetCartan.Iteration.PhysicalMean.SamplingEvent

/-!
# One realization for the original measured and original scalar rows

The analytic scalar inputs are produced by `exists_original_scalar_sampling_bounds`.
The globally cut scalar kernel is used only to apply the all-label Bernstein
theorem. Its original failure budget, continuum means, finite samples and all
prefix deviations are then restored by exact identities. No independent
realization, inverse sampling weight or duplicated sample is introduced.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace JanetCartan.PhysicalSampling

open Sampling SeparatedSampling Sampling.Realization RawInputPartition SamplingKernelBounds
  LatticeQuadrature Sampling.BackgroundQuadrature

/-- Use the all-label scalar extension in the common event, while the conclusion
retains the SAME original scalar row and the SAME measured realization.
The scalar sharp and mean premises are the outputs of `OriginalBounds`, not
measured-row coercivity or inversion assumptions (`new:eq:amplitude-test`). -/
theorem exists_common_original_scalar_realization
    {n J p : ℕ} {A : Type*} [Fintype A]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hkpos : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4)) (hp : 0 < p)
    (D Dscalar : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (β : A → Point → ℝ) (hβ : ∀ a, Continuous (β a))
    (hβone : ∀ a z, |β a z| ≤ 1)
    (hn : 1 ≤ n) {ψ : A → Point → ℝ} {B h C_op R C t : ℝ} {P : A → ℝ}
    (hplateau : ∀ a z, ψ a z ≠ 0 → β a z = 1)
    (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hψc : ∀ a, Continuous (ψ a))
    (hh : 0 < h) (hh₁ : h ≤ 1) (hC_op : 0 ≤ C_op)
    (hband : ∀ a (i : RefinedIndex J) c z,
      ‖(D a).operator (refinedRadius i) (i.1, (c, z))‖ ^ 2 ≤ C_op * refinedRadius i)
    (hbandScalar : ∀ a (i : RefinedIndex J) c z,
      ‖(scalarCarrierCutKernel (Dscalar a) (β a) (hβ a) (hβone a)).operator
        (refinedRadius i) (i.1, (c, z))‖ ^ 2 ≤ C_op * refinedRadius i)
    (hblock : ∀ a, (nodesPerBlock p : ℝ) * (h ^ 3 * (P a * 1 ^ 3)) *
      ((3 * C_op) * (2 : ℝ) ^ J) ≤ R)
    (hR : 0 < R) (hC : 0 < C)
    (hmean : ‖∑ a, patchMeanNormal p B (ψ a) (convolvedBoxWindow κ p) h
      (fun c z ↦ refinedKernelPrefix (D a) J (c, z))‖ ≤ C)
    (hmeanScalar : ‖∑ a, patchMeanNormal p B (ψ a) (convolvedBoxWindow κ p) h
      (fun c z ↦ refinedKernelPrefix (Dscalar a) J (c, z))‖ ≤ C)
    (ht : 0 < t) (hthreshold : R * C + R * t / 3 ≤ t ^ 2)
    (hfailure : (J + 1 : ENNReal) * OperatorCompression.bernsteinTail R (R * C)
      (R * ((∑ a, ((D a).squaredKernelConstant * (1 + (2 : ℝ) ^ n)) *
        (countConstant p B * (P a * 1 ^ 3))) * ((2 : ℝ) ^ J) ^ n)) t +
      (J + 1 : ENNReal) * OperatorCompression.bernsteinTail R (R * C)
      (R * ((∑ a, ((Dscalar a).squaredKernelConstant * (1 + (2 : ℝ) ^ n)) *
        (countConstant p B * (P a * 1 ^ 3))) * ((2 : ℝ) ^ J) ^ n)) t < 1) :
    ∃ ξ : A → ShiftSpace p B h,
      (∀ a q i, 0 ≤ extendedShift (ξ a) q i ∧ extendedShift (ξ a) q i < h) ∧
      (∀ L ≤ J, ‖familyDeviation p B ψ (convolvedBoxWindow κ p) h
        (fun a c z ↦ refinedKernelPrefix (D a) L (c, z)) ξ‖ ≤ t) ∧
      (∀ L ≤ J, ‖familyDeviation p B ψ (convolvedBoxWindow κ p) h
        (fun a c z ↦ refinedKernelPrefix (Dscalar a) L (c, z)) ξ‖ ≤ t) ∧
      (∀ a, SampleGeometry p B (P a) 1 (ψ a) (convolvedBoxWindow κ p) h
        (extendedShift (ξ a))) ∧
      (∀ (G : A → (Fin 3 → Fin (p + 1)) → Point → V) (Q : A → ℝ),
        (∀ a c, ContDiff ℝ p (fun z ↦ ψ a z • G a c z)) →
        (∀ a, 0 ≤ Q a) →
        (∀ a c z, ‖iteratedFDeriv ℝ p (fun z ↦ ψ a z • G a c z) z‖ ≤ Q a) →
        ‖familyBackgroundError p B ψ (convolvedBoxWindow κ p) h
          (fun a ↦ extendedShift (ξ a)) G‖ ≤
            backgroundQuadratureConstant p B * (∑ a, Q a) * h ^ p) := by
  let Dcut := fun a ↦ scalarCarrierCutKernel (Dscalar a) (β a) (hβ a) (hβone a)
  have hmeanCut : ‖∑ a, patchMeanNormal p B (ψ a) (convolvedBoxWindow κ p) h
      (fun c z ↦ refinedKernelPrefix (Dcut a) J (c, z))‖ ≤ C := by
    have heq : (∑ a, patchMeanNormal p B (ψ a) (convolvedBoxWindow κ p) h
        (fun c z ↦ refinedKernelPrefix (Dcut a) J (c, z))) =
        ∑ a, patchMeanNormal p B (ψ a) (convolvedBoxWindow κ p) h
          (fun c z ↦ refinedKernelPrefix (Dscalar a) J (c, z)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact scalarCarrierCutKernel_patchMeanNormal _ _ _ _ _ (hplateau a) _ _ _ _
    rwa [heq]
  obtain ⟨ξ, hξ, hmeasured, hscalar, hgeometry, hbackground⟩ :=
    PhysicalMean.exists_common_measured_scalar_realization (V := V) hc hs hm hkpos hk hp
      D Dcut hn hψ hψc hh hh₁ hC_op hband hbandScalar hblock hR hC hmean hmeanCut
      ht hthreshold (by simpa only [Dcut, scalarCarrierCutKernel_squaredKernelConstant] using hfailure)
  refine ⟨ξ, hξ, hmeasured, ?_, hgeometry, hbackground⟩
  intro L hL
  have he := scalarCarrierCutKernel_familyDeviation Dscalar β hβ hβone ψ hplateau
    B h (convolvedBoxWindow κ p) ξ L
  exact he ▸ hscalar L hL

end JanetCartan.PhysicalSampling
