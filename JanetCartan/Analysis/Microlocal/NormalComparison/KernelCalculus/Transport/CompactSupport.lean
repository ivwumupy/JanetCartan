module

public import JanetCartan.Analysis.Microlocal.NormalComparison.MaskDerivative
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Compact support calculus for the normal transport identity

The boundary cancellation in `app:ch_osc:prop:osc-normal` uses support strictly
inside the input domain. The mask itself need only be smooth on that domain.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace JanetCartan.NormalComparison.CompactTransport

variable {n : ℕ} {D : Set (Euclidean n)}

/-- Local mask smoothness suffices after multiplication by an interior-supported
amplitude (`app:ch_osc:prop:osc-normal`). -/
theorem contDiff_mask_smul {m : Euclidean n → ℝ} {B : Euclidean n → ℂ}
    (hD : IsOpen D) (hm : ContDiffOn ℝ ∞ m D) (hB : ContDiff ℝ ∞ B)
    (hs : tsupport B ⊆ D) : ContDiff ℝ ∞ (fun u ↦ m u • B u) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u ∈ tsupport B
  · exact (hm.contDiffAt (hD.mem_nhds (hs hu))).smul hB.contDiffAt
  · have hz : B =ᶠ[𝓝 u] 0 := notMem_tsupport_iff_eventuallyEq.mp hu
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hz] with v hv
    simp [hv]

/-- Compactly supported smooth factors justify all three integrability premises
of integration by parts (`app:ch_osc:prop:osc-normal`). -/
theorem integral_mul_partialDeriv {f g : Euclidean n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) (j : Fin n) :
    (∫ u, f u * partialDeriv g u j) =
      -(∫ u, partialDeriv f u j * g u) := by
  have hf' : Continuous (fun u ↦ partialDeriv f u j) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hg' : Continuous (fun u ↦ partialDeriv g u j) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hf'.mul hg.continuous).integrable_of_hasCompactSupport hs.mul_left)
    ((hf.continuous.mul hg').integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ (EuclideanSpace.single j 1)).mul_left)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hs.mul_left)
    (fun _ _ ↦ hf.differentiable (by simp) _) (fun _ _ ↦ hg.differentiable (by simp) _)

/-- Integration by parts on the open input domain, with boundary cancellation
derived from compact amplitude support (`app:ch_osc:prop:osc-normal`). -/
theorem integral_mask_mul_partialDeriv {f B : Euclidean n → ℂ}
    {m : Euclidean n → ℝ} (hD : IsOpen D) (hm : ContDiffOn ℝ ∞ m D)
    (hf : ContDiff ℝ ∞ f) (hB : ContDiff ℝ ∞ B)
    (hc : HasCompactSupport B) (hs : tsupport B ⊆ D) (j : Fin n) :
    (∫ u in D, f u * partialDeriv (fun v ↦ m v • B v) u j) =
      -(∫ u in D, partialDeriv f u j * (m u • B u)) := by
  have hms : tsupport (fun u ↦ m u • B u) ⊆ tsupport B := tsupport_smul_subset_right m B
  have hc' : HasCompactSupport (fun u ↦ m u • B u) := hc.smul_left (f := m)
  have hleft : (∫ u in D, f u * partialDeriv (fun v ↦ m v • B v) u j) =
      ∫ u, f u * partialDeriv (fun v ↦ m v • B v) u j := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    change f u * (fderiv ℝ (fun v ↦ m v • B v) u) _ = 0
    have hn : u ∉ tsupport (fun v ↦ m v • B v) := fun h ↦ hu (hs (hms h))
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hn]
    exact mul_zero _
  have hright : (∫ u in D, partialDeriv f u j * (m u • B u)) =
      ∫ u, partialDeriv f u j * (m u • B u) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hn : u ∉ tsupport B := fun h ↦ hu (hs h)
    have hz : m u • B u = 0 := by rw [image_eq_zero_of_notMem_tsupport hn, smul_zero]
    rw [hz, mul_zero]
  rw [hleft, hright]
  exact integral_mul_partialDeriv hf (contDiff_mask_smul hD hm hB hs) hc' j

/-- The integrated first-mask-derivative decomposition, with every boundary and
integrability premise discharged by interior compact support
(`app:ch_osc:prop:osc-normal`). -/
theorem integral_transport_expansion {f Aε : Euclidean n → ℂ}
    {B : Fin n → Euclidean n → ℂ} {m : Euclidean n → ℝ}
    (hD : IsOpen D) (hm : ContDiffOn ℝ ∞ m D)
    (hf : ContDiff ℝ ∞ f) (hA : ContDiff ℝ ∞ Aε)
    (hcA : HasCompactSupport Aε) (hsA : tsupport Aε ⊆ D)
    (hB : ∀ j, ContDiff ℝ ∞ (B j)) (hcB : ∀ j, HasCompactSupport (B j))
    (hsB : ∀ j, tsupport (B j) ⊆ D) :
    (∫ u in D, f u * (m u • Aε u) +
      ∑ j, partialDeriv f u j * (m u • B j u)) =
    ∫ u in D, f u * (m u • transportCoefficient Aε B u +
      ∑ j, partialDeriv m u j • (-B j u)) := by
  have hMA := contDiff_mask_smul hD hm hA hsA
  have hMB j := contDiff_mask_smul hD hm (hB j) (hsB j)
  have hcMA : HasCompactSupport (fun u ↦ m u • Aε u) := hcA.smul_left (f := m)
  have hcMB j : HasCompactSupport (fun u ↦ m u • B j u) := (hcB j).smul_left (f := m)
  have hiA : IntegrableOn (fun u ↦ f u * (m u • Aε u)) D :=
    ((hf.continuous.mul hMA.continuous).integrable_of_hasCompactSupport hcMA.mul_left).integrableOn
  have hiL j : IntegrableOn (fun u ↦ partialDeriv f u j * (m u • B j u)) D :=
    ((((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul
      (hMB j).continuous).integrable_of_hasCompactSupport (hcMB j).mul_left).integrableOn
  have hiR j : IntegrableOn (fun u ↦ f u * partialDeriv (fun v ↦ m v • B j v) u j) D :=
    ((hf.continuous.mul
      (((hMB j).continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
        ((hcMB j).fderiv_apply ℝ (EuclideanSpace.single j 1)).mul_left).integrableOn
  have he : (∫ u in D, f u * (m u • transportCoefficient Aε B u +
      ∑ j, partialDeriv m u j • (-B j u))) =
      ∫ u in D, f u * (m u • Aε u) -
        ∑ j, f u * partialDeriv (fun v ↦ m v • B j v) u j := by
    apply setIntegral_congr_fun hD.measurableSet
    intro u hu
    dsimp only
    rw [← mask_transport_expansion m Aε B u
      ((hm.contDiffAt (hD.mem_nhds hu)).differentiableAt (by simp))
      (fun j ↦ (hB j).differentiable (by simp) u), mul_sub, Finset.mul_sum]
  rw [he, integral_add hiA (integrable_finsetSum _ (fun j _ ↦ hiL j)),
    integral_sub hiA (integrable_finsetSum _ (fun j _ ↦ hiR j)),
    integral_finsetSum _ (fun j _ ↦ hiL j),
    integral_finsetSum _ (fun j _ ↦ hiR j)]
  simp_rw [integral_mask_mul_partialDeriv hD hm hf (hB _) (hcB _) (hsB _)]
  simp [Finset.sum_neg_distrib, sub_neg_eq_add]

end JanetCartan.NormalComparison.CompactTransport
