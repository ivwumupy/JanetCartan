module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.WeakAction

/-!
# Local L² closure of the physical test identity

The frequency-limit step of `app:ch_regular_base:eq:energy-complete-residual`.
Only the functions and the complete right sides converge. No convergence of
their separate derivatives, or pointwise differentiation of the limit, is
assumed. The intended strong-limit producers are
`EvolutionIntegral.KernelIdentification.exists_retardedOperator_of_regularizations`
for the elapsed terms and the matrix PDO realization for the algebraic and
diagonal terms. Their instantiation and the finite-cutoff complete identity
are separate obligations of the complete-residual construction.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace JanetCartan.CharacteristicTransport.CompleteResidual

variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "FV" => Fin q → ℂ

private theorem integral_test_eq_restrict {U : Set E} {φ : E → ℝ}
    (hs : tsupport φ ⊆ U) (f : E → ℂ) :
    (∫ x, φ x • f x) = ∫ x in U, φ x • f x := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h)), zero_smul]

private theorem tendsto_integral_coordinate {ι : Type*} {l : Filter ι}
    {U : Set E} {u : ι → E → FV} {v : E → FV}
    (hu : ∀ k, MemLp (u k) 2 (volume.restrict U)) (hv : MemLp v 2 (volume.restrict U))
    (hlim : Tendsto (fun k ↦ eLpNorm (u k - v) 2 (volume.restrict U)) l (𝓝 0))
    {φ : E → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (j : Fin q) :
    Tendsto (fun k ↦ ∫ x, φ x • u k x j) l (𝓝 (∫ x, φ x • v x j)) := by
  simp_rw [integral_test_eq_restrict hs]
  let L : FV →L[ℝ] ℂ := ContinuousLinearMap.proj j
  exact Mollification.tendsto_integral_smul_of_tendsto_eLpNorm_two
    (hφ.memLp_of_hasCompactSupport hc) (fun k ↦ L.comp_memLp' (hu k)) (L.comp_memLp' hv)
    (Mollification.tendsto_eLpNorm_compCLM_sub L hu hv hlim)

/-- The full physical test action is continuous under local L² convergence.
Compact tests control coefficient derivatives without any bound on the
derivatives of the approximating solver
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem physicalTestAction_tendsto {ι : Type*} {l : Filter ι}
    (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    {U : Set E} {u : ι → E → FV} {v : E → FV}
    (hu : ∀ k, MemLp (u k) 2 (volume.restrict U)) (hv : MemLp v 2 (volume.restrict U))
    (hlim : Tendsto (fun k ↦ eLpNorm (u k - v) 2 (volume.restrict U)) l (𝓝 0))
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ U) (i : Fin q) :
    Tendsto (fun k ↦ physicalTestAction A B (u k) φ i) l
      (𝓝 (physicalTestAction A B v φ i)) := by
  unfold physicalTestAction
  apply Tendsto.add
  · apply Tendsto.neg
    apply tendsto_finsetSum
    intro a _
    apply tendsto_finsetSum
    intro j _
    apply tendsto_integral_coordinate hu hv hlim
    · exact ((hφ.mul (hA a i j)).continuous_fderiv (by simp)).clm_apply continuous_const
    · exact hc.mul_right.fderiv_apply ℝ (EuclideanSpace.single a 1)
    · exact (tsupport_comp_subset (g := fun L : E →L[ℝ] ℝ ↦ L (EuclideanSpace.single a 1))
        (f := fderiv ℝ (fun y ↦ φ y * A y a i j)) rfl).trans
        ((tsupport_fderiv_subset ℝ).trans (tsupport_mul_subset_left.trans hs))
  · apply tendsto_finsetSum
    intro j _
    exact tendsto_integral_coordinate hu hv hlim (hφ.mul (hB i j)).continuous
      hc.mul_right (tsupport_mul_subset_left.trans hs) j

/-- A finite-frequency equation passes to the uncut tested equation using
only local L² convergence of its two sides. The finite right side must be
the complete expression, including the diagonal, differentiated correction,
algebraic PDO term and output commutator. This theorem does not supply that
finite identity or instantiate the graph/PDO limits; it supplies their weak
closure (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem firstOrderApply_test_of_tendsto {ι : Type*} {l : Filter ι} [NeBot l]
    (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    {U : Set E} (hU : MeasurableSet U) {u r : ι → E → FV} {v g : E → FV}
    (hsmooth : ∀ k, ContDiff ℝ 1 (u k))
    (hu : ∀ k, MemLp (u k) 2 (volume.restrict U))
    (hr : ∀ k, MemLp (r k) 2 (volume.restrict U))
    (hv : MemLp v 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hulim : Tendsto (fun k ↦ eLpNorm (u k - v) 2 (volume.restrict U)) l (𝓝 0))
    (hrlim : Tendsto (fun k ↦ eLpNorm (r k - g) 2 (volume.restrict U)) l (𝓝 0))
    (hfinite : ∀ k, WKB.firstOrderApply
      (fun x a ↦ ((A x a).map Complex.ofReal).mulVecLin)
      (fun x ↦ ((B x).map Complex.ofReal).mulVecLin) (u k) =ᵐ[volume.restrict U] r k)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ U) (i : Fin q) :
    physicalTestAction A B v φ i = ∫ x, φ x • g x i := by
  apply tendsto_nhds_unique (physicalTestAction_tendsto A B hA hB hu hv hulim hφ hc hs i)
  apply (tendsto_integral_coordinate hr hg hrlim hφ.continuous hc hs i).congr
  intro k
  rw [← integral_firstOrderApply_eq_physicalTestAction A B hA hB (hsmooth k) hφ hc i]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hU).mp (hfinite k)] with x hx
  by_cases hxU : x ∈ U
  · rw [hx hxU]
  · rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hxU (hs h))]
    simp only [zero_smul]

end JanetCartan.CharacteristicTransport.CompleteResidual
