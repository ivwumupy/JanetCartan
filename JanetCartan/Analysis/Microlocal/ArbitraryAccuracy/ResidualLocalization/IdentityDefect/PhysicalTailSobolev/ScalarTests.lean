module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailSobolev.Schur
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.CompactIntegral
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.WeakJetFourier.Scalar

/-!
# Scalar test estimates from physical kernel jets

For `app:ch_regular:eq:chain-tail`, differentiation of the literal kernel
integral is justified on the compact test carrier. Schur bounds put every
classical jet in L². The existing weak-jet comparison then gives the actual
Fourier Sobolev norm, including its physical `2π` convention.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailSobolev

open FourierIntegral.WeightedPrincipalLocalization.SourceIndependentBounds
open FiniteChain.Retarded.KernelDecay LocalSobolev Pseudodifferential

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Classical output jets of a compact-test kernel integral satisfy the
dimension-only Schur estimate. Smoothness and the derivative formula are
proved here, rather than supplied as extra analytic premises. Consumer:
`exists_physicalTail_scalarTest_fourierSobolev_constant`
(`app:ch_regular:eq:chain-tail`). -/
theorem physicalTail_scalarTest_jet_bound
    (k : E → E → ℂ) (hk : ContDiff ℝ ∞ (Function.uncurry k))
    (g : E → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j ≤ m, ∀ x y,
      (1 + ‖x - y‖) ^ (n + 1) * ‖iteratedFDeriv ℝ j (fun z ↦ k z y) x‖ ≤ B) :
    ContDiff ℝ ∞ (fun x ↦ ∫ y, k x y * g y) ∧
      ∀ j ≤ m,
        MemLp (iteratedFDeriv ℝ j (fun x ↦ ∫ y, k x y * g y)) 2 volume ∧
        (eLpNorm (iteratedFDeriv ℝ j (fun x ↦ ∫ y, k x y * g y)) 2 volume).toReal ≤
          physicalTailSchurConstant n * B * (eLpNorm g 2 volume).toReal := by
  let f : E × E → ℂ := fun p ↦ k p.1 p.2 * g p.2
  have hf : ContDiff ℝ ∞ f := hk.mul (hg.comp contDiff_snd)
  have hz : ∀ x y, y ∉ tsupport g → f (x, y) = 0 := by
    intro x y hy
    simp only [f, image_eq_zero_of_notMem_tsupport hy, mul_zero]
  refine ⟨contDiff_integral_commonCarrier hf hgc hz, ?_⟩
  intro j hj
  have he (x y : E) : iteratedFDeriv ℝ j (fun z ↦ f (z, y)) x =
      g y • iteratedFDeriv ℝ j (fun z ↦ k z y) x := by
    have hh : (fun z ↦ f (z, y)) = fun z ↦ g y • k z y := by
      funext z
      exact mul_comm _ _
    rw [hh]
    exact iteratedFDeriv_const_smul_apply'
      (((hk.comp (contDiff_id.prodMk contDiff_const)).contDiffAt).of_le (by simp))
  have hb' (x y : E) : ‖iteratedFDeriv ℝ j (fun z ↦ f (z, y)) x‖ ≤
      B * (frequencyDifferenceMajorant (x - y) * ‖g y‖) := by
    rw [he, norm_smul]
    calc
      _ ≤ ‖g y‖ * (B * frequencyDifferenceMajorant (x - y)) :=
        mul_le_mul_of_nonneg_left (le_physicalTailMajorant x y (hb j hj x y)) (norm_nonneg _)
      _ = _ := by ring
  have hbound := physicalTail_integral_memLp_bound
    (fun x y ↦ iteratedFDeriv ℝ j (fun z ↦ f (z, y)) x)
    (contDiff_outputJet hf j).continuous.stronglyMeasurable
    (fun y ↦ ‖g y‖) hg.continuous.norm.stronglyMeasurable (fun _ ↦ norm_nonneg _)
    (hg.continuous.integrable_of_hasCompactSupport hgc).norm
    (hg.continuous.memLp_of_hasCompactSupport hgc).norm hB hb'
  have hjint : iteratedFDeriv ℝ j (fun x ↦ ∫ y, k x y * g y) =
      fun x ↦ ∫ y, iteratedFDeriv ℝ j (fun z ↦ f (z, y)) x :=
    funext (iteratedFDeriv_integral_commonCarrier hf hgc hz j)
  rw [hjint]
  simpa only [eLpNorm_norm _ hg.continuous.aestronglyMeasurable] using hbound.2

/-- A compact scalar test has actual Fourier Sobolev output from the finite
pointwise kernel-jet bound. This constructs the weak derivatives from the
classical integral and invokes the existing weak-jet Fourier theorem.
The constant precedes the kernel, budget, test and L² representative.
Consumer: the vector compact-test bound for both physical tails in
`app:ch_regular:eq:resolved-angular-tail`. -/
theorem exists_physicalTail_scalarTest_fourierSobolev_constant (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : E → E → ℂ),
      ContDiff ℝ ∞ (Function.uncurry k) → ∀ B : ℝ, 0 ≤ B →
      (∀ j ≤ m, ∀ x y,
        (1 + ‖x - y‖) ^ (n + 1) * ‖iteratedFDeriv ℝ j (fun z ↦ k z y) x‖ ≤ B) →
      ∀ (g : E → ℂ), ContDiff ℝ ∞ g → HasCompactSupport g →
      ∀ v : Lp (α := E) ℂ 2, (v =ᵐ[volume] fun x ↦ ∫ y, k x y * g y) →
      MemFourierSobolev (m : ℝ) v ∧
        fourierSobolevNorm (m : ℝ) v ≤ C * B * (eLpNorm g 2 volume).toReal := by
  obtain ⟨D, hD, hFourier⟩ := scalarFourierSobolev_extension_bounds n m
  refine ⟨D * (m + 1) * physicalTailSchurConstant n,
    mul_nonneg (mul_nonneg hD.le (by positivity)) physicalTailSchurConstant_nonneg, ?_⟩
  intro k hk B hB hb g hg hgc v hv
  obtain ⟨hsm, hjets⟩ := physicalTail_scalarTest_jet_bound k hk g hg hgc m hB hb
  let F := fun x ↦ ∫ y, k x y * g y
  have hF : MemLp F 2 volume := (Lp.memLp v).ae_eq hv
  let u : LocalL2 (univ : Set E) ℂ :=
    (hF.mono_measure Measure.restrict_le_self).toLp F
  let e : SobolevExtension univ m u := {
    toFun := F
    jet := fun j ↦ iteratedFDeriv ℝ j F
    weakJet := Mollification.hasWeakJetOn_of_contDiff volume (hsm.of_le (by simp)) univ
    memLp_fun := hF
    memLp_jet := fun j hj ↦ (hjets j hj).1
    restrict_eq := (hF.mono_measure Measure.restrict_le_self).coeFn_toLp.symm }
  have he : e.toL2 = v := Lp.ext (e.toL2_coeFn.trans hv.symm)
  have hnorm : e.jetNorm ≤
      (m + 1) * (physicalTailSchurConstant n * B * (eLpNorm g 2 volume).toReal) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (m + 1),
          physicalTailSchurConstant n * B * (eLpNorm g 2 volume).toReal := by
        apply Finset.sum_le_sum
        intro j hj
        exact (hjets j (by simpa using Finset.mem_range.mp hj)).2
      _ = _ := by simp
  have h := hFourier univ u e
  rw [he] at h
  refine ⟨h.1, h.2.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left hnorm hD.le).trans_eq (by ring)

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailSobolev
