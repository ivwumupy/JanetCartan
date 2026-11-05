module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.Oscillation
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Compact supported calculus for the joint carrier integral

Analytic prerequisites for `paper-v2.tex`, `new:eq:carrier-ibp`, consumed by
`DirectEvolution.CompactTransfer`. Smoothness is required only on the original
open integration domain. Compact support inside that domain supplies all
integrability and domination hypotheses.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer

variable {n : ℕ} {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth supported integrand extends across the boundary by its actual
zero values. Used for every compact amplitude in `new:eq:carrier-ibp`. -/
theorem contDiff_of_support_subset
    {D K : Set (CarrierVariables n)} (hD : IsOpen D) (hK : IsClosed K)
    (hKD : K ⊆ D) {g : CarrierVariables n → F}
    (hg : ContDiffOn ℝ ∞ g D) (hs : Function.support g ⊆ K) :
    ContDiff ℝ ∞ g := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w ∈ D
  · exact hg.contDiffAt (hD.mem_nhds hw)
  · apply (show ContDiffAt ℝ ∞ (fun _ : CarrierVariables n ↦ (0 : F)) w from
      contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [hK.isOpen_compl.mem_nhds (show w ∈ Kᶜ from fun h ↦ hw (hKD h))]
      with z hz
    exact Function.notMem_support.mp (fun h ↦ hz (hs h))

omit [NormedSpace ℝ F] in
/-- The same compact integration box controls the support closure, as required
for the boundary-free integration by parts in `new:eq:carrier-ibp`. -/
theorem hasCompactSupport_of_support_subset
    {K : Set (CarrierVariables n)} (hK : IsCompact K)
    {g : CarrierVariables n → F} (hs : Function.support g ⊆ K) :
    HasCompactSupport g :=
  hK.of_isClosed_subset (isClosed_tsupport g) (closure_minimal hs hK.isClosed)

/-- Compact supported local smoothness supplies integrability for the actual
joint Lebesgue integral in `new:eq:carrier-ibp`. -/
theorem integrable_of_support_subset
    {D K : Set (CarrierVariables n)} (hD : IsOpen D) (hK : IsCompact K)
    (hKD : K ⊆ D) {g : CarrierVariables n → F}
    (hg : ContDiffOn ℝ ∞ g D) (hs : Function.support g ⊆ K) :
    Integrable g :=
  ((contDiff_of_support_subset hD hK.isClosed hKD hg hs).continuous).integrable_of_hasCompactSupport (hasCompactSupport_of_support_subset hK hs)

/-- External derivatives preserve the same integration support. This retains
the actual differentiated masks in every iteration of `new:eq:carrier-ibp`. -/
theorem support_parameterFDeriv_subset
    {U : Set E} {K : Set (CarrierVariables n)} (hU : IsOpen U)
    {g : E → CarrierVariables n → F}
    (hs : ∀ p ∈ U, Function.support (g p) ⊆ K)
    {q : E} (hq : q ∈ U) (e : E) :
    Function.support (fun w ↦ fderiv ℝ (fun p ↦ g p w) q e) ⊆ K := by
  intro w hw
  by_contra hn
  have hz : (fun p ↦ g p w) =ᶠ[𝓝 q] (fun _ ↦ (0 : F)) := by
    filter_upwards [hU.mem_nhds hq] with p hp
    exact Function.notMem_support.mp (fun h ↦ hn (hs p hp h))
  exact hw (by simp [hz.fderiv_eq])

variable [FiniteDimensional ℝ E] [CompleteSpace F]

/-- Differentiation under the actual compact supported integral, with output
and parameter directions treated together. Domination is proved from compactness,
not assumed. Consumer: the left side of `new:eq:carrier-ibp`. -/
theorem fderiv_integral_supported
    {U : Set E} {D K : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D)
    {g : E → CarrierVariables n → F}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ D))
    (hs : ∀ p ∈ U, Function.support (g p) ⊆ K)
    {q : E} (hq : q ∈ U) (e : E) :
    fderiv ℝ (fun p ↦ ∫ w, g p w) q e =
      ∫ w, fderiv ℝ (fun p ↦ g p w) q e := by
  let : IsFiniteMeasure ((volume : Measure (CarrierVariables n)).restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have heq : (fun p ↦ ∫ w, g p w) =ᶠ[𝓝 q] (fun p ↦ ∫ w in K, g p w) := by
    filter_upwards [hU.mem_nhds hq] with p hp
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    exact Function.notMem_support.mp (fun h ↦ hw (hs p hp h))
  have hd := fderiv_compactParameterIntegral (μ := volume) hU hD hK hKD hg hq
  change fderiv ℝ (fun p ↦ ∫ w in K, g p w) q =
    ∫ w in K, fderiv ℝ (fun p ↦ g p w) q at hd
  have hi : IntegrableOn (fun w ↦ fderiv ℝ (fun p ↦ g p w) q) K :=
    integrableOn_parameterFDeriv (μ := volume) hU hD hK hKD hg hq
  rw [heq.fderiv_eq, hd, ContinuousLinearMap.integral_apply hi]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro w hw
  have hz : (fun p ↦ g p w) =ᶠ[𝓝 q] (fun _ ↦ (0 : F)) := by
    filter_upwards [hU.mem_nhds hq] with p hp
    exact Function.notMem_support.mp (fun h ↦ hw (hs p hp h))
  simp [hz.fderiv_eq]

variable [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

omit [CompleteSpace F] in
/-- One constant integration direction, with a phase smooth only on the
supported box. This is the analytic integration-by-parts step used for each
component of the literal vector field in `new:eq:carrier-ibp`. -/
theorem integral_fderiv_smul_eq_neg
    {D K : Set (CarrierVariables n)} (hD : IsOpen D) (hK : IsCompact K)
    (hKD : K ⊆ D) {Ω : CarrierVariables n → ℂ} {g : CarrierVariables n → F}
    (hΩ : ContDiffOn ℝ ∞ Ω D) (hg : ContDiffOn ℝ ∞ g D)
    (hs : Function.support g ⊆ K) (v : CarrierVariables n) :
    (∫ w, fderiv ℝ Ω w v • g w) = -(∫ w, Ω w • fderiv ℝ g w v) := by
  have hg' := contDiff_of_support_subset hD hK.isClosed hKD hg hs
  have hdg : ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ g w v) D :=
    ((hg'.fderiv_right (by simp)).clm_apply contDiff_const).contDiffOn
  have hdΩ : ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ Ω w v) D :=
    (hΩ.fderiv_of_isOpen hD (by simp)).clm_apply contDiffOn_const
  have hsg : tsupport g ⊆ K := closure_minimal hs hK.isClosed
  have hsdg : Function.support (fun w ↦ fderiv ℝ g w v) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ v).trans hsg)
  have hi₁ : Integrable (fun w ↦ fderiv ℝ Ω w v • g w) :=
    integrable_of_support_subset hD hK hKD (hdΩ.smul hg)
      ((Function.support_smul_subset_right _ _).trans hs)
  have hi₂ : Integrable (fun w ↦ Ω w • fderiv ℝ g w v) :=
    integrable_of_support_subset hD hK hKD (hΩ.smul hdg)
      ((Function.support_smul_subset_right _ _).trans hsdg)
  have hi₀ : Integrable (fun w ↦ Ω w • g w) :=
    integrable_of_support_subset hD hK hKD (hΩ.smul hg)
      ((Function.support_smul_subset_right _ _).trans hs)
  have hi := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable hi₁ hi₂ hi₀
    (fun w hw ↦ (hΩ.contDiffAt (hD.mem_nhds (hKD (hsg hw)))).differentiableAt (by simp))
    (fun w _ ↦ hg'.differentiable (by simp) w)
  simpa only [neg_neg] using congrArg Neg.neg hi.symm

end JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
