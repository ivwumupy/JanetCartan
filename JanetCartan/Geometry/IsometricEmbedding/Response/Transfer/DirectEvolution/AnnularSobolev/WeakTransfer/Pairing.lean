module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.Compact

/-!
# Local weak identities for the actual compact branch sums

The spatial weak derivative identity after any ordered combination of output
and parameter derivatives in `new:eq:carrier-ibp`. Tests are supported inside
the original output/parameter domain. No extension of the phase across the
boundary and no regularity assumption on the output are used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
open Pseudodifferential FourierIntegral CompactTransfer BranchAmplitudes
variable {n r : ℕ} {P ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [Fintype ι]
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "V" => Fin r → ℂ

omit [FiniteDimensional ℝ P] in
/-- Local joint smoothness is preserved by the actual ordered derivative word.
Used to test the annular expansion after mixed output/parameter derivatives
in `app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiffOn_originalDatumDerivative {U : Set (E × P)} (hU : IsOpen U)
    {g : E × P → V} (hg : ContDiffOn ℝ ∞ g U) (es : List (E × P)) :
    ContDiffOn ℝ ∞ (originalDatumDerivative es g) U := by
  induction es with
  | nil => exact hg
  | cons e es ih =>
    exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

private theorem integrable_test_smul {W : Set E} {g : E → V} {ψ : E → ℝ}
    (hg : ContinuousOn g W) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ W) : Integrable (fun x => ψ x • g x) := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_smul_subset_left ψ g).trans (subset_tsupport ψ))).mp
  exact (hψ.continuousOn.smul (hg.mono hs)).integrableOn_compact hc

private theorem integral_test_smul_fderiv {W : Set E} (hW : IsOpen W)
    {g : E → V} (hg : ContDiffOn ℝ ∞ g W)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ W) (v : E) :
    (∫ x, ψ x • fderiv ℝ g x v) = - ∫ x, fderiv ℝ ψ x v • g x := by
  have hdψ : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : HasCompactSupport (fun x => fderiv ℝ ψ x v) := hc.fderiv_apply ℝ v
  have hss : tsupport (fun x => fderiv ℝ ψ x v) ⊆ W :=
    (tsupport_fderiv_apply_subset ℝ v).trans hs
  apply integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
  · exact integrable_test_smul hg.continuousOn hdψ hcs hss
  · exact integrable_test_smul
      ((hg.fderiv_of_isOpen (m := ∞) hW (by simp)).clm_apply contDiffOn_const).continuousOn
      hψ.continuous hc hs
  · exact integrable_test_smul hg.continuousOn hψ.continuous hc hs
  · exact fun x _ => hψ.differentiable (by simp) x
  · exact fun x hx => (hg.contDiffAt (hW.mem_nhds (hs hx))).differentiableAt (by simp)

/-- Weak spatial differentiation of the actual branch sum after ANY joint
output/parameter word. Each term acts on the corresponding ordered derivative
of the original datum. All smoothness, integral interchange and integration by
parts follow from primitive local geometry and the original compact support.
The frequency and order factors stay fixed throughout. Source:
`new:eq:carrier-ibp`, consumed by `app:ch_response:eq:direct-envelope-profile`. -/
theorem normalizedBranchIntegral_weak_spatialDerivative
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    {f : (E × P) → CarrierVariables n → ℝ} {w₀ : E × P → CarrierVariables n}
    {U : Set (E × P)} {D K : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {α : (E × P) → CarrierVariables n → Mat} {a : E × P → V}
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D)) (ha : ContDiff ℝ ∞ a)
    (hs : ∀ q ∈ U, Function.support (α q) ⊆ K)
    (hw₀ : ContDiffOn ℝ ∞ w₀ U)
    (hcritical : ∀ q ∈ U, gradient (f q) (w₀ q) = 0)
    (hvalue : ∀ q ∈ U, f q (w₀ q) = 0) (h₀ : MapsTo w₀ U D)
    (hinv : ∀ q ∈ U, ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w))
    (lam : ℝ) (p : ℤ) (es : List (E × P)) (c : P) (v : E)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : ∀ x ∈ tsupport ψ, (x, c) ∈ U) :
    (∫ x, ψ x • ((jointTransferTerms b ((v, 0) :: es)).map fun t =>
      normalizedBranchIntegral b f w₀ α a t lam p (x, c)).sum) =
    - ∫ x, fderiv ℝ ψ x v • ((jointTransferTerms b es).map fun t =>
      normalizedBranchIntegral b f w₀ α a t lam p (x, c)).sum := by
  let W : Set E := {x | (x, c) ∈ U}
  have hW : IsOpen W := hU.preimage (continuous_id.prodMk continuous_const)
  let g := originalDatumDerivative es
    (normalizedBranchIntegral b f w₀ α a initialJointTransferTerm lam p)
  have hg : ContDiffOn ℝ ∞ g U := contDiffOn_originalDatumDerivative hU
    (contDiffOn_normalizedBranchIntegral b hU hD hcD hK hKD hf hα ha hs hw₀ h₀
      hinv lam p [] initialJointTransferTerm (by simp [jointTransferTerms, orderedTransferAction])) es
  have hgs : ContDiffOn ℝ ∞ (fun x => g (x, c)) W :=
    hg.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hx => hx)
  have hex (ds : List (E × P)) {x : E} (hx : x ∈ W) :=
    originalDatumDerivative_normalizedIntegral_expansion b hU hD hcD hK hKD hf
      hα ha hs hw₀ hcritical hvalue h₀ hinv lam p ds hx
  have hd {x : E} (hx : x ∈ W) :
      fderiv ℝ (fun y => g (y, c)) x v =
        ((jointTransferTerms b ((v, 0) :: es)).map fun t =>
          normalizedBranchIntegral b f w₀ α a t lam p (x, c)).sum := by
    have hcomp := ((hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.comp x
      ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (𝕜 := ℝ) c x))
    have he := congrArg (fun L : E →L[ℝ] V => L v) hcomp.fderiv
    exact he.trans (hex ((v, 0) :: es) hx)
  calc
    _ = ∫ x, ψ x • fderiv ℝ (fun y => g (y, c)) x v := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport ψ
      · rw [hd (hψs x hx)]
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_smul, zero_smul]
    _ = - ∫ x, fderiv ℝ ψ x v • g (x, c) :=
      integral_test_smul_fderiv hW hgs ψ hψ hψc hψs v
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport ψ
      · rw [show g (x, c) = _ from hex es (hψs x hx)]
      · have hz : fderiv ℝ ψ x v = 0 := by
          have hn : x ∉ tsupport (fun x => fderiv ℝ ψ x v) :=
            fun h => hx (tsupport_fderiv_apply_subset ℝ v h)
          exact image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ ψ x v) hn
        rw [hz, zero_smul, zero_smul]

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
