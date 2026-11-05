module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.ParameterClass

/-!
# Joint spatial weak and L² parameter derivatives of annular kernels

This identifies the output in `annular_joint_sobolev_of_expansion` with the
actual parameter derivative of the SAME realized L² family. Spatial derivatives
are taken as tempered derivatives; parameter derivatives are genuine Fréchet
norm derivatives. Only literal kernel agreement is supplied by low calculus.
Source: `app:ch_response:lem:energy-carrier-jets` and `new:eq:carrier-ibp`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter LineDeriv
open scoped ContDiff SchwartzMap Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
open Pseudodifferential FourierIntegral CompactTransfer BranchAmplitudes
variable {n r : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

variable {ι : Type} [Fintype ι] [FiniteDimensional ℝ P]
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The joint expansion of the SAME L² family, with actual parameter
derivatives and actual original-datum words. The physical graph, elapsed time
and frequency remain fixed in the normalized kernel. No output derivative,
regularity, norm estimate or convergence assumption is an input. Consumer:
`annular_joint_sobolev_of_expansion` (`new:eq:carrier-ibp`). -/
theorem realizedBranchFamily_joint_derivative_expansion
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    {f : (E × P) → CarrierVariables n → ℝ} {w₀ : E × P → CarrierVariables n}
    {U : Set (E × P)} {D K : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {α : (E × P) → CarrierVariables n → Mat} {a : E × P → Fin r → ℂ}
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D)) (ha : ContDiff ℝ ∞ a)
    (hs : ∀ q ∈ U, Function.support (α q) ⊆ K)
    (hw₀ : ContDiffOn ℝ ∞ w₀ U)
    (hcritical : ∀ q ∈ U, gradient (f q) (w₀ q) = 0)
    (hvalue : ∀ q ∈ U, f q (w₀ q) = 0) (h₀ : MapsTo w₀ U D)
    (hinv : ∀ q ∈ U, ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w))
    (lam : ℝ) (p : ℤ) (ps : List P) (is : List (Fin n))
    {X : Set E} (hX : IsCompact X)
    (houtput : ∀ q ∈ tsupport (Function.uncurry α), q.1.1 ∈ X)
    {C : Set P} (hC : IsOpen C) (hXU : X ×ˢ C ⊆ U) {c : P} (hc : c ∈ C)

    (F : P → H)
    (hF : ∀ c ∈ C, F c =ᵐ[volume] fun x => WithLp.toLp 2
      (normalizedBranchIntegral b f w₀ α a initialJointTransferTerm lam p (x, c)))
    (T : JointTransferTerm n P Mat ι → H)
    (hT : ∀ js : List (Fin n), js.length ≤ is.length →
      ∀ t ∈ jointTransferTerms b ((js.map fun i => (EuclideanSpace.single i (1 : ℝ), (0 : P))) ++ ps.map (fun v => ((0 : E), v))),
        T t =ᵐ[volume] fun x => WithLp.toLp 2
          (normalizedBranchIntegral b f w₀ α a t lam p (x, c))) :
    orderedTransferAction (fun i => lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
      ((orderedTransferAction (fun v F c => fderiv ℝ F c v) ps F c : H) : 𝓢'(E, V)) =
      ((jointTransferTerms b ((is.map fun i => (EuclideanSpace.single i (1 : ℝ), (0 : P))) ++
        ps.map (fun v => ((0 : E), v)))).map fun t => (T t : 𝓢'(E, V))).sum := by
  let g := normalizedBranchIntegral b f w₀ α a initialJointTransferTerm lam p
  have hg : ContDiffOn ℝ ∞ g (univ ×ˢ C) :=
    contDiffOn_normalizedBranchIntegral_output_strip b hU hD hcD hK hKD hf hα ha hs hw₀ h₀
      hinv lam p [] initialJointTransferTerm (by simp [jointTransferTerms, orderedTransferAction])
      hX.isClosed houtput hXU
  have hgs (q : E × P) (hq : q.1 ∉ X) : g q = 0 :=
    normalizedBranchIntegral_zero_of_notMem_output b f w₀ α a [] _
      (by simp [jointTransferTerms, orderedTransferAction]) houtput lam p hq
  let ds := ps.map fun v => ((0 : E), v)
  have hsum : ((jointTransferTerms b ds).map T).sum =ᵐ[volume]
      fun x => WithLp.toLp 2 (originalDatumDerivative ds g (x, c)) := by
    have hh := coe_list_sum_eq_joint (r := r) (W := (univ : Set E))
      (jointTransferTerms b ds) T
      (fun t x => normalizedBranchIntegral b f w₀ α a t lam p (x, c))
      (fun t ht => by simpa only [Measure.restrict_univ] using hT [] (Nat.zero_le _) t ht)
    simp only [Measure.restrict_univ] at hh
    filter_upwards [hh] with x hx
    rw [hx]
    exact congrArg (WithLp.toLp 2)
      (originalDatumDerivative_normalizedIntegral_expansion_of_output_support
        b hU hD hcD hK hKD hf hα ha hs hw₀ hcritical hvalue h₀ hinv lam p ds
          hX.isClosed houtput hXU hc x).symm
  have hparam : orderedTransferAction (fun v F c => fderiv ℝ F c v) ps F c =
      ((jointTransferTerms b ds).map T).sum := by
    rw [orderedParameterDerivative_eq_supportedJointWordClass g hC hg hX hgs F hF ps hc]
    exact Lp.ext ((supportedJointWordClass_ae g hC hg hX hgs ds hc).trans hsum.symm)
  rw [hparam]
  have h := realizedBranchSum_tempered_spatialWords b hU hD hcD hK hKD hf hα ha hs hw₀
    hcritical hvalue h₀ hinv lam p ds is hX houtput hC hXU hc T hT
  rw [h]
  change (Lp.toTemperedDistributionCLM V volume 2) _ = _
  rw [map_list_sum]
  simp only [List.map_map, Function.comp_def, Lp.toTemperedDistributionCLM_apply, ds]

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
