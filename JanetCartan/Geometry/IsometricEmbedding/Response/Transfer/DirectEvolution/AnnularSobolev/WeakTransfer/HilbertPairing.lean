module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.Pairing

/-!
# Weak pairing of bounded realizations of the literal annular branches

This transfers the compact integral identity to the same Euclidean-fiber L²
outputs. The premise identifies each bounded output with its displayed joint
kernel; it contains no derivative identity. `annularBranchOperator_ae_jointIntegral`
and its reverse counterpart supply this identification from physical test
realizations. Consumer: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
open Pseudodifferential FourierIntegral CompactTransfer BranchAmplitudes
variable {n r : ℕ} {P ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [Fintype ι]
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

private theorem integral_test_smul_congr_ae {W : Set E} {ψ : E → ℝ}
    (hs : tsupport ψ ⊆ W) {g h : E → V} (he : g =ᵐ[volume.restrict W] h) :
    (∫ x, ψ x • g x) = ∫ x, ψ x • h x := by
  have hr (f : E → V) : (∫ x in W, ψ x • f x) = ∫ x, ψ x • f x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), zero_smul]
  rw [← hr g, ← hr h]
  exact integral_congr_ae (EventuallyEq.rfl.smul he)

/-- Finite bounded branch sums retain the literal joint integral representative.
Used by the local weak pairing and its tempered-distribution characterization
in `app:ch_response:eq:direct-envelope-profile`. -/
theorem coe_list_sum_eq_joint {J : Type} (l : List J)
    (T : J → H) (g : J → E → Fin r → ℂ) {W : Set E}
    (hT : ∀ j ∈ l, T j =ᵐ[volume.restrict W] fun x => WithLp.toLp 2 (g j x)) :
    (l.map T).sum =ᵐ[volume.restrict W]
      fun x => WithLp.toLp 2 ((l.map fun j => g j x).sum) := by
  induction l with
  | nil =>
    change (0 : H) =ᵐ[volume.restrict W] fun _ => (0 : V)
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_zero V 2 (volume : Measure E))] with x hx
    exact hx
  | cons j js ih =>
    have hj := hT j (by simp)
    have hjs := ih (fun k hk => hT k (by simp [hk]))
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_add (T j) ((js.map T).sum)), hj, hjs]
      with x hx hjx hjsx
    simpa only [List.map_cons, List.sum_cons, Pi.add_apply, hjx, hjsx, WithLp.toLp_add] using hx

/-- The primitive compact expansion gives a weak derivative identity for
bounded L² realizations of its SAME literal branches. This applies directly to
`annularBranchOperator` and `reverseAnnularBranchOperator` after their physical
kernel identifications, including arbitrary original-datum parameter words.
The derivative is a conclusion; only agreement with the literal kernels is
supplied. Source: `new:eq:carrier-ibp`. -/
theorem realizedBranchSum_weak_spatialDerivative
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
    (lam : ℝ) (p : ℤ) (es : List (E × P)) (c : P) (v : E)
    (T : JointTransferTerm n P Mat ι → H)
    (hT : ∀ t ∈ jointTransferTerms b es ++ jointTransferTerms b ((v, 0) :: es),
      T t =ᵐ[volume.restrict {x | (x, c) ∈ U}] fun x => WithLp.toLp 2
        (normalizedBranchIntegral b f w₀ α a t lam p (x, c)))
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : ∀ x ∈ tsupport ψ, (x, c) ∈ U) :
    (∫ x, ψ x • (((jointTransferTerms b ((v, 0) :: es)).map T).sum : H) x) =
      - ∫ x, fderiv ℝ ψ x v • (((jointTransferTerms b es).map T).sum : H) x := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r => ℂ)).symm
  have hcompact := normalizedBranchIntegral_weak_spatialDerivative b hU hD hcD hK hKD hf hα
    ha hs hw₀ hcritical hvalue h₀ hinv lam p es c v ψ hψ hψc hψs
  have hvec := congrArg L hcompact
  rw [map_neg, ← L.integral_comp_comm, ← L.integral_comp_comm] at hvec
  simp only [map_smul] at hvec
  have hsum (ds : List (E × P))
      (hds : ∀ t ∈ jointTransferTerms b ds,
        t ∈ jointTransferTerms b es ++ jointTransferTerms b ((v, 0) :: es)) :=
    coe_list_sum_eq_joint (jointTransferTerms b ds) T
      (fun t x => normalizedBranchIntegral b f w₀ α a t lam p (x, c))
      (fun t ht => hT t (hds t ht))
  calc
    _ = ∫ x, ψ x • L (((jointTransferTerms b ((v, 0) :: es)).map fun t =>
        normalizedBranchIntegral b f w₀ α a t lam p (x, c)).sum) :=
      integral_test_smul_congr_ae hψs (hsum ((v, 0) :: es) (fun _ ht => List.mem_append_right _ ht))
    _ = - ∫ x, fderiv ℝ ψ x v • L (((jointTransferTerms b es).map fun t =>
        normalizedBranchIntegral b f w₀ α a t lam p (x, c)).sum) := hvec
    _ = _ := congrArg Neg.neg (integral_test_smul_congr_ae
      ((tsupport_fderiv_apply_subset ℝ v).trans hψs)
      (hsum es (fun _ ht => List.mem_append_left _ ht)).symm)

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
