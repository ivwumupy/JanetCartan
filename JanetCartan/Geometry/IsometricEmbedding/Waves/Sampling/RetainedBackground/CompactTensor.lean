module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.CompactTensor.Family
public import JanetCartan.Analysis.Fourier.SeparatedSampling.Geometry
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.AffinePullback

/-!
# Classical retained tensors as smooth L2 carrier families

This is the classical-to-L2 deduction for `app:ch_waves:eq:background-quadrature`.
The producer is the retained carrier pullback of
`exists_retained_supportedBackground_budgets`. The input consists only of joint
classical smoothness, common compact physical support, and classical jet bounds.
The original `SeparatedSampling.Point` carrier and physical volume are retained.
Actual construction and instantiation remain with the retained-background parent.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.RetainedBackground
open SeparatedSampling CompactTensor
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets

variable {n : ℕ} {J : Set (Euclidean n)} (hJ : IsCompact J)
variable {H : ℝ → Point → Euclidean n → Matrix (Fin n) (Fin n) ℝ}
variable (hH : ContDiff ℝ ∞ (fun q : ℝ × (Point × Euclidean n) ↦ H q.1 q.2.1 q.2.2))
variable (hS : ∀ τ z x, x ∉ J → H τ z x = 0)

include hH in
/-- Reassociation of the classical variables for the generic compact-family
calculus (`app:ch_waves:eq:background-quadrature`). -/
theorem contDiff_uncurry_background : ContDiff ℝ ∞
    (Function.uncurry (fun a : ℝ × Point ↦ H a.1 a.2)) :=
  hH.comp ((contDiff_fst.fst).prodMk (contDiff_fst.snd.prodMk contDiff_snd))

/-- The original retained tensor defines a literal physical L2 class, jointly
in the radial and carrier variables (`app:ch_waves:eq:background-quadrature`). -/
def backgroundL2 (a : ℝ × Point) :
    Lp (Matrix (Fin n) (Fin n) ℝ) 2 (volume : Measure (Euclidean n)) :=
  family hJ (contDiff_uncurry_background hH) (fun a ↦ hS a.1 a.2) a

/-- The constructed class represents exactly the classical retained tensor
(`app:ch_waves:eq:background-quadrature`). -/
theorem backgroundL2_ae (τ : ℝ) (z : Point) :
    backgroundL2 hJ hH hS (τ, z) =ᵐ[volume] H τ z :=
  family_ae hJ (contDiff_uncurry_background hH) (fun a ↦ hS a.1 a.2) (τ, z)

/-- Joint radial/carrier L2 smoothness is deduced from the classical input
(`app:ch_waves:eq:background-quadrature`). -/
theorem contDiff_backgroundL2 (k : ℕ) :
    ContDiff ℝ k (backgroundL2 hJ hH hS) :=
  contDiff_family hJ (contDiff_uncurry_background hH) (fun a ↦ hS a.1 a.2) k

/-- The literal tensor is jointly infinitely differentiable as an L2 family
(`app:ch_waves:eq:background-quadrature`). -/
theorem contDiff_infty_backgroundL2 : ContDiff ℝ ∞ (backgroundL2 hJ hH hS) :=
  contDiff_infty.mpr (contDiff_backgroundL2 hJ hH hS)

/-- Every evaluated joint L2 derivative is the class of the actual classical
joint parameter derivative (`app:ch_waves:eq:background-quadrature`). -/
theorem iteratedFDeriv_backgroundL2 (k : ℕ) (v : Fin k → ℝ × Point) (a : ℝ × Point) :
    iteratedFDeriv ℝ k (backgroundL2 hJ hH hS) a v =
      (iteratedParameterDeriv_memLp hJ (contDiff_uncurry_background hH)
        (fun a ↦ hS a.1 a.2) k v a).toLp
        (fun x ↦ iteratedFDeriv ℝ k (fun b : ℝ × Point ↦ H b.1 b.2 x) a v) :=
  iteratedFDeriv_family hJ (contDiff_uncurry_background hH) (fun a ↦ hS a.1 a.2) k v a

/-- A classical tensor bound on the fixed support controls its L2 norm, with
no carrier-dependent constant (`app:ch_waves:eq:background-quadrature`). -/
theorem norm_backgroundL2_le (τ : ℝ) (z : Point) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x ∈ J, ‖H τ z x‖ ≤ B) :
    ‖backgroundL2 hJ hH hS (τ, z)‖ ≤ physicalL2Constant hJ * B :=
  norm_family_le hJ (contDiff_uncurry_background hH) (fun a ↦ hS a.1 a.2) (τ, z) hB hb

variable {ψ : Point → ℝ} (hψ : ContDiff ℝ ∞ ψ)

include hH hψ in
private lemma weighted_slice_smooth (τ : ℝ) : ContDiff ℝ ∞
    (Function.uncurry (fun z x ↦ ψ z • H τ z x)) :=
  (hψ.comp contDiff_fst).smul (hH.comp (contDiff_const.prodMk contDiff_id))

include hS in
private lemma weighted_slice_support (τ : ℝ) :
    ∀ z x, x ∉ J → ψ z • H τ z x = 0 := by
  intro z x hx
  rw [hS τ z x hx, smul_zero]

private lemma weighted_family_eq (τ : ℝ) :
    family hJ (weighted_slice_smooth hH hψ τ) (weighted_slice_support hS τ) =
      (fun z ↦ ψ z • backgroundL2 hJ hH hS (τ, z)) := by
  funext z
  apply Lp.ext
  filter_upwards [family_ae hJ (weighted_slice_smooth hH hψ τ)
    (weighted_slice_support hS τ) z, backgroundL2_ae hJ hH hS τ z,
    Lp.coeFn_smul (ψ z) (backgroundL2 hJ hH hS (τ, z))] with x hx hy hz
  simp only [hx, hz, Pi.smul_apply, hy]

include hψ in
/-- The weighted carrier function used by Taylor quadrature is smooth in L2
(`app:ch_waves:eq:background-quadrature`). -/
theorem contDiff_weighted_backgroundL2 (τ : ℝ) (k : ℕ) :
    ContDiff ℝ k (fun z ↦ ψ z • backgroundL2 hJ hH hS (τ, z)) := by
  rw [← weighted_family_eq hJ hH hS hψ τ]
  exact contDiff_family hJ (weighted_slice_smooth hH hψ τ) (weighted_slice_support hS τ) k

include hH hψ in
private lemma norm_carrier_jet_le_joint (τ : ℝ) (z : Point) (x : Euclidean n) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z ↦ ψ z • H τ z x) z‖ ≤
      ‖iteratedFDeriv ℝ k
        (fun q : ℝ × (Point × Euclidean n) ↦ ψ q.2.1 • H q.1 q.2.1 q.2.2)
        (τ, (z, x))‖ := by
  let T : Point →L[ℝ] ℝ × (Point × Euclidean n) :=
    (0 : Point →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ Point).prod 0)
  have hT : ‖T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simp [T, Prod.norm_def]
  have hsmooth : ContDiff ℝ ∞
      (fun q : ℝ × (Point × Euclidean n) ↦ ψ q.2.1 • H q.1 q.2.1 q.2.2) :=
    (hψ.comp contDiff_snd.fst).smul hH
  have hh := norm_iteratedFDeriv_preAffine_le T (τ, (0, x)) isOpen_univ
    hsmooth.contDiffOn (x := z) (mem_univ _) k
  have he : (fun y ↦ ψ (T y + (τ, (0, x))).2.1 •
      H (T y + (τ, (0, x))).1 (T y + (τ, (0, x))).2.1
        (T y + (τ, (0, x))).2.2) = (fun y ↦ ψ y • H τ y x) := by
    funext y
    simp [T]
  rw [he] at hh
  apply hh.trans
  convert mul_le_of_le_one_right
    (norm_nonneg (iteratedFDeriv ℝ k
      (fun q : ℝ × (Point × Euclidean n) ↦ ψ q.2.1 • H q.1 q.2.1 q.2.2)
        (T z + (τ, (0, x))))) (pow_le_one₀ (norm_nonneg T) hT) using 1; simp [T]

include hψ in
/-- The original joint classical jet budget implies the L2 carrier derivative
budget. No L2 estimate is an input. The power is the manuscript's natural
truncated exponent (`app:ch_waves:eq:background-quadrature`). -/
theorem norm_iteratedFDeriv_weighted_backgroundL2_le
    {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) {L : ℝ} (hL : 1 ≤ L) {rpar : ℕ}
    (hjet : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z x j,
      ‖iteratedFDeriv ℝ j
        (fun q : ℝ × (Point × Euclidean n) ↦ ψ q.2.1 • H q.1 q.2.1 q.2.2)
        (τ, (z, x))‖ ≤ A j * L ^ (j - rpar))
    {τ : ℝ} (hτ : τ ∈ Icc (-1 : ℝ) 1) (z : Point) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z ↦ ψ z • backgroundL2 hJ hH hS (τ, z)) z‖ ≤
      physicalL2Constant hJ * (A k * L ^ (k - rpar)) := by
  rw [← weighted_family_eq hJ hH hS hψ τ]
  apply norm_iteratedFDeriv_family_le hJ (weighted_slice_smooth hH hψ τ)
    (weighted_slice_support hS τ) k z (mul_nonneg (hA k) (pow_nonneg (by linarith) _))
  intro x _
  exact (norm_carrier_jet_le_joint hH hψ τ z x k).trans (hjet τ hτ z x k)

include hψ in
/-- Below the parameter reserve, the carrier derivative bound is independent
of frequency and of `L`; it is the constant needed by deterministic quadrature
(`app:ch_waves:eq:background-quadrature`). -/
theorem norm_iteratedFDeriv_weighted_backgroundL2_le_of_le
    {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) {L : ℝ} (hL : 1 ≤ L) {rpar : ℕ}
    (hjet : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z x j,
      ‖iteratedFDeriv ℝ j
        (fun q : ℝ × (Point × Euclidean n) ↦ ψ q.2.1 • H q.1 q.2.1 q.2.2)
        (τ, (z, x))‖ ≤ A j * L ^ (j - rpar))
    {τ : ℝ} (hτ : τ ∈ Icc (-1 : ℝ) 1) (z : Point) {p : ℕ} (hp : p ≤ rpar) :
    ‖iteratedFDeriv ℝ p (fun z ↦ ψ z • backgroundL2 hJ hH hS (τ, z)) z‖ ≤
      physicalL2Constant hJ * A p := by
  simpa only [Nat.sub_eq_zero_of_le hp, pow_zero, mul_one] using
    norm_iteratedFDeriv_weighted_backgroundL2_le hJ hH hS hψ hA hL hjet hτ z p

end JanetCartan.Sampling.RetainedBackground
