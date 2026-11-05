module

public import JanetCartan.Iteration.PhysicalPairs.FourierNorm
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.Assembly
public import JanetCartan.Geometry.IsometricEmbedding.Response.SourceExtension.Complex
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.MatrixKernels

/-!
# Actual ambient reconstruction in physical radian Sobolev norm

The reduced solution and complete tensor source are passed through the proved
first-order ambient reconstruction, with zero demodulation phase. This proves
the physical `H^r` conclusion of paper-v2 `main:prop:pairs` from their original
Fourier profiles, without passing the output to a torus. The real Schwartz
field is identified with the literal output formula; no norm of that field is
assumed. The fixed inverse and signed-source producers supply the two input
profiles on the same final sampled family.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open Set MeasureTheory FourierTransform
open scoped ContDiff SchwartzMap Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalPairs

open Pseudodifferential ResponseTransfer IsometricEmbedding.Reconstruction

variable {n N : ℕ}
local notation "E" => Euclidean n
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- The actual reduced Fourier profile produces physical radian size of the
SAME full ambient response, at every order with exactly one carrier power
(`main:prop:pairs`). Constants precede the current map, sources, history, sample
and carrier. No error or output-size estimate is a premise. -/
theorem exists_completedVariation_physicalWeighted_size_constants
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (C B : ℕ → ℝ) (hC : ∀ r, 1 ≤ C r) (hB : ∀ r, 0 ≤ B r) :
    ∃ D : ℕ → ℝ, (∀ r, 0 ≤ D r) ∧
      ∀ (F : E → Euclidean N) (Ω : Set E), IsOpen Ω → tsupport ψ ⊆ Ω →
      ∀ (g : E → EuclideanSpace ℂ (Fin n)) (a : E → Matrix (Fin n) (Fin n) ℂ),
      ContDiff ℝ ∞ g → ContDiff ℝ ∞ a →
      (∀ l j, ContDiffOn ℝ ∞ (reconstructionValueEntry F l j) Ω) →
      (∀ l ij, ContDiffOn ℝ ∞ (reconstructionDerivativeEntry F l ij) Ω) →
      (∀ l ij, ContDiffOn ℝ ∞ (reconstructionSourceEntry F l ij) Ω) →
      ∀ (L lam : ℝ), 1 ≤ L → L ≤ lam →
      (∀ l j r, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r (reconstructionValueEntry F l j) x‖ ≤ C r * L^r) →
      (∀ l ij r, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r (reconstructionDerivativeEntry F l ij) x‖ ≤ C r * L^r) →
      (∀ l ij r, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r (reconstructionSourceEntry F l ij) x‖ ≤ C r * L^r) →
      ∀ (ug : PiLp 2 (fun _ : Fin n ↦ L2)) (ua : PiLp 2 (fun _ : Fin n × Fin n ↦ L2)),
      (∀ j, ug j =ᵐ[volume] fun x ↦ g x j) →
      (∀ ij, ua ij =ᵐ[volume] fun x ↦ a x ij.1 ij.2) →
      (∀ r : ℕ, MemMatrixFourierSobolev (r : ℝ) ug ∧
        matrixFourierSobolevNorm (r : ℝ) ug ≤ B r * lam^r) →
      (∀ r : ℕ, MemMatrixFourierSobolev (r : ℝ) ua ∧
        matrixFourierSobolevNorm (r : ℝ) ua ≤ B r * lam^r) →
      ∀ u : 𝓢(E, Euclidean N),
      (∀ x, u x = ψ x • AmbientResponse.completedVariation F
        (fun y ↦ euclideanRealPart (g y)) (ResponseSourceExtension.tensorFieldRealPart a) x) →
      ∀ r : ℕ,
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight r ((2 * Real.pi) • ξ) •
        𝓕 (PhysicalCutoff.complexify u) ξ) 2 volume).toReal ≤ D r * lam^(r+1) := by
  let ψc : E → ℂ := fun x ↦ (ψ x : ℂ)
  have hψcs : ContDiff ℝ ∞ ψc := Complex.ofRealCLM.contDiff.comp hψ
  have hψcc : HasCompactSupport ψc := hψc.comp_left (g := Complex.ofReal) rfl
  have hbnd (r : ℕ) := (hψcc.iteratedFDeriv r).exists_bound_of_continuous
    (hψcs.continuous_iteratedFDeriv (by simp))
  choose P₀ hP₀ using hbnd
  let P := fun r ↦ max 0 (P₀ r)
  have hP r : 0 ≤ P r := le_max_left _ _
  have hψbound r x : ‖iteratedFDeriv ℝ r ψc x‖ ≤ P r :=
    (hP₀ r x).trans (le_max_right _ _)
  let D := fun r ↦ (2 * Real.pi)^r * max 0
    (reconstructionDisplacementConstant n N (max 1 r) P C B)
  refine ⟨D, fun r ↦ mul_nonneg (by positivity) (le_max_left _ _), ?_⟩
  intro F Ω hΩ hsΩ g a hg ha hV hDer hS L lam hL hLlam
    hVB hDB hSB ug ua hgrep harep hgb hab u hu r
  let k := max 1 r
  have hk : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hrk : (r : ℝ) ≤ k := by exact_mod_cast (le_max_right 1 r)
  have hC₀ j : 0 ≤ C j := zero_le_one.trans (hC j)
  have hχbound j (_hj : j ≤ k+1) x (_hx : x ∈ Ω) :
      ‖iteratedFDeriv ℝ j (fun _ : E ↦ (1 : ℂ)) x‖ ≤ C j * L^j := by
    cases j with
    | zero => simpa using hC 0
    | succ j => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
                exact mul_nonneg (hC₀ _) (pow_nonneg (zero_le_one.trans hL) _)
  have hphase : ∀ i : Fin n, (fun x : E ↦ ((partialDeriv (fun _ : E ↦ (0 : ℝ)) x i : ℝ) : ℂ)) =
      fun _ ↦ 0 := by intro i; funext x; simp [partialDeriv]
  obtain ⟨out, _, houtrep, houtmem, houtbound, _⟩ := completedVariationComplex_graded_envelopes
    k hk (s := (r : ℝ)) (Nat.cast_nonneg _) hrk F hΩ
    (fun _ ↦ 0) (fun _ ↦ 1) ψ g a (differentiable_const 0) hg
    (fun j l ↦ (AmplitudeBound.matrixEntryEvaluation j l).contDiff.comp ha)
    hψcs hψcc
    ((tsupport_comp_subset (g := Complex.ofReal) (by simp) ψ).trans hsΩ)
    contDiffOn_const (fun i ↦ by rw [hphase]; exact contDiffOn_const)
    hV hDer hS P C B hP hC₀ hB (A := 1) (K := lam) (ρ := lam)
    zero_le_one hL hLlam le_rfl
    (fun j _ x _ ↦ (hψbound j x).trans
      (le_mul_of_one_le_right (hP j) (one_le_pow₀ hL)))
    hχbound
    (fun i j _ x _ ↦ by
      rw [hphase]
      cases j with
      | zero => simpa using (mul_nonneg (hC₀ 0) (pow_nonneg (zero_le_one.trans hL) 0))
      | succ j =>
        simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
        exact mul_nonneg (hC₀ _) (pow_nonneg (zero_le_one.trans hL) _))
    (fun l j q _ x hx ↦ hVB l j q x hx)
    (fun l ij q _ x hx ↦ hDB l ij q x hx)
    (fun l ij q _ x hx ↦ hSB l ij q x hx)
    ug ua hgrep harep (hgb _).1 (hab _).1
    (fun p _ ↦ by simpa only [mul_one] using (hgb p).2)
    (fun p _ ↦ by simpa only [mul_one] using (hab p).2)
  let v := fun x ↦ (ψ x : ℂ) • completedVariationComplex F g a x
  have hmod : modulatedWave lam (fun _ : E ↦ 0) g = g := by
    funext x
    simp [modulatedWave, waveCarrier]
  have houtrep' : ∀ l, out l =ᵐ[volume] fun x ↦ v x l := by
    rw [hmod] at houtrep
    simpa only [waveCarrier, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_smul, Complex.ofReal_one] using houtrep
  have hvreal x : u x = euclideanRealPart (v x) := by
    rw [hu]
    apply PiLp.ext
    intro l
    have hgRe : (fun x ↦ euclideanRealPart (g x)) =
        fun y ↦ WithLp.toLp 2 (fun j ↦ (g y j).re) := by
      funext y
      apply PiLp.ext
      intro j
      exact euclideanRealPart_apply _ _
    rw [hgRe]
    symm
    simpa only [v, euclideanRealPart_apply, PiLp.smul_apply,
      smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, ResponseSourceExtension.tensorFieldRealPart,
      LinearMap.coe_mk, AddHom.coe_mk] using
      congrArg (fun z : ℝ ↦ ψ x * z) (completedVariationComplex_re F a
        (hg.differentiable (by simp) x) l)
  apply (physicalWeightedNorm_le_matrix_representative r u v out houtrep' hvreal houtmem).trans
  have hlam : 0 ≤ lam := (zero_le_one.trans hL).trans hLlam
  calc
    _ ≤ (2 * Real.pi)^r * (reconstructionDisplacementConstant n N k P C B * lam * lam^(r : ℝ)) :=
      mul_le_mul_of_nonneg_left (by simpa only [mul_one] using houtbound) (by positivity)
    _ ≤ (2 * Real.pi)^r * (max 0 (reconstructionDisplacementConstant n N k P C B) * lam * lam^(r : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hlam) (Real.rpow_nonneg hlam _))
        (by positivity)
    _ = D r * lam^(r+1) := by
      rw [Real.rpow_natCast, pow_succ]
      dsimp only [D, k]
      ring

end JanetCartan.PhysicalPairs
