module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Basic
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.AmplitudeGrades.Products

/-!
# Primitive product grades for the full graph amplitude

The consumer is the pointwise graph kernel estimate in
`app:ch_regular:eq:chain-tail`. Profiles are chosen independently of the
frequency and integration order. The hypotheses bound the five primitive
factors, never the composed or transferred amplitude. Both positions of the
full matrix symbol remain present, with the Frobenius norm.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelEstimates
open FourierIntegral Retarded.KernelDecay

/-- Primitive profiles and fixed grade offsets for the five factors of
`jointAmplitude` (`app:ch_regular:eq:high-amplitude`). -/
structure AmplitudeProfiles where
  symbol : ℕ → ℝ
  graphCutoff : ℕ → ℝ
  outputCutoff : ℕ → ℝ
  inputMask : ℕ → ℝ
  outputMask : ℕ → ℝ
  symbol_nonneg : ∀ j, 0 ≤ symbol j
  graphCutoff_nonneg : ∀ j, 0 ≤ graphCutoff j
  outputCutoff_nonneg : ∀ j, 0 ≤ outputCutoff j
  inputMask_nonneg : ∀ j, 0 ≤ inputMask j
  outputMask_nonneg : ∀ j, 0 ≤ outputMask j
  symbolOffset : ℕ
  graphCutoffOffset : ℕ
  outputCutoffOffset : ℕ
  inputMaskOffset : ℕ
  outputMaskOffset : ℕ

/-- The product offset adds each primitive loss exactly once; in particular
it does not depend on the integration order (`app:ch_regular:eq:chain-tail`). -/
def AmplitudeProfiles.offset (D : AmplitudeProfiles) : ℕ :=
  ((D.graphCutoffOffset + D.outputCutoffOffset) + D.outputMaskOffset) +
    D.inputMaskOffset + D.symbolOffset

/-- Explicit Leibniz convolution for all five factors, including the identity
in the complementary output mask (`app:ch_regular:eq:chain-tail`). -/
def AmplitudeProfiles.productProfile (D : AmplitudeProfiles) : ℕ → ℝ :=
  derivativeConvolution
    (derivativeConvolution
      (derivativeConvolution (derivativeConvolution D.graphCutoff D.outputCutoff)
        (fun j => 1 + D.outputMask j)) D.inputMask) D.symbol

/-- Nonnegative constants for the vector integration-by-parts estimate
(`app:ch_regular:eq:chain-tail`). -/
theorem AmplitudeProfiles.productProfile_nonneg (D : AmplitudeProfiles) (j : ℕ) :
    0 ≤ D.productProfile j :=
  derivativeConvolution_nonneg
    (fun _ => derivativeConvolution_nonneg
      (fun _ => derivativeConvolution_nonneg
        (derivativeConvolution_nonneg D.graphCutoff_nonneg D.outputCutoff_nonneg)
        (fun j => by linarith [D.outputMask_nonneg j]) _)
      D.inputMask_nonneg _) D.symbol_nonneg j

variable {n r : ℕ}

/-- Primitive normalized full-symbol and cutoff grades. The symbol is evaluated
at the physical covector `ρ • ξ`, retaining both positions. These assumptions
hold only on the carrier `K`, so positive and negative symbol orders need no
false global frequency bound. They are supplied by the full symbol grades and buffered localizer construction
in the parent graph factor proof (`app:ch_regular:eq:high-amplitude`). -/
structure HasAmplitudeGrades (D : AmplitudeProfiles) (ρ S L : ℝ)
    (A : FullAmplitude n r) (mi mo : LocalizerSymbol n)
    (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    (K : Set (JointVariables (Euclidean n)) := Set.univ) : Prop where
  symbol_smooth : ContDiff ℝ ∞ (fun p : JointVariables (Euclidean n) =>
    A p.1.1 p.1.2 (ρ • p.2.1))
  graphCutoff_smooth : ContDiff ℝ ∞ (fun p : JointVariables (Euclidean n) =>
    (χA (ρ • p.2.1) : ℂ))
  outputCutoff_smooth : ContDiff ℝ ∞ (fun p : JointVariables (Euclidean n) =>
    (χo (ρ • p.2.2.2) : ℂ))
  inputMask_smooth : ContDiff ℝ ∞ (fun p : JointVariables (Euclidean n) =>
    (mi (y, p.2.2.1) : ℂ))
  outputMask_smooth : ContDiff ℝ ∞ (fun p : JointVariables (Euclidean n) =>
    (mo (x, p.2.2.2) : ℂ))
  symbol_bound : ∀ j p, p ∈ K → ‖iteratedFDeriv ℝ j (fun p : JointVariables (Euclidean n) =>
    A p.1.1 p.1.2 (ρ • p.2.1)) p‖ ≤ S * D.symbol j * L ^ (j + D.symbolOffset)
  graphCutoff_bound : ∀ j p, p ∈ K → ‖iteratedFDeriv ℝ j
    (fun p : JointVariables (Euclidean n) => (χA (ρ • p.2.1) : ℂ)) p‖ ≤
      D.graphCutoff j * L ^ (j + D.graphCutoffOffset)
  outputCutoff_bound : ∀ j p, p ∈ K → ‖iteratedFDeriv ℝ j
    (fun p : JointVariables (Euclidean n) => (χo (ρ • p.2.2.2) : ℂ)) p‖ ≤
      D.outputCutoff j * L ^ (j + D.outputCutoffOffset)
  inputMask_bound : ∀ j p, p ∈ K → ‖iteratedFDeriv ℝ j
    (fun p : JointVariables (Euclidean n) => (mi (y, p.2.2.1) : ℂ)) p‖ ≤
      D.inputMask j * L ^ (j + D.inputMaskOffset)
  outputMask_bound : ∀ j p, p ∈ K → ‖iteratedFDeriv ℝ j
    (fun p : JointVariables (Euclidean n) => (mo (x, p.2.2.2) : ℂ)) p‖ ≤
      D.outputMask j * L ^ (j + D.outputMaskOffset)

/-- Scalar multiplication by the full matrix symbol adds the two fixed grade
offsets once. This is shared by the amplitude product and output-jet grade
estimates (`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_smul_le_amplitude_grades {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    {f : V → ℂ} {g : V → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {C B : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j) {S L : ℝ} (hL : 0 ≤ L)
    (a b : ℕ) (x : V)
    (ha : ∀ j, ‖iteratedFDeriv ℝ j f x‖ ≤ C j * L ^ (j + a))
    (hb : ∀ j, ‖iteratedFDeriv ℝ j g x‖ ≤ S * B j * L ^ (j + b)) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => f y • g y) x‖ ≤
      S * derivativeConvolution C B k * L ^ (k + (a + b)) := by
  apply (norm_iteratedFDeriv_smul_le hf hg x (show (k : ℕ∞ω) ≤ ∞ by simp)).trans
  simp only [derivativeConvolution, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  calc
    _ ≤ (k.choose j : ℝ) * (C j * L ^ (j + a)) *
        (S * B (k - j) * L ^ (k - j + b)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (ha j) (Nat.cast_nonneg _))
        (hb _) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC j) (pow_nonneg hL _)))
    _ = S * ((k.choose j : ℝ) * C j * B (k - j)) *
        (L ^ (j + a) * L ^ (k - j + b)) := by ring
    _ = _ := by rw [← pow_add]; congr 2; omega

private theorem jointAmplitude_eq_product (ρ : ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (x y : Euclidean n) :
    jointAmplitude ρ A mi mo χA χo x y = fun p =>
      ((χA (ρ • p.2.1) : ℂ) * (χo (ρ • p.2.2.2) : ℂ) *
        (1 - (mo (x, p.2.2.2) : ℂ)) * (mi (y, p.2.2.1) : ℂ)) •
      A p.1.1 p.1.2 (ρ • p.2.1) := by
  funext p
  simp [jointAmplitude]

/-- Smoothness of the literal product follows from primitive smoothness
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem HasAmplitudeGrades.contDiff_jointAmplitude {D : AmplitudeProfiles} {ρ S L : ℝ}
    {A : FullAmplitude n r} {mi mo : LocalizerSymbol n}
    {χA χo : Euclidean n → ℝ} {x y : Euclidean n}
    {K : Set (JointVariables (Euclidean n))}
    (h : HasAmplitudeGrades D ρ S L A mi mo χA χo x y K) :
    ContDiff ℝ ∞ (jointAmplitude ρ A mi mo χA χo x y) := by
  rw [jointAmplitude_eq_product]
  convert (((h.graphCutoff_smooth.mul h.outputCutoff_smooth).mul
    ((contDiff_const (c := (1 : ℂ))).sub h.outputMask_smooth)).mul
      h.inputMask_smooth).smul h.symbol_smooth using 1

/-- Full product grades are derived by Leibniz from the five primitive inputs.
No transferred-amplitude estimate is assumed. The sole frequency factor `S`
may be a positive or negative real symbol power (`app:ch_regular:eq:chain-tail`). -/
theorem HasAmplitudeGrades.norm_iteratedFDeriv_jointAmplitude_le
    {D : AmplitudeProfiles} {ρ S L : ℝ} {A : FullAmplitude n r}
    {mi mo : LocalizerSymbol n} {χA χo : Euclidean n → ℝ} {x y : Euclidean n}
    {K : Set (JointVariables (Euclidean n))}
    (h : HasAmplitudeGrades D ρ S L A mi mo χA χo x y K) (hL : 1 ≤ L)
    (p : JointVariables (Euclidean n)) (hp : p ∈ K) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (jointAmplitude ρ A mi mo χA χo x y) p‖ ≤
      S * D.productProfile k * L ^ (k + D.offset) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hco j : 0 ≤ 1 + D.outputMask j := by linarith [D.outputMask_nonneg j]
  have ho k := norm_iteratedFDeriv_one_sub_le_grades h.outputMask_smooth
    (S := 1) le_rfl hL D.outputMaskOffset p
    (fun j => by simpa using h.outputMask_bound j p hp) k
  have hgo k := norm_iteratedFDeriv_mul_le_grades h.graphCutoff_smooth h.outputCutoff_smooth
    D.graphCutoff_nonneg D.outputCutoff_nonneg (S := 1) (T := 1)
    zero_le_one zero_le_one hL0 D.graphCutoffOffset D.outputCutoffOffset p
    (fun j => by simpa using h.graphCutoff_bound j p hp)
    (fun j => by simpa using h.outputCutoff_bound j p hp) k
  have hgo' := derivativeConvolution_nonneg D.graphCutoff_nonneg D.outputCutoff_nonneg
  have hcomp k := norm_iteratedFDeriv_mul_le_grades
    (h.graphCutoff_smooth.mul h.outputCutoff_smooth)
    ((contDiff_const (c := (1 : ℂ))).sub h.outputMask_smooth) hgo' hco (S := 1) (T := 1)
    zero_le_one zero_le_one hL0 (D.graphCutoffOffset + D.outputCutoffOffset)
    D.outputMaskOffset p (fun j => by simpa using hgo j) ho k
  have hcomp' := derivativeConvolution_nonneg hgo' hco
  have hmask k := norm_iteratedFDeriv_mul_le_grades
    ((h.graphCutoff_smooth.mul h.outputCutoff_smooth).mul
      ((contDiff_const (c := (1 : ℂ))).sub h.outputMask_smooth)) h.inputMask_smooth
    hcomp' D.inputMask_nonneg (S := 1) (T := 1) zero_le_one zero_le_one hL0
    ((D.graphCutoffOffset + D.outputCutoffOffset) + D.outputMaskOffset)
    D.inputMaskOffset p (fun j => by simpa using hcomp j)
    (fun j => by simpa using h.inputMask_bound j p hp) k
  have hf := norm_iteratedFDeriv_smul_le_amplitude_grades
    (((h.graphCutoff_smooth.mul h.outputCutoff_smooth).mul
      ((contDiff_const (c := (1 : ℂ))).sub h.outputMask_smooth)).mul h.inputMask_smooth) h.symbol_smooth
    (derivativeConvolution_nonneg hcomp' D.inputMask_nonneg) hL0
    (((D.graphCutoffOffset + D.outputCutoffOffset) + D.outputMaskOffset) + D.inputMaskOffset)
    D.symbolOffset p (fun j => by simpa using hmask j) (fun j => h.symbol_bound j p hp) k
  simpa only [jointAmplitude_eq_product,
    AmplitudeProfiles.productProfile, AmplitudeProfiles.offset] using hf

end JanetCartan.FiniteChain.Graph.KernelEstimates
