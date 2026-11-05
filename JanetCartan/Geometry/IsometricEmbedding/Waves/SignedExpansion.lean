module

public import JanetCartan.Analysis.Matrix.HermitianTensor
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The exact ordered signed expansion

This proves the finite-matrix identity `app:ch_pairs:eq:pairs-exact-offself` in
`app:ch_pairs:lem:pairs-ledger` of `paper.tex`. Rows are ambient coordinates and
columns are domain coordinates, as in `HermitianTensor`.

`realWaveMatrixSum b μ dW` is the matrix `dP` obtained by differentiating the
physical combination `P = b √2 ∑ j, √(μ j) Re W_j`, with fixed `b` and `μ`.
The final theorem takes exactly the matrix factorization `dW_j = exp(i θ_j) A_j`;
it imposes no restriction on the amplitudes `A_j` and allows zero weights.

The plus sum contains all ordered pairs, including its doubled-carrier diagonal.
The minus sum ranges over `univ.erase j`, removing precisely its Hermitian self
diagonal. Phases are arbitrary real angles; any physical `2π` factor from the
unit-torus convention is already part of the angle. There are no analytic
estimates or frequency-separation assumptions in these identities.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate
open Matrix

namespace JanetCartan

variable {ι m n : Type*} [Fintype ι] [Fintype m]

/-- The physical weighted real combination in app:ch_pairs:lem:pairs-ledger.
Applied to the derivative matrices `dW_j`, this is `dP`. -/
def realWaveMatrixSum (b : ℝ) (μ : ι → ℝ) (D : ι → Matrix m n ℂ) : Matrix m n ℝ :=
  (b * Real.sqrt 2) • ∑ j, Real.sqrt (μ j) • (D j).map Complex.re

/-- Weighted realification of the quadratic tensor, the first step in the proof
of app:ch_pairs:lem:pairs-ledger. Nonnegative weights may vanish. -/
theorem realWaveMatrixSum_transpose_mul (b : ℝ) (μ : ι → ℝ) (hμ : ∀ j, 0 ≤ μ j)
    (D : ι → Matrix m n ℂ) :
    (realWaveMatrixSum b μ D)ᵀ * realWaveMatrixSum b μ D =
      b ^ 2 • ∑ j, ∑ k, Real.sqrt (μ j * μ k) •
        ((symmetricBilinearTensor (D j) (D k)).map Complex.re +
          (symmetricBilinearTensor (D j) ((D k).map conj)).map Complex.re) := by
  rw [← symmetricBilinearTensor_self]
  simp only [realWaveMatrixSum, symmetricBilinearTensor_smul_left,
    symmetricBilinearTensor_smul_right, symmetricBilinearTensor_sum_left,
    symmetricBilinearTensor_sum_right, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [symmetricBilinearTensor_comm ((D k).map Complex.re)]
  rw [← symmetricBilinearTensor_realification]
  simp only [smul_smul]
  congr 1
  rw [Real.sqrt_mul (hμ j)]
  have hs : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  calc
    _ = (Real.sqrt 2 * Real.sqrt 2) * (b ^ 2 * Real.sqrt (μ j) * Real.sqrt (μ k)) := by
      ring
    _ = _ := by rw [hs]; ring

/-- The phase `exp(i θ)` in app:ch_pairs:lem:pairs-ledger, with `θ` a real angle. -/
def wavePhase (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

/-- Addition of the carrier angles in app:ch_pairs:lem:pairs-ledger. -/
theorem wavePhase_add (θ φ : ℝ) : wavePhase (θ + φ) = wavePhase θ * wavePhase φ := by
  simp [wavePhase, add_mul, Complex.exp_add]

/-- Conjugation reverses the carrier angle in app:ch_pairs:lem:pairs-ledger. -/
theorem wavePhase_conj (θ : ℝ) : conj (wavePhase θ) = wavePhase (-θ) := by
  simp [wavePhase, ← Complex.exp_conj]

/-- The ordered sum-phase tensor `q⁺` of app:ch_pairs:lem:pairs-ledger. -/
def signedPairPlus (θ φ : ℝ) (A B : Matrix m n ℂ) : Matrix n n ℝ :=
  (wavePhase (θ + φ) • symmetricBilinearTensor A B).map Complex.re

/-- The ordered difference-phase tensor `q⁻` of app:ch_pairs:lem:pairs-ledger. -/
def signedPairMinus (θ φ : ℝ) (A B : Matrix m n ℂ) : Matrix n n ℝ :=
  (wavePhase (θ - φ) • symmetricBilinearTensor A (B.map conj)).map Complex.re

/-- Extract the two phases in the plus term of app:ch_pairs:lem:pairs-ledger. -/
theorem signedPairPlus_eq (θ φ : ℝ) (A B : Matrix m n ℂ) :
    signedPairPlus θ φ A B =
      (symmetricBilinearTensor (wavePhase θ • A) (wavePhase φ • B)).map Complex.re := by
  simp [signedPairPlus, wavePhase_add, symmetricBilinearTensor_smul_left,
    symmetricBilinearTensor_smul_right, smul_smul, mul_comm]

/-- Extract the conjugated phase in the minus term of app:ch_pairs:lem:pairs-ledger. -/
theorem signedPairMinus_eq (θ φ : ℝ) (A B : Matrix m n ℂ) :
    signedPairMinus θ φ A B =
      (symmetricBilinearTensor (wavePhase θ • A)
        ((wavePhase φ • B).map conj)).map Complex.re := by
  have hc : (wavePhase φ • B).map conj = wavePhase (-φ) • B.map conj := by
    ext i j
    simp [wavePhase_conj]
  rw [hc, symmetricBilinearTensor_smul_left, symmetricBilinearTensor_smul_right]
  simp [signedPairMinus, sub_eq_add_neg, wavePhase_add, smul_smul]

/-- The minus diagonal is the complete Hermitian tensor in
app:ch_pairs:lem:pairs-ledger, without any restriction on the amplitude. -/
theorem signedPairMinus_self (θ : ℝ) (A : Matrix m n ℂ) :
    signedPairMinus θ θ A A = hermitianTensor A := by
  simp [signedPairMinus, wavePhase, symmetricBilinearTensor_re_conj_self]

/-- The plus diagonal is the doubled carrier retained in
app:ch_pairs:eq:pairs-exact-offself. -/
theorem signedPairPlus_self (θ : ℝ) (A : Matrix m n ℂ) :
    signedPairPlus θ θ A A = (wavePhase (2 * θ) • (Aᵀ * A)).map Complex.re := by
  rw [signedPairPlus, symmetricBilinearTensor_self, two_mul]

/-- The two full ordered sums before removing the Hermitian self tensor in
app:ch_pairs:lem:pairs-ledger. -/
theorem realWaveMatrixSum_signed_expansion (b : ℝ) (μ θ : ι → ℝ)
    (hμ : ∀ j, 0 ≤ μ j) (A : ι → Matrix m n ℂ) :
    (realWaveMatrixSum b μ (fun j ↦ wavePhase (θ j) • A j))ᵀ *
        realWaveMatrixSum b μ (fun j ↦ wavePhase (θ j) • A j) =
      b ^ 2 • ((∑ j, ∑ k, Real.sqrt (μ j * μ k) • signedPairPlus (θ j) (θ k) (A j) (A k)) +
        ∑ j, ∑ k, Real.sqrt (μ j * μ k) • signedPairMinus (θ j) (θ k) (A j) (A k)) := by
  rw [realWaveMatrixSum_transpose_mul b μ hμ]
  simp only [← signedPairPlus_eq, ← signedPairMinus_eq, smul_add, Finset.sum_add_distrib]

/-- The complete self contribution `H_self = b² ∑ j, μ_j Re(A_j* A_j)` of
app:ch_pairs:lem:pairs-ledger. -/
def hermitianSelfSum (b : ℝ) (μ : ι → ℝ) (A : ι → Matrix m n ℂ) : Matrix n n ℝ :=
  b ^ 2 • ∑ j, μ j • hermitianTensor (A j)

variable [DecidableEq ι]

/-- Split precisely the diagonal out of the ordered minus sum in
app:ch_pairs:lem:pairs-ledger. The square-root diagonal equals `μ_j` also at zero. -/
theorem signedPairMinus_sum_split (μ θ : ι → ℝ)
    (hμ : ∀ j, 0 ≤ μ j) (A : ι → Matrix m n ℂ) :
    (∑ j, ∑ k, Real.sqrt (μ j * μ k) • signedPairMinus (θ j) (θ k) (A j) (A k)) =
      (∑ j, ∑ k ∈ Finset.univ.erase j,
        Real.sqrt (μ j * μ k) • signedPairMinus (θ j) (θ k) (A j) (A k)) +
      ∑ j, μ j • hermitianTensor (A j) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hd : Real.sqrt (μ j * μ j) • signedPairMinus (θ j) (θ j) (A j) (A j) =
      μ j • hermitianTensor (A j) := by
    rw [signedPairMinus_self, Real.sqrt_mul_self (hμ j)]
  rw [← hd]
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm

/-- Equation app:ch_pairs:eq:pairs-exact-offself for the explicit phased matrices.
This algebraic form holds for every real scale `b`. Both sums are ordered; the
plus sum includes its diagonal and the minus sum excludes exactly its diagonal. -/
theorem realWaveMatrixSum_offSelf_eq_signedPairs (b : ℝ) (μ θ : ι → ℝ)
    (hμ : ∀ j, 0 ≤ μ j) (A : ι → Matrix m n ℂ) :
    (realWaveMatrixSum b μ (fun j ↦ wavePhase (θ j) • A j))ᵀ *
        realWaveMatrixSum b μ (fun j ↦ wavePhase (θ j) • A j) - hermitianSelfSum b μ A =
      b ^ 2 • ((∑ j, ∑ k, Real.sqrt (μ j * μ k) • signedPairPlus (θ j) (θ k) (A j) (A k)) +
        ∑ j, ∑ k ∈ Finset.univ.erase j,
          Real.sqrt (μ j * μ k) • signedPairMinus (θ j) (θ k) (A j) (A k)) := by
  rw [realWaveMatrixSum_signed_expansion b μ θ hμ, signedPairMinus_sum_split μ θ hμ]
  simp only [hermitianSelfSum, smul_add]
  abel

/-- The exact finite-matrix signed expansion of app:ch_pairs:lem:pairs-ledger,
under the manuscript's `b > 0`, `μ_j ≥ 0`, and `dW_j = exp(i θ_j) A_j` hypotheses.
Here `realWaveMatrixSum b μ dW` is the derivative of the stated physical wave
combination. No signed expansion or self-term cancellation is assumed. -/
theorem signedExpansion_of_derivativeFactorization (b : ℝ) (_hb : 0 < b)
    (μ θ : ι → ℝ) (hμ : ∀ j, 0 ≤ μ j) (dW A : ι → Matrix m n ℂ)
    (hdW : ∀ j, dW j = wavePhase (θ j) • A j) :
    (realWaveMatrixSum b μ dW)ᵀ * realWaveMatrixSum b μ dW - hermitianSelfSum b μ A =
      b ^ 2 • ((∑ j, ∑ k, Real.sqrt (μ j * μ k) • signedPairPlus (θ j) (θ k) (A j) (A k)) +
        ∑ j, ∑ k ∈ Finset.univ.erase j,
          Real.sqrt (μ j * μ k) • signedPairMinus (θ j) (θ k) (A j) (A k)) := by
  have h : dW = fun j ↦ wavePhase (θ j) • A j := funext hdW
  rw [h]
  exact realWaveMatrixSum_offSelf_eq_signedPairs b μ θ hμ A

end JanetCartan
