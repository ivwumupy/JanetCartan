module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.OutputJets.Grades.Phase
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.OutputJets.Grades.Leibniz
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.OutputJets.Grades.Oscillation

/-!
# Source derivative grades for actual output jets

The binomial convolution of the primitive amplitude and proved oscillation
profiles bounds every ordered output jet. The grade keeps the primitive offset
`b` independent of the source derivative order, as required before integration by parts in
`app:ch_response:thm:response-literal-transfer`. The consumers are
`norm_normalMatrixDerivList_forwardDemodulatedKernel` and
`norm_normalMatrixDerivList_reverseDemodulatedKernel`, followed by
`norm_sourceKernel_le`.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.LowEnvelope

open FourierIntegral NormalComparison

variable {n r : ℕ}

/-- The binomial convolution of the primitive mixed amplitude profile and the
proved oscillation profile for `app:ch_response:thm:response-literal-transfer`.
It depends only on `P`, `C`, output order `m`, and source order `k`, independently
of dimension, positions, physical covector, scales, amplitude size, offset `b`,
and the integration-by-parts order. -/
def outputJetAmplitudeGrade (P : ℕ → ℝ) (C : ℕ → ℕ → ℝ)
    (m k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * outputOscillationGrade P j * C (m - j) k

/-- Nonnegative primitive profiles give a nonnegative output-amplitude profile
for `app:ch_response:thm:response-literal-transfer`. -/
theorem outputJetAmplitudeGrade_nonneg (P : ℕ → ℝ) (C : ℕ → ℕ → ℝ)
    (hP : ∀ j, 0 ≤ P j) (hC : ∀ m k, 0 ≤ C m k) (m k : ℕ) :
    0 ≤ outputJetAmplitudeGrade P C m k := by
  exact Finset.sum_nonneg fun j _ ↦ mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (outputOscillationGrade_nonneg P hP j)) (hC _ k)

/-- Primitive mixed amplitude and phase grades imply the all-order source bound
for the actual output-jet amplitude in
`app:ch_response:thm:response-literal-transfer`. The offset `b` remains unchanged
for every source order `k`; all target derivative costs are absorbed in `R`.
The scalar oscillation bounds are proved from `hτj`, and the Leibniz estimate is
instantiated with the primitive mixed jets `hAj`. This supplies the amplitude
input to `norm_sourceKernel_le` after either demodulated kernel norm identity. -/
theorem norm_iteratedFDeriv_outputJetAmplitude_le
    (τ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (η : Euclidean n) (C : ℕ → ℕ → ℝ) (P : ℕ → ℝ)
    (hC : ∀ m k, 0 ≤ C m k) (hP : ∀ j, 0 ≤ P j)
    {a L R : ℝ} (ha : 0 ≤ a) (hL : 1 ≤ L) (hLR : L ≤ R) (b : ℕ)
    (hτ : ContDiff ℝ ∞ (fun x ↦ τ x η))
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    (hAj : ∀ (β : List (Fin n)) k x y,
      ‖iteratedFDeriv ℝ k (fun z ↦ normalMatrixDerivList β (fun w ↦ A w z η) x) y‖ ≤
        C β.length k * a * L ^ (b + β.length + k))
    (hτj : ∀ j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z ↦ τ z η) x‖ ≤ P j * R * L ^ (j - 1))
    (α : List (Fin n)) (k : ℕ) (x y : Euclidean n) :
    ‖iteratedFDeriv ℝ k (fun z ↦ outputJetAmplitude τ α A x z η) y‖ ≤
      outputJetAmplitudeGrade P C α.length k * a * L ^ (b + k) * R ^ α.length := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hR0 : 0 ≤ R := hL0.trans hLR
  have hjet := norm_iteratedFDeriv_outputJetAmplitude_le_leibniz τ A η hτ hA k
    (fun j ↦ outputOscillationGrade P j * R ^ j)
    (fun m ↦ C m k * a * L ^ (b + m + k))
    (fun j ↦ mul_nonneg (outputOscillationGrade_nonneg P hP j) (pow_nonneg hR0 j))
    (fun m ↦ mul_nonneg (mul_nonneg (hC m k) ha) (pow_nonneg hL0 _))
    (fun β z ↦ norm_euclideanCoordinateDerivList_outputOscillation_le τ η P hP hL hLR
      hτ hτj β z) (fun β z w ↦ hAj β k z w) α x y
  refine hjet.trans ?_
  unfold outputJetAmplitudeGrade
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjm : j ≤ α.length := by
    have := Finset.mem_range.mp hj
    omega
  have hp : L ^ (b + (α.length - j) + k) = L ^ (b + k) * L ^ (α.length - j) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = ((α.length.choose j : ℝ) * outputOscillationGrade P j * C (α.length - j) k *
        a * L ^ (b + k)) * (R ^ j * L ^ (α.length - j)) := by
      rw [hp]
      ring
    _ ≤ ((α.length.choose j : ℝ) * outputOscillationGrade P j * C (α.length - j) k *
        a * L ^ (b + k)) * (R ^ j * R ^ (α.length - j)) := by
      apply mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hLR _) (pow_nonneg hR0 _))
      exact mul_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (outputOscillationGrade_nonneg P hP j))
        (hC _ k)) ha) (pow_nonneg hL0 _)
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le hjm]

/-- Forward output-jet grades from the primitive jets of `S`, `φ`, and the full
amplitude, at `R = ρ + ‖η‖`, for
`app:ch_response:thm:response-literal-transfer`. This instantiates every phase
premise in the amplitude estimate consumed by
`norm_normalMatrixDerivList_forwardDemodulatedKernel`. -/
theorem norm_iteratedFDeriv_forwardOutputJetAmplitude_le
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (η : Euclidean n)
    (C : ℕ → ℕ → ℝ) (PS Pφ : ℕ → ℝ)
    (hC : ∀ m k, 0 ≤ C m k) (hPS : ∀ j, 0 ≤ PS j) (hPφ : ∀ j, 0 ≤ Pφ j)
    {a L ρ : ℝ} (ha : 0 ≤ a) (hL : 1 ≤ L) (hρ : 0 ≤ ρ)
    (hLR : L ≤ ρ + ‖η‖) (b : ℕ)
    (hS : ContDiff ℝ ∞ (fun x ↦ S x η)) (hφ : ContDiff ℝ ∞ φ)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    (hAj : ∀ (β : List (Fin n)) k x y,
      ‖iteratedFDeriv ℝ k (fun z ↦ normalMatrixDerivList β (fun w ↦ A w z η) x) y‖ ≤
        C β.length k * a * L ^ (b + β.length + k))
    (hSj : ∀ j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z ↦ S z η) x‖ ≤ PS j * ‖η‖ * L ^ (j - 1))
    (hφj : ∀ j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j φ x‖ ≤ Pφ j * L ^ (j - 1))
    (α : List (Fin n)) (k : ℕ) (x y : Euclidean n) :
    ‖iteratedFDeriv ℝ k
      (fun z ↦ outputJetAmplitude (forwardTargetPhase S φ ρ) α A x z η) y‖ ≤
      outputJetAmplitudeGrade (fun j ↦ PS j + Pφ j) C α.length k *
        a * L ^ (b + k) * (ρ + ‖η‖) ^ α.length := by
  apply norm_iteratedFDeriv_outputJetAmplitude_le (forwardTargetPhase S φ ρ) A η C
    (fun j ↦ PS j + Pφ j) hC (fun j ↦ add_nonneg (hPS j) (hPφ j)) ha hL hLR b
    (hS.sub (contDiff_const.mul hφ)) hA hAj
  intro j hj z
  exact norm_iteratedFDeriv_forwardTargetPhase_le S φ η z hρ (zero_le_one.trans hL)
    PS Pφ hPS hPφ hS hφ (fun j hj ↦ hSj j hj z) (fun j hj ↦ hφj j hj z) j hj

/-- Reverse output-jet grades from a fixed carrier bound and primitive full
amplitude jets, at `R = ρ + ‖η‖`, for
`app:ch_response:thm:response-literal-transfer`. Here `y` is the target and `x`
is the source; both positions and the physical covector remain explicit.
This supplies the amplitude grade for
`norm_normalMatrixDerivList_reverseDemodulatedKernel`. -/
theorem norm_iteratedFDeriv_reverseOutputJetAmplitude_le
    (ζ : Euclidean n) (A : FullAmplitude n r) (η : Euclidean n)
    (C : ℕ → ℕ → ℝ) (hC : ∀ m k, 0 ≤ C m k)
    {a L ρ Z : ℝ} (ha : 0 ≤ a) (hL : 1 ≤ L) (hρ : 0 ≤ ρ)
    (hLR : L ≤ ρ + ‖η‖) (hζ : ‖ζ‖ ≤ Z) (b : ℕ)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    (hAj : ∀ (β : List (Fin n)) k y x,
      ‖iteratedFDeriv ℝ k (fun z ↦ normalMatrixDerivList β (fun w ↦ A w z η) y) x‖ ≤
        C β.length k * a * L ^ (b + β.length + k))
    (α : List (Fin n)) (k : ℕ) (y x : Euclidean n) :
    ‖iteratedFDeriv ℝ k
      (fun z ↦ outputJetAmplitude (reverseTargetPhase ζ ρ) α A y z η) x‖ ≤
      outputJetAmplitudeGrade (fun _ ↦ 1 + Z) C α.length k *
        a * L ^ (b + k) * (ρ + ‖η‖) ^ α.length := by
  have hZ : 0 ≤ Z := (norm_nonneg ζ).trans hζ
  apply norm_iteratedFDeriv_outputJetAmplitude_le (reverseTargetPhase ζ ρ) A η C
    (fun _ ↦ 1 + Z) hC (fun _ ↦ add_nonneg zero_le_one hZ) ha hL hLR b
    (contDiff_id.inner ℝ contDiff_const) hA hAj
  intro j hj z
  exact norm_iteratedFDeriv_reverseTargetPhase_le ζ z η hρ (zero_le_one.trans hL) hζ j hj

/-- The zeroth output jet preserves every primitive source grade, with the same
fixed offset, for `app:ch_response:thm:response-literal-transfer`. -/
theorem norm_iteratedFDeriv_outputJetAmplitude_nil_le
    (τ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (x y η : Euclidean n) (C : ℕ → ℕ → ℝ) (a L : ℝ) (b k : ℕ)
    (hA : ‖iteratedFDeriv ℝ k (fun z ↦ A x z η) y‖ ≤ C 0 k * a * L ^ (b + k)) :
    ‖iteratedFDeriv ℝ k (fun z ↦ outputJetAmplitude τ [] A x z η) y‖ ≤
      C 0 k * a * L ^ (b + k) := by
  simpa only [outputJetAmplitude_nil] using hA

/-- The first output jet has profile `C 1 k + P 1 * C 0 k`. This proves the
source-order-independent offset directly from the primitive mixed jets, without
assuming any grade on the modified amplitude
(`app:ch_response:thm:response-literal-transfer`). -/
theorem norm_iteratedFDeriv_outputJetAmplitude_singleton_le
    (τ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (η : Euclidean n) (C : ℕ → ℕ → ℝ) (P : ℕ → ℝ)
    (hC : ∀ m k, 0 ≤ C m k) (hP : ∀ j, 0 ≤ P j)
    {a L R : ℝ} (ha : 0 ≤ a) (hL : 1 ≤ L) (hLR : L ≤ R) (b : ℕ)
    (hτ : ContDiff ℝ ∞ (fun x ↦ τ x η))
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    (hAj : ∀ (β : List (Fin n)) k x y,
      ‖iteratedFDeriv ℝ k (fun z ↦ normalMatrixDerivList β (fun w ↦ A w z η) x) y‖ ≤
        C β.length k * a * L ^ (b + β.length + k))
    (hτj : ∀ j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z ↦ τ z η) x‖ ≤ P j * R * L ^ (j - 1))
    (i : Fin n) (k : ℕ) (x y : Euclidean n) :
    ‖iteratedFDeriv ℝ k (fun z ↦ outputJetAmplitude τ [i] A x z η) y‖ ≤
      (C 1 k + P 1 * C 0 k) * a * L ^ (b + k) * R := by
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hR0 : 0 ≤ R := hL0.trans hLR
  let c : ℂ := (fderiv ℝ (fun z ↦ τ z η) x (EuclideanSpace.single i 1) : ℝ) * Complex.I
  have hc : ‖c‖ ≤ P 1 * R := by
    calc
      ‖c‖ = ‖fderiv ℝ (fun z ↦ τ z η) x (EuclideanSpace.single i 1)‖ := by
        simp [c]
      _ ≤ ‖fderiv ℝ (fun z ↦ τ z η) x‖ := by
        simpa [EuclideanSpace.single, PiLp.norm_single] using
          (fderiv ℝ (fun z ↦ τ z η) x).le_opNorm (EuclideanSpace.single i 1)
      _ ≤ P 1 * R := by simpa [norm_iteratedFDeriv_one] using hτj 1 le_rfl x
  have hs (β : List (Fin n)) : ContDiff ℝ ∞
      (fun z ↦ normalMatrixDerivList β (fun w ↦ A w z η) x) := by
    exact (contDiff_joint_normalMatrixDerivList (f := fun w z ↦ A w z η) hA β).comp
      (contDiff_const.prodMk contDiff_id)
  have hs0 : ContDiff ℝ ∞ (fun z ↦ A x z η) := hs []
  have he : (fun z ↦ outputJetAmplitude τ [i] A x z η) =
      fun z ↦ normalMatrixDerivList [i] (fun w ↦ A w z η) x + c • A x z η := by
    funext z
    exact outputJetAmplitude_singleton τ A i x z η hτ
      (hA.comp (contDiff_id.prodMk contDiff_const))
  rw [he]
  change ‖iteratedFDeriv ℝ k ((fun z ↦ normalMatrixDerivList [i] (fun w ↦ A w z η) x) +
    (fun z ↦ c • A x z η)) y‖ ≤ _
  rw [iteratedFDeriv_add_apply (i := k) (x := y) ((hs [i]).contDiffAt.of_le (by simp))
    ((hs0.const_smul c).contDiffAt.of_le (by simp)),
    iteratedFDeriv_const_smul_apply' (hs0.contDiffAt.of_le (by simp))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k
        (fun z ↦ normalMatrixDerivList [i] (fun w ↦ A w z η) x) y‖ +
        ‖c‖ * ‖iteratedFDeriv ℝ k (fun z ↦ A x z η) y‖ := by
      simpa only [norm_smul] using norm_add_le
        (iteratedFDeriv ℝ k (fun z ↦ normalMatrixDerivList [i] (fun w ↦ A w z η) x) y)
        (c • iteratedFDeriv ℝ k (fun z ↦ A x z η) y)
    _ ≤ C 1 k * a * L ^ (b + 1 + k) + P 1 * R * (C 0 k * a * L ^ (b + k)) := by
      apply add_le_add (by simpa using hAj [i] k x y)
      exact mul_le_mul hc (by simpa [normalMatrixDerivList] using hAj [] k x y)
        (norm_nonneg _) (mul_nonneg (hP 1) hR0)
    _ ≤ (C 1 k + P 1 * C 0 k) * a * L ^ (b + k) * R := by
      have hp : L ^ (b + 1 + k) = L ^ (b + k) * L := by
        rw [show b + 1 + k = (b + k) + 1 by omega, pow_succ]
      rw [hp]
      have hh := mul_le_mul_of_nonneg_left hLR
        (mul_nonneg (mul_nonneg (hC 1 k) ha) (pow_nonneg hL0 (b + k)))
      nlinarith

end JanetCartan.ResponseTransfer.LowEnvelope
