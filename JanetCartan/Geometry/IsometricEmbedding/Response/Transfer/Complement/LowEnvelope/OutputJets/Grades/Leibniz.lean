module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.OutputJets.Basic
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.Amplitude
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Mixed ordered Leibniz bounds for output jets

The source derivative estimate in `app:ch_response:thm:response-literal-transfer`
is proved from the ordered scalar target jets and the primitive mixed amplitude
jets. Both physical positions and the fixed physical frequency are retained.

The exact ordered product recursion gives the binomial convolution at arbitrary
output order. The consumer in `OutputJets.Grades` supplies the oscillation profile
`G` from phase bounds and the profile `H` from primitive mixed amplitude bounds;
no estimate on a modified amplitude is an input here.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.LowEnvelope

open FourierIntegral NormalComparison AmplitudeBound JanetCartan.Localization

variable {n r : ℕ}

/-- Concatenation composes ordered target jets, with the outer derivatives first.
Used by `normalMatrixDerivList_snoc_smul` for
`app:ch_response:thm:response-literal-transfer`. -/
theorem normalMatrixDerivList_append (α β : List (Fin n))
    (f : Euclidean n → Matrix (Fin r) (Fin r) ℂ) :
    normalMatrixDerivList (α ++ β) f =
      normalMatrixDerivList α (normalMatrixDerivList β f) := by
  induction α with
  | nil => rfl
  | cons i α ih => simp only [List.cons_append, normalMatrixDerivList, ih]

/-- Ordered target jets distribute over a smooth matrix sum. This supplies the
additive step of `normalMatrixDerivList_snoc_smul` in
`app:ch_response:thm:response-literal-transfer`. -/
theorem normalMatrixDerivList_add
    {f g : Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (α : List (Fin n)) :
    normalMatrixDerivList α (fun x ↦ f x + g x) =
      fun x ↦ normalMatrixDerivList α f x + normalMatrixDerivList α g x := by
  induction α with
  | nil => rfl
  | cons i α ih =>
    simp only [normalMatrixDerivList, ih]
    funext x
    rw [fderiv_fun_add ((contDiff_normalMatrixDerivList hf α).differentiable (by simp) x)
      ((contDiff_normalMatrixDerivList hg α).differentiable (by simp) x)]
    rfl

/-- Exact ordered Leibniz recursion: the innermost target derivative lands on
either the scalar or the matrix factor. Iterating this identity proves
`norm_iteratedFDeriv_normalMatrixDerivList_smul_le`, without commuting target and
source derivatives (`app:ch_response:thm:response-literal-transfer`). -/
theorem normalMatrixDerivList_snoc_smul
    {f : Euclidean n → ℂ} {B : Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (hf : ContDiff ℝ ∞ f) (hB : ContDiff ℝ ∞ B) (α : List (Fin n)) (i : Fin n) :
    normalMatrixDerivList (α ++ [i]) (fun x ↦ f x • B x) = fun x ↦
      normalMatrixDerivList α (fun z ↦ f z • normalMatrixDerivList [i] B z) x +
      normalMatrixDerivList α (fun z ↦ euclideanCoordinateDerivList [i] f z • B z) x := by
  rw [normalMatrixDerivList_append]
  have he : normalMatrixDerivList [i] (fun x ↦ f x • B x) = fun x ↦
      f x • normalMatrixDerivList [i] B x + euclideanCoordinateDerivList [i] f x • B x := by
    funext x
    simp only [normalMatrixDerivList, euclideanCoordinateDerivList]
    rw [fderiv_fun_smul (hf.differentiable (by simp) x) (hB.differentiable (by simp) x)]
    rfl
  rw [he]
  exact normalMatrixDerivList_add
    (hf.smul (contDiff_normalMatrixDerivList hB [i]))
    ((contDiff_euclideanCoordinateDerivList hf [i]).smul hB) α

/-- Pascal's identity combines the two product-rule contributions in
`norm_iteratedFDeriv_normalMatrixDerivList_smul_le`
(`app:ch_response:thm:response-literal-transfer`). -/
private theorem outputLeibniz_sum_succ (G H : ℕ → ℝ) (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * G j * H (m - j + 1)) +
      (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * G (j + 1) * H (m - j)) =
    ∑ j ∈ Finset.range (m + 2), ((m + 1).choose j : ℝ) * G j * H (m + 1 - j) := by
  rw [show (∑ j ∈ Finset.range (m + 2), ((m + 1).choose j : ℝ) * G j * H (m + 1 - j)) =
    ∑ j ∈ Finset.range (m + 2), ((m + 1).choose j : ℝ) * (G j * H (m + 1 - j)) by
      simp only [mul_assoc], Finset.sum_choose_succ_mul (fun a b ↦ G a * H b) m]
  simp only [← mul_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [show m - j + 1 = m + 1 - j by have := Finset.mem_range.mp hj; omega]

/-- Mixed ordered Leibniz estimate for a target-only scalar factor and a full
matrix amplitude (`app:ch_response:thm:response-literal-transfer`). The source
order `k` is fixed, and only primitive jets enter the binomial convolution.
The oscillatory specialization is `norm_iteratedFDeriv_outputJetAmplitude_le_leibniz`. -/
theorem norm_iteratedFDeriv_normalMatrixDerivList_smul_le
    (f : Euclidean n → ℂ) (A : FullAmplitude n r) (η : Euclidean n)
    (hf : ContDiff ℝ ∞ f)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    (k : ℕ) (G H : ℕ → ℝ) (hG : ∀ j, 0 ≤ G j) (hH : ∀ j, 0 ≤ H j)
    (hfG : ∀ (β : List (Fin n)) x, ‖euclideanCoordinateDerivList β f x‖ ≤ G β.length)
    (hAH : ∀ (β : List (Fin n)) x y,
      ‖iteratedFDeriv ℝ k (fun z ↦ normalMatrixDerivList β (fun w ↦ A w z η) x) y‖ ≤
        H β.length)
    (α : List (Fin n)) (x y : Euclidean n) :
    ‖iteratedFDeriv ℝ k
      (fun z ↦ normalMatrixDerivList α (fun w ↦ f w • A w z η) x) y‖ ≤
      ∑ j ∈ Finset.range (α.length + 1), (α.length.choose j : ℝ) * G j * H (α.length - j) := by
  induction α using List.reverseRecOn generalizing f A G H with
  | nil =>
    simp only [normalMatrixDerivList, List.length_nil, Nat.zero_add, Finset.sum_range_one,
      Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    have hs : ContDiff ℝ ∞ (fun z ↦ A x z η) :=
      hA.comp (contDiff_const.prodMk contDiff_id)
    rw [iteratedFDeriv_const_smul_apply' (hs.contDiffAt.of_le (by simp)), norm_smul]
    exact mul_le_mul (hfG [] x) (hAH [] x y) (norm_nonneg _) (hG 0)
  | append_singleton α i ih =>
    let A' : FullAmplitude n r := fun w z ξ ↦ normalMatrixDerivList [i] (fun v ↦ A v z ξ) w
    let f' := euclideanCoordinateDerivList [i] f
    have hA' : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A' p.1 p.2 η) :=
      contDiff_joint_normalMatrixDerivList (f := fun w z ↦ A w z η) hA [i]
    have hf' : ContDiff ℝ ∞ f' := contDiff_euclideanCoordinateDerivList hf [i]
    have hAH' (β : List (Fin n)) (w z : Euclidean n) :
        ‖iteratedFDeriv ℝ k (fun v ↦ normalMatrixDerivList β (fun u ↦ A' u v η) w) z‖ ≤
          H (β.length + 1) := by
      simpa only [A', ← normalMatrixDerivList_append, List.length_append,
        List.length_singleton] using hAH (β ++ [i]) w z
    have hfG' (β : List (Fin n)) (w : Euclidean n) :
        ‖euclideanCoordinateDerivList β f' w‖ ≤ G (β.length + 1) := by
      simpa only [f', ← Pseudodifferential.euclideanCoordinateDerivList_append,
        List.length_append, List.length_singleton] using hfG (β ++ [i]) w
    have h1 := ih f A' hf hA' G (fun j ↦ H (j + 1)) hG (fun j ↦ hH (j + 1)) hfG hAH'
    have h2 := ih f' A hf' hA (fun j ↦ G (j + 1)) H (fun j ↦ hG (j + 1)) hH hfG' hAH
    have he : (fun z ↦ normalMatrixDerivList (α ++ [i]) (fun w ↦ f w • A w z η) x) =
        fun z ↦ normalMatrixDerivList α (fun w ↦ f w • A' w z η) x +
          normalMatrixDerivList α (fun w ↦ f' w • A w z η) x := by
      funext z
      exact congrFun (normalMatrixDerivList_snoc_smul hf
        (hA.comp (contDiff_id.prodMk contDiff_const)) α i) x
    have hs1 : ContDiff ℝ ∞
        (fun z ↦ normalMatrixDerivList α (fun w ↦ f w • A' w z η) x) :=
      (contDiff_joint_normalMatrixDerivList (f := fun w z ↦ f w • A' w z η)
        ((hf.comp contDiff_fst).smul hA') α).comp (contDiff_const.prodMk contDiff_id)
    have hs2 : ContDiff ℝ ∞
        (fun z ↦ normalMatrixDerivList α (fun w ↦ f' w • A w z η) x) :=
      (contDiff_joint_normalMatrixDerivList (f := fun w z ↦ f' w • A w z η)
        ((hf'.comp contDiff_fst).smul hA) α).comp (contDiff_const.prodMk contDiff_id)
    rw [he]
    change ‖iteratedFDeriv ℝ k
      ((fun z ↦ normalMatrixDerivList α (fun w ↦ f w • A' w z η) x) +
       (fun z ↦ normalMatrixDerivList α (fun w ↦ f' w • A w z η) x)) y‖ ≤ _
    rw [iteratedFDeriv_add_apply (hs1.contDiffAt.of_le (by simp)) (hs2.contDiffAt.of_le (by simp))]
    exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by
      simpa only [List.length_append, List.length_singleton, Nat.add_assoc] using
        outputLeibniz_sum_succ G H α.length))

/-- The actual output-jet amplitude obeys the mixed Leibniz bound from primitive
amplitude jets and scalar oscillation jets. Its demodulation factor has norm one
and is constant in the source position. This is the conditional estimate used by
`OutputJets.Grades` for `app:ch_response:thm:response-literal-transfer`; the parent
construction must supply `G` from phase bounds and `H` from mixed amplitude bounds. -/
theorem norm_iteratedFDeriv_outputJetAmplitude_le_leibniz
    (τ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r) (η : Euclidean n)
    (hτ : ContDiff ℝ ∞ (fun x ↦ τ x η))
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    (k : ℕ) (G H : ℕ → ℝ) (hG : ∀ j, 0 ≤ G j) (hH : ∀ j, 0 ≤ H j)
    (hτG : ∀ (β : List (Fin n)) x,
      ‖euclideanCoordinateDerivList β (phaseOscillation (fun w ↦ τ w η)) x‖ ≤ G β.length)
    (hAH : ∀ (β : List (Fin n)) x y,
      ‖iteratedFDeriv ℝ k (fun z ↦ normalMatrixDerivList β (fun w ↦ A w z η) x) y‖ ≤
        H β.length)
    (α : List (Fin n)) (x y : Euclidean n) :
    ‖iteratedFDeriv ℝ k (fun z ↦ outputJetAmplitude τ α A x z η) y‖ ≤
      ∑ j ∈ Finset.range (α.length + 1), (α.length.choose j : ℝ) * G j * H (α.length - j) := by
  have hs : ContDiff ℝ ∞ (fun z ↦ normalMatrixDerivList α
      (fun w ↦ phaseOscillation (fun v ↦ τ v η) w • A w z η) x) :=
    (contDiff_joint_normalMatrixDerivList
      (f := fun w z ↦ phaseOscillation (fun v ↦ τ v η) w • A w z η)
      (((contDiff_outputOscillation hτ).comp contDiff_fst).smul hA) α).comp
      (contDiff_const.prodMk contDiff_id)
  simp only [outputJetAmplitude,
    iteratedFDeriv_const_smul_apply' (hs.contDiffAt.of_le (by simp)),
    norm_smul, JanetCartan.Localization.norm_phaseOscillation, one_mul]
  exact norm_iteratedFDeriv_normalMatrixDerivList_smul_le
    (phaseOscillation (fun w ↦ τ w η)) A η (contDiff_outputOscillation hτ) hA
    k G H hG hH hτG hAH α x y

end JanetCartan.ResponseTransfer.LowEnvelope
