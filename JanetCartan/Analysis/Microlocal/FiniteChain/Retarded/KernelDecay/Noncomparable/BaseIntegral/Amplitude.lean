module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.AmplitudeGrades.Products

/-!
# Primitive weight bounds for common-base integration

The two literal amplitudes in `app:ch_regular:lem:finite-chain` have a common
compact carrier and a two-factor Leibniz profile. This supplies the amplitude
input for the noncomparable estimate of `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.FiniteChain.Retarded.KernelDecay.BaseIntegral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The weight portion of the literal amplitude, preserving the scalar and
weight order of the adjoint (`app:ch_regular:lem:finite-chain`). -/
def weightAmplitude (upper : Bool) (α β : ℝ × E → ℝ) (x : ℝ × (ℝ × E)) : ℂ :=
  if upper then -Complex.I * (β x.2 : ℂ) * (α (x.2.1 + x.1, x.2.2) : ℂ)
  else Complex.I * (α (x.2.1 + x.1, x.2.2) : ℂ) * (β x.2 : ℂ)

/-- The carrier is fixed before the weights or frequency parameters are chosen
(`app:ch_regular:lem:finite-chain`). -/
def weightCarrier (Kα Kβ : Set (ℝ × E)) : Set (ℝ × (ℝ × E)) :=
  (fun p : (ℝ × E) × (ℝ × E) => (p.1.1 - p.2.1, p.2)) '' (Kα ×ˢ Kβ)

omit [NormedSpace ℝ E] in
/-- Compact primitive weight carriers give compact normal and common-base
support (`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_weightCarrier {Kα Kβ : Set (ℝ × E)}
    (hα : IsCompact Kα) (hβ : IsCompact Kβ) : IsCompact (weightCarrier Kα Kβ) :=
  (hα.prod hβ).image (by fun_prop)

omit [NormedSpace ℝ E] in
/-- Support is derived from the primitive weights, without a full-amplitude
support assumption (`app:ch_regular:lem:finite-chain`). -/
theorem tsupport_weightAmplitude_subset (upper : Bool) (α β : ℝ × E → ℝ)
    {Kα Kβ : Set (ℝ × E)} (hKα : IsCompact Kα) (hKβ : IsCompact Kβ)
    (hα : tsupport α ⊆ Kα) (hβ : tsupport β ⊆ Kβ) :
    tsupport (weightAmplitude upper α β) ⊆ weightCarrier Kα Kβ := by
  apply closure_minimal ?_ (isCompact_weightCarrier hKα hKβ).isClosed
  intro x hx
  have ha : α (x.2.1 + x.1, x.2.2) ≠ 0 := by
    intro hz
    cases upper <;> simp [weightAmplitude, hz] at hx
  have hb : β x.2 ≠ 0 := by
    intro hz
    cases upper <;> simp [weightAmplitude, hz] at hx
  refine ⟨((x.2.1 + x.1, x.2.2), x.2),
    ⟨hα (subset_tsupport α ha), hβ (subset_tsupport β hb)⟩, ?_⟩
  simp

private def shiftedBase : (ℝ × (ℝ × E)) →L[ℝ] ℝ × E :=
  (((ContinuousLinearMap.fst ℝ ℝ E).comp (ContinuousLinearMap.snd ℝ ℝ _)) +
    ContinuousLinearMap.fst ℝ ℝ _).prod
    ((ContinuousLinearMap.snd ℝ ℝ E).comp (ContinuousLinearMap.snd ℝ ℝ _))

private theorem norm_shiftedBase_le : ‖shiftedBase (E := E)‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖(x.2.1 + x.1, x.2.2)‖ ≤ _
  rw [Prod.norm_def]
  have h1 := (norm_fst_le x.2).trans (norm_snd_le x)
  have h2 := (norm_snd_le x.2).trans (norm_snd_le x)
  exact max_le (by linarith [norm_add_le x.2.1 x.1, norm_fst_le x])
    (by linarith [norm_nonneg x])

/-- Smoothness follows directly from the two primitive weights
(`app:ch_regular:lem:finite-chain`). -/
theorem contDiff_weightAmplitude (upper : Bool) {α β : ℝ × E → ℝ}
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (weightAmplitude upper α β) := by
  have ha : ContDiff ℝ ∞ (fun x : ℝ × (ℝ × E) => (α (x.2.1 + x.1, x.2.2) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hα.comp (shiftedBase (E := E)).contDiff)
  have hb : ContDiff ℝ ∞ (fun x : ℝ × (ℝ × E) => (β x.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hβ.comp contDiff_snd)
  cases upper
  · exact (contDiff_const.mul ha).mul hb
  · exact (contDiff_const.mul hb).mul ha

/-- The explicit two-weight profile, including the shifted coordinate cost
`2^j`, used in `app:ch_regular:eq:chain-tail`. -/
def weightProfile (A B : ℕ → ℝ) : ℕ → ℝ :=
  derivativeConvolution (fun j => A j * 2 ^ j) B

/-- Nonnegativity of the product profile (`app:ch_regular:eq:chain-tail`). -/
theorem weightProfile_nonneg {A B : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    (j : ℕ) : 0 ≤ weightProfile A B j :=
  derivativeConvolution_nonneg (fun j => mul_nonneg (hA j) (by positivity)) hB j

/-- Derive all amplitude bounds from primitive weight jets. There is no
covector derivative and no assumed full-amplitude profile
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_weightAmplitude_le (upper : Bool) {α β : ℝ × E → ℝ}
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    {A B : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    {L : ℝ} (hL : 1 ≤ L)
    (ha : ∀ j y, ‖iteratedFDeriv ℝ j α y‖ ≤ A j * L ^ j)
    (hb : ∀ j y, ‖iteratedFDeriv ℝ j β y‖ ≤ B j * L ^ j)
    (x : ℝ × (ℝ × E)) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (weightAmplitude upper α β) x‖ ≤ weightProfile A B j * L ^ j := by
  let a := fun x : ℝ × (ℝ × E) => (α (shiftedBase x) : ℂ)
  let b := fun x : ℝ × (ℝ × E) => (β x.2 : ℂ)
  have hsa : ContDiff ℝ ∞ a :=
    Complex.ofRealCLM.contDiff.comp (hα.comp (shiftedBase (E := E)).contDiff)
  have hsb : ContDiff ℝ ∞ b := Complex.ofRealCLM.contDiff.comp (hβ.comp contDiff_snd)
  have ha' (n : ℕ) : ‖iteratedFDeriv ℝ n a x‖ ≤ 1 * (A n * 2 ^ n) * L ^ (n + 0) := by
    change ‖iteratedFDeriv ℝ n (Complex.ofRealLI ∘ (α ∘ shiftedBase)) x‖ ≤ _
    rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      (hα.comp (shiftedBase (E := E)).contDiff).contDiffAt (show (n : ℕ∞ω) ≤ ∞ by simp)]
    apply norm_iteratedFDeriv_comp_linear_le_grades hα shiftedBase (by norm_num)
      norm_shiftedBase_le hA zero_le_one (zero_le_one.trans hL) 0 x n
    simpa using ha n (shiftedBase x)
  have hb' (n : ℕ) : ‖iteratedFDeriv ℝ n b x‖ ≤ 1 * B n * L ^ (n + 0) := by
    change ‖iteratedFDeriv ℝ n (Complex.ofRealLI ∘ (β ∘ ContinuousLinearMap.snd ℝ ℝ (ℝ × E))) x‖ ≤ _
    rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      (hβ.comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × E)).contDiff).contDiffAt
      (show (n : ℕ∞ω) ≤ ∞ by simp)]
    simpa using norm_iteratedFDeriv_comp_linear_le_grades hβ
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × E)) zero_le_one
      (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by
        intro y
        simpa using norm_snd_le y)) hB zero_le_one (zero_le_one.trans hL)
      0 x n (by simpa using hb n x.2)
  have hab := norm_iteratedFDeriv_mul_le_grades hsa hsb
    (fun n => mul_nonneg (hA n) (by positivity)) hB zero_le_one zero_le_one
    (zero_le_one.trans hL) 0 0 x ha' hb' j
  have he : weightAmplitude upper α β =
      (if upper then -Complex.I else Complex.I) • (fun y => a y * b y) := by
    funext y
    cases upper <;> simp [weightAmplitude, a, b, shiftedBase, mul_comm, mul_left_comm, mul_assoc]
  rw [he, iteratedFDeriv_const_smul_apply ((hsa.mul hsb).contDiffAt.of_le (by simp)), norm_smul]
  have hn : ‖(if upper then -Complex.I else Complex.I)‖ = 1 := by cases upper <;> simp
  rw [hn, one_mul]
  simpa [weightProfile] using hab

end JanetCartan.FiniteChain.Retarded.KernelDecay.BaseIntegral
