module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.Noncomparable.Geometry

/-!
# The retarded phase with fixed covectors

The common-base integration in `app:ch_regular:lem:finite-chain` treats both
covectors as parameters. This removes external bases from every phase derivative
used in the noncomparable estimate of `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.FiniteChain.Retarded.KernelDecay.BaseIntegral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
attribute [local fun_prop] ContDiff.inner DifferentiableAt.inner

/-- The exact literal phase with output/input covectors fixed, in that order
(`app:ch_regular:lem:finite-chain`). -/
def basePhase (upper : Bool) (xi xo : ℝ × E) (w : (ℝ × E) × (ℝ × E))
    (x : ℝ × (ℝ × E)) : ℝ := literalPhase upper xi xo (x.1, x.2, w)

/-- Smoothness in the normal and common-base variables
(`app:ch_regular:lem:finite-chain`). -/
theorem contDiff_basePhase (upper : Bool) (xi xo : ℝ × E) (w : (ℝ × E) × (ℝ × E)) :
    ContDiff ℝ ∞ (basePhase upper xi xo w) :=
  (contDiff_literalPhase upper xi xo).comp (by fun_prop)

/-- Every phase derivative is independent of the external bases and integration
point. The normal coefficient is retained, but never inverted
(`app:ch_regular:lem:finite-chain`). -/
theorem fderiv_basePhase_apply (upper : Bool) (xi xo : ℝ × E)
    (w : (ℝ × E) × (ℝ × E)) (x v : ℝ × (ℝ × E)) :
    fderiv ℝ (basePhase upper xi xo w) x v =
      (if upper then w.2.1 else -w.1.1) * v.1 +
      (w.2.1 - w.1.1) * v.2.1 + inner ℝ (w.2.2 - w.1.2) v.2.2 := by
  cases upper <;>
    unfold basePhase literalPhase packedPhase LocalizedKernel.packedUpperPhase phase adjointPhase <;>
    simp (disch := fun_prop) only [Bool.false_eq_true, ↓reduceIte,
      fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul, add_apply, sub_apply,
      smul_apply, smul_eq_mul, fderiv_inner_apply, fderiv.fst, fderiv.snd,
      fderiv_const_apply, fderiv_fun_id, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.id_apply, zero_apply, inner_sub_left,
      inner_zero_right, Prod.fst_zero, Prod.snd_zero] <;>
    simp only [real_inner_comm v.2.2 w.1.2, real_inner_comm v.2.2 w.2.2] <;> ring

/-- Freezing the covectors makes the gradient constant in all integration
variables (`app:ch_regular:lem:finite-chain`). -/
theorem fderiv_basePhase_eq_const (upper : Bool) (xi xo : ℝ × E)
    (w : (ℝ × E) × (ℝ × E)) :
    fderiv ℝ (basePhase upper xi xo w) =
      fun _ => fderiv ℝ (basePhase upper (0, 0) (0, 0) w) 0 := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  simp only [fderiv_basePhase_apply]

/-- The common-time and transverse directions used in tangential integration
by parts (`app:ch_regular:lem:finite-chain`). -/
def baseDirections {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ E) : Unit ⊕ ι → ℝ × E
  | .inl _ => (1, 0)
  | .inr i => (0, e i)

/-- The frozen-covector squared gradient equals the manuscript frequency gap
(`app:ch_regular:lem:finite-chain`). -/
theorem basePhase_gradientSquare {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (upper : Bool) (xi xo : ℝ × E)
    (w : (ℝ × E) × (ℝ × E)) (d : ℝ) (b : ℝ × E) :
    Localization.phaseGradientSquare (baseDirections e)
      (fun z => basePhase upper xi xo w (d, z)) b =
      (w.2.1 - w.1.1) ^ 2 + ‖w.2.2 - w.1.2‖ ^ 2 := by
  have hd (v : ℝ × E) :
      fderiv ℝ (fun z => basePhase upper xi xo w (d, z)) b v =
        (w.2.1 - w.1.1) * v.1 + inner ℝ (w.2.2 - w.1.2) v.2 := by
    have h := ((contDiff_basePhase upper xi xo w).differentiable (by simp)
      (d, b)).hasFDerivAt.comp b ((hasFDerivAt_const d b).prodMk (hasFDerivAt_id b))
    change HasFDerivAt (fun z => basePhase upper xi xo w (d, z)) _ b at h
    rw [h.fderiv]
    simp [ContinuousLinearMap.comp_apply, fderiv_basePhase_apply]
  have hs (a : E) : ∑ i, (inner ℝ a (e i)) ^ 2 = ‖a‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using e.sum_sq_norm_inner_left a
  simp [Localization.phaseGradientSquare, hd, baseDirections, Fintype.sum_sum_type, hs]

/-- The noncomparable gap holds on the entire open common-base space; no
frequency variable is differentiated (`app:ch_regular:lem:finite-chain`). -/
theorem basePhase_gradient_gap {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (upper : Bool) (xi xo : ℝ × E)
    (w : (ℝ × E) × (ℝ × E)) {c : ℝ} (hc : 0 ≤ c)
    (hlarge : c ≤ max (frequencySize w.2.1 w.2.2) (frequencySize w.1.1 w.1.2))
    (hsep : 2 * frequencySize w.2.1 w.2.2 ≤ frequencySize w.1.1 w.1.2 ∨
      2 * frequencySize w.1.1 w.1.2 ≤ frequencySize w.2.1 w.2.2)
    (d : ℝ) (b : ℝ × E) :
    c ^ 2 / 4 ≤ Localization.phaseGradientSquare (baseDirections e)
      (fun z => basePhase upper xi xo w (d, z)) b := by
  rw [basePhase_gradientSquare]
  simpa only [literalPhase_base_gradientSquare] using
    noncomparable_literalPhase_gradient_gap e upper xi xo d (b, w) hc hlarge hsep

omit [InnerProductSpace ℝ E] in
private theorem frequency_components_le {τ M : ℝ} {η : E}
    (h : frequencySize τ η ≤ M) : ‖τ‖ ≤ M ∧ ‖η‖ ≤ M := by
  constructor
  · apply le_trans ?_ h
    simpa only [frequencySize, Real.sqrt_sq_eq_abs, Real.norm_eq_abs] using
      Real.sqrt_le_sqrt (show τ ^ 2 ≤ τ ^ 2 + ‖η‖ ^ 2 by nlinarith [sq_nonneg ‖η‖])
  · apply le_trans ?_ h
    simpa only [frequencySize, Real.sqrt_sq (norm_nonneg η)] using
      Real.sqrt_le_sqrt (show ‖η‖ ^ 2 ≤ τ ^ 2 + ‖η‖ ^ 2 by nlinarith [sq_nonneg τ])

/-- A global derivative bound depends only on the upper normalized frequency
radius, uniformly in both external bases (`app:ch_regular:lem:finite-chain`). -/
theorem norm_fderiv_basePhase_le (upper : Bool) (xi xo : ℝ × E)
    (w : (ℝ × E) × (ℝ × E)) {M : ℝ}
    (hM : max (frequencySize w.2.1 w.2.2) (frequencySize w.1.1 w.1.2) ≤ M)
    (x : ℝ × (ℝ × E)) : ‖fderiv ℝ (basePhase upper xi xo w) x‖ ≤ 5 * M := by
  have hi := frequency_components_le ((le_max_left _ _).trans hM)
  have ho := frequency_components_le ((le_max_right _ _).trans hM)
  have hM0 : 0 ≤ M := (norm_nonneg w.2.1).trans hi.1
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [fderiv_basePhase_apply]
  have hn : ‖(if upper then w.2.1 else -w.1.1)‖ ≤ M := by
    cases upper
    · simpa using ho.1
    · simpa using hi.1
  have ht : ‖w.2.1 - w.1.1‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith)
  have hy : ‖w.2.2 - w.1.2‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith)
  calc
    _ ≤ ‖(if upper then w.2.1 else -w.1.1) * v.1‖ +
        ‖(w.2.1 - w.1.1) * v.2.1‖ + ‖inner ℝ (w.2.2 - w.1.2) v.2.2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ M * ‖v‖ + (2 * M) * ‖v‖ + (2 * M) * ‖v‖ := by
      simp only [norm_mul]
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul hn (norm_fst_le v) (norm_nonneg _) hM0
        · exact mul_le_mul ht ((norm_fst_le v.2).trans (norm_snd_le v))
            (norm_nonneg _) (by positivity)
      · exact (norm_inner_le_norm _ _).trans (mul_le_mul hy
          ((norm_snd_le v.2).trans (norm_snd_le v)) (norm_nonneg _) (by positivity))
    _ = _ := by ring

/-- All higher gradient derivatives vanish with the covectors fixed. The
constant profile `5 M` is uniform in the external bases and the grade scale
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_fderiv_basePhase_le (upper : Bool) (xi xo : ℝ × E)
    (w : (ℝ × E) × (ℝ × E)) {M L : ℝ} (hL : 1 ≤ L)
    (hM : max (frequencySize w.2.1 w.2.2) (frequencySize w.1.1 w.1.2) ≤ M)
    (x : ℝ × (ℝ × E)) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fderiv ℝ (basePhase upper xi xo w)) x‖ ≤ (5 * M) * L ^ j := by
  cases j with
  | zero => simpa using norm_fderiv_basePhase_le upper xi xo w hM x
  | succ j =>
    rw [fderiv_basePhase_eq_const, iteratedFDeriv_succ_const]
    have hM0 : 0 ≤ M := (Real.sqrt_nonneg _).trans ((le_max_left _ _).trans hM)
    simp only [Pi.zero_apply, norm_zero]
    positivity

end JanetCartan.FiniteChain.Retarded.KernelDecay.BaseIntegral
