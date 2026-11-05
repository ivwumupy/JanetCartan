module

public import JanetCartan.Analysis.Operator.RetardedSobolev.ConcreteTransverse
public import JanetCartan.Analysis.Operator.RetardedSobolev.CompactTimeEnergy

/-!
# Repeated transverse derivatives of retarded primitives

For `app:ch_osc:prop:osc-retarded-tube`, arbitrary ordered transverse derivatives
commute with the unweighted lower and upper primitives. The derivatives here
are actual Fréchet derivatives of the transverse slices. Smoothness of the input
supplies every differentiation-under-the-integral hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.RetardedSobolev

variable {Y E : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A transverse directional derivative in the coordinates of
`app:ch_osc:setup:osc-retarded`. -/
def transverseDeriv (v : Y) (f : ℝ × Y → E) (x : ℝ × Y) : E :=
  fderiv ℝ (fun y ↦ f (x.1, y)) x.2 v

/-- Ordered, repeated transverse derivatives for
`app:ch_osc:prop:osc-retarded-tube`. -/
def transverseJet : List Y → (ℝ × Y → E) → (ℝ × Y → E)
  | [], f => f
  | v :: vs, f => transverseDeriv v (transverseJet vs f)

/-- Transverse derivatives are evaluations of the full differential
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem transverseDeriv_eq_fderiv (v : Y) {f : ℝ × Y → E}
    (hf : Differentiable ℝ f) :
    transverseDeriv v f = fun x ↦ fderiv ℝ f x (0, v) := by
  funext x
  have h := ((hf (x.1, x.2)).hasFDerivAt.comp x.2
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) x.1 x.2)).fderiv
  exact congrArg (fun L ↦ L v) h

/-- Smoothness of every actual transverse jet
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem contDiff_transverseJet {f : ℝ × Y → E} (hf : ContDiff ℝ ∞ f) (vs : List Y) :
    ContDiff ℝ ∞ (transverseJet vs f) := by
  induction vs with
  | nil => exact hf
  | cons v vs ih =>
    rw [transverseJet, transverseDeriv_eq_fderiv v (ih.differentiable (by simp))]
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

/-- Compact support is preserved by transverse jets
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem hasCompactSupport_transverseJet {f : ℝ × Y → E} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (vs : List Y) : HasCompactSupport (transverseJet vs f) := by
  induction vs with
  | nil => exact hs
  | cons v vs ih =>
    rw [transverseJet, transverseDeriv_eq_fderiv v
      ((contDiff_transverseJet hf vs).differentiable (by simp))]
    exact ih.fderiv_apply ℝ (0, v)

/-- Every mixed time/transverse jet of a smooth cutoff is bounded
(`app:ch_osc:prop:osc-retarded-tube`). The constant is independent of the input. -/
theorem exists_timeJet_transverseJet_bound {f : ℝ × Y → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (vs : List Y) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ m, ∀ x, ‖timeJet j (transverseJet vs f) x‖ ≤ C :=
  exists_timeJet_bound (contDiff_transverseJet hf vs)
    (hasCompactSupport_transverseJet hf hs vs) m

variable [ProperSpace Y]

/-- A directional derivative passes through a fixed finite time integral
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem transverseDeriv_timeIntegral (v : Y) {g : ℝ × Y → E}
    (hg : ContDiff ℝ 1 g) (a b t : ℝ) (y : Y) :
    transverseDeriv v (fun x ↦ ∫ s in a..b, g (s, x.2)) (t, y) =
      ∫ s in a..b, transverseDeriv v g (s, y) := by
  unfold transverseDeriv
  rw [(hasFDerivAt_timeIntegral_transverse hg a b y).fderiv]
  rw [ContinuousLinearMap.intervalIntegral_apply
    ((((hg.continuous_fderiv (by norm_num)).comp
      (continuous_id.prodMk continuous_const)).clm_comp continuous_const).intervalIntegrable a b)]
  apply intervalIntegral.integral_congr
  intro s _
  have h := (((hg.differentiable (by norm_num)) (s, y)).hasFDerivAt.comp y
    (hasFDerivAt_prodMk_right s y)).fderiv
  exact congrArg (fun L ↦ L v) h.symm

/-- Every ordered transverse jet commutes with the lower primitive in
`app:ch_osc:prop:osc-retarded-tube`. -/
theorem transverseJet_lower_one (a : ℝ) {f : ℝ × Y → ℂ}
    (hf : ContDiff ℝ ∞ f) (vs : List Y) :
    transverseJet vs (Retarded.lower a (fun _ ↦ 1) (fun _ ↦ 1) f) =
      Retarded.lower a (fun _ ↦ 1) (fun _ ↦ 1) (transverseJet vs f) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [transverseJet, ih]
    funext x
    simpa only [transverseDeriv, Retarded.lower, Complex.ofReal_one, one_mul,
      transverseJet] using transverseDeriv_timeIntegral v
        ((contDiff_transverseJet hf vs).of_le (by simp)) a x.1 x.1 x.2

/-- Every ordered transverse jet commutes with the upper primitive in
`app:ch_osc:eq:retarded-literal-adjoint`. -/
theorem transverseJet_upper_one (b : ℝ) {f : ℝ × Y → ℂ}
    (hf : ContDiff ℝ ∞ f) (vs : List Y) :
    transverseJet vs (Retarded.upper b (fun _ ↦ 1) (fun _ ↦ 1) f) =
      Retarded.upper b (fun _ ↦ 1) (fun _ ↦ 1) (transverseJet vs f) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [transverseJet, ih]
    funext x
    simpa only [transverseDeriv, Retarded.upper, Complex.ofReal_one, one_mul,
      transverseJet] using transverseDeriv_timeIntegral v
        ((contDiff_transverseJet hf vs).of_le (by simp)) x.1 b x.1 x.2

/-- Positive time derivatives of every transverse jet of the lower primitive
are the corresponding jets of the input (`app:ch_osc:prop:osc-retarded-tube`). -/
theorem timeJet_transverseJet_lower_one_succ (a : ℝ) {f : ℝ × Y → ℂ}
    (hf : ContDiff ℝ ∞ f) (vs : List Y) (j : ℕ) :
    timeJet (j + 1) (transverseJet vs (Retarded.lower a (fun _ ↦ 1) (fun _ ↦ 1) f)) =
      timeJet j (transverseJet vs f) := by
  rw [transverseJet_lower_one a hf vs]
  exact timeJet_lower_one_succ a _
    (fun _ ↦ (contDiff_transverseJet hf vs).continuous.comp
      (continuous_id.prodMk continuous_const)) j

/-- The upper primitive has the opposite endpoint sign for every mixed jet
(`app:ch_osc:eq:retarded-literal-adjoint`). -/
theorem timeJet_transverseJet_upper_one_succ (b : ℝ) {f : ℝ × Y → ℂ}
    (hf : ContDiff ℝ ∞ f) (vs : List Y) (j : ℕ) :
    timeJet (j + 1) (transverseJet vs (Retarded.upper b (fun _ ↦ 1) (fun _ ↦ 1) f)) =
      fun x ↦ -timeJet j (transverseJet vs f) x := by
  rw [transverseJet_upper_one b hf vs]
  exact timeJet_upper_one_succ b _
    (fun _ ↦ (contDiff_transverseJet hf vs).continuous.comp
      (continuous_id.prodMk continuous_const)) j

end JanetCartan.RetardedSobolev
