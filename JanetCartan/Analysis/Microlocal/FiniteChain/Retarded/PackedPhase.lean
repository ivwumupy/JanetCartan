module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.Gaps
public import JanetCartan.Analysis.Microlocal.Localization.Coefficients

/-!
# The joint retarded phase and its integration-by-parts gradients

The partial-derivative defects of `app:ch_regular:lem:finite-chain` are
connected here to the actual Fréchet derivative and to the directional
square used by the half-space integration-by-parts theorem. All six
tangential variables, including both covectors and the common base, remain
integration variables. The normal variable is kept separate.
-/

@[expose] public noncomputable section

open scoped ContDiff
attribute [local fun_prop] ContDiff.inner DifferentiableAt.inner
namespace JanetCartan.FiniteChain.Retarded
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The common base, output covector, and input covector, in that order
(`app:ch_regular:lem:finite-chain`). -/
abbrev TangentialVariables (E : Type*) := (ℝ × E) × (ℝ × E) × (ℝ × E)
/-- The manuscript phase on the normal/tangential product space required
by half-space integration by parts (`app:ch_regular:lem:finite-chain`). -/
def packedPhase (xi xo : ℝ × E) (x : ℝ × TangentialVariables E) : ℝ :=
  phase xi xo x.1 x.2.1.1 x.2.1.2 x.2.2.1.1 x.2.2.1.2 x.2.2.2.1 x.2.2.2.2
/-- Smoothness of the full joint phase (`app:ch_regular:lem:finite-chain`). -/
theorem contDiff_packedPhase (xi xo : ℝ × E) : ContDiff ℝ ∞ (packedPhase xi xo) := by
  unfold packedPhase phase
  fun_prop
/-- The complete derivative, retaining the input-base equations
(`app:ch_regular:lem:finite-chain`). -/
theorem fderiv_packedPhase_apply (xi xo : ℝ × E) (x v : ℝ × TangentialVariables E) :
    fderiv ℝ (packedPhase xi xo) x v =
      (-x.2.2.1.1) * v.1 +
      (x.2.2.2.1 - x.2.2.1.1) * v.2.1.1 + inner ℝ (x.2.2.2.2 - x.2.2.1.2) v.2.1.2 +
      (xo.1 - (x.2.1.1 + x.1)) * v.2.2.1.1 + inner ℝ (xo.2-x.2.1.2) v.2.2.1.2 +
      (x.2.1.1-xi.1) * v.2.2.2.1 + inner ℝ (x.2.1.2-xi.2) v.2.2.2.2 := by
  unfold packedPhase phase
  simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul,
    add_apply, sub_apply,
    smul_apply, smul_eq_mul, fderiv_inner_apply,
    fderiv.fst, fderiv.snd, fderiv_const_apply, fderiv_fun_id,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.id_apply,
    zero_apply, inner_sub_left, inner_zero_left, Prod.fst_zero, Prod.snd_zero]
  simp only [real_inner_comm v.2.1.2 x.2.2.1.2,
    real_inner_comm v.2.1.2 x.2.2.2.2]
  ring
/-- The derivative in tangential variables only; no normal derivative
of the boundary jump occurs (`app:ch_regular:lem:finite-chain`). -/
theorem fderiv_packedPhase_tangential_apply (xi xo : ℝ × E) (d : ℝ)
    (z v : TangentialVariables E) :
    fderiv ℝ (fun w => packedPhase xi xo (d, w)) z v =
      (z.2.2.1 - z.2.1.1) * v.1.1 + inner ℝ (z.2.2.2 - z.2.1.2) v.1.2 +
      (xo.1 - (z.1.1 + d)) * v.2.1.1 + inner ℝ (xo.2-z.1.2) v.2.1.2 +
      (z.1.1-xi.1) * v.2.2.1 + inner ℝ (z.1.2-xi.2) v.2.2.2 := by
  have hp := (contDiff_packedPhase xi xo).differentiable (by simp)
  have he : (fun w => packedPhase xi xo (d, w)) =
      packedPhase xi xo ∘ (fun w : TangentialVariables E => (d, w)) := rfl
  rw [he, fderiv_comp z (hp _) (by fun_prop)]
  have hi : fderiv ℝ (fun w : TangentialVariables E => (d, w)) z =
      (0 : TangentialVariables E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ _) :=
    ((hasFDerivAt_const d z).prodMk (hasFDerivAt_id z)).fderiv
  rw [hi]
  simp [ContinuousLinearMap.comp_apply, fderiv_packedPhase_apply]

/-- Vanishing of the joint tangential derivative is exactly the six
stationary equations (`app:ch_regular:lem:finite-chain`). -/
theorem fderiv_packedPhase_tangential_eq_zero_iff (xi xo : ℝ × E) (d : ℝ)
    (z : TangentialVariables E) :
    fderiv ℝ (fun w => packedPhase xi xo (d, w)) z = 0 ↔
      TangentialStationary xi xo d z.1.1 z.1.2 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2 := by
  rw [tangentialStationary_iff]
  constructor
  · intro h
    have hv (v : TangentialVariables E) := congrArg (fun f : TangentialVariables E →L[ℝ] ℝ => f v) h
    simp only [fderiv_packedPhase_tangential_apply, zero_apply] at hv
    have hτ : z.2.2.1 = z.2.1.1 := sub_eq_zero.mp (by simpa using hv ((1, 0), 0, 0))
    have hη : z.2.2.2 = z.2.1.2 := sub_eq_zero.mp (by simpa using hv ((0, z.2.2.2-z.2.1.2), 0, 0))
    have ht : xo.1 = z.1.1+d := sub_eq_zero.mp (by simpa using hv (0, (1, 0), 0))
    have hy : xo.2 = z.1.2 := sub_eq_zero.mp (by simpa using hv (0, (0, xo.2-z.1.2), 0))
    have hs : z.1.1 = xi.1 := sub_eq_zero.mp (by simpa using hv (0, 0, (1, 0)))
    have hyi : z.1.2 = xi.2 := sub_eq_zero.mp (by simpa using hv (0, 0, (0, z.1.2-xi.2)))
    exact ⟨hτ, hη, ht, hy, hs, hyi⟩
  · rintro ⟨hτ, hη, ht, hy, hs, hyi⟩
    apply ContinuousLinearMap.ext
    intro v
    simp only [fderiv_packedPhase_tangential_apply, hτ, hη, ht, hy, hs, hyi,
      sub_self, zero_mul, inner_zero_left, add_zero, zero_apply]

/-- Separate the normal derivative from the tangential derivative
(`app:ch_regular:lem:finite-chain`). -/
theorem fderiv_packedPhase_split (xi xo : ℝ × E) (x v : ℝ × TangentialVariables E) :
    fderiv ℝ (packedPhase xi xo) x v = -x.2.2.1.1 * v.1 +
      fderiv ℝ (fun w => packedPhase xi xo (x.1, w)) x.2 v.2 := by
  rw [fderiv_packedPhase_apply, fderiv_packedPhase_tangential_apply]
  ring

/-- The full derivative vanishes exactly at interior stationary points
(`app:ch_regular:lem:finite-chain`). -/
theorem fderiv_packedPhase_eq_zero_iff (xi xo : ℝ × E) (x : ℝ × TangentialVariables E) :
    fderiv ℝ (packedPhase xi xo) x = 0 ↔
      InteriorStationary xi xo x.1 x.2.1.1 x.2.1.2 x.2.2.1.1 x.2.2.1.2
        x.2.2.2.1 x.2.2.2.2 := by
  rw [InteriorStationary, deriv_phase_normal, neg_eq_zero,
    ← fderiv_packedPhase_tangential_eq_zero_iff]
  constructor
  · intro h
    constructor
    · apply ContinuousLinearMap.ext
      intro v
      have hv := congrArg (fun f : (ℝ × TangentialVariables E) →L[ℝ] ℝ => f (0, v)) h
      simpa [fderiv_packedPhase_split] using hv
    · have hv := congrArg (fun f : (ℝ × TangentialVariables E) →L[ℝ] ℝ => f (1, 0)) h
      simpa [fderiv_packedPhase_split] using hv
  · rintro ⟨ht, hn⟩
    apply ContinuousLinearMap.ext
    intro v
    simp [fderiv_packedPhase_split, ht, hn]

section Basis
variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
/-- A finite basis detects vanishing of the derivative in the
integration-by-parts denominator (`app:ch_regular:lem:finite-chain`). -/
theorem phaseGradientSquare_basis_eq_zero_iff (e : Module.Basis ι ℝ V)
    (F : V → ℝ) (x : V) :
    Localization.phaseGradientSquare e F x = 0 ↔ fderiv ℝ F x = 0 := by
  constructor
  · intro h
    have hi : ∀ i, (fderiv ℝ F x (e i)) ^ 2 = 0 := by
      simpa only [Localization.phaseGradientSquare, Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg (fderiv ℝ F x (e i))), Finset.mem_univ, forall_true_left] using h
    have he : (fderiv ℝ F x).toLinearMap = 0 :=
      e.ext (fun i => sq_eq_zero_iff.mp (hi i))
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun f : V →ₗ[ℝ] ℝ => f v) he
  · intro h
    simp [Localization.phaseGradientSquare, h]

/-- Positivity of the integration-by-parts denominator is equivalent
to a nonzero derivative (`app:ch_regular:lem:finite-chain`). -/
theorem phaseGradientSquare_basis_pos_iff (e : Module.Basis ι ℝ V)
    (F : V → ℝ) (x : V) :
    0 < Localization.phaseGradientSquare e F x ↔ fderiv ℝ F x ≠ 0 := by
  have hn : 0 ≤ Localization.phaseGradientSquare e F x :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [lt_iff_le_and_ne]
  simp only [hn, true_and, ne_eq, eq_comm (a := (0 : ℝ)), phaseGradientSquare_basis_eq_zero_iff]
end Basis

/-- The tangential geometric defect and analytic denominator have
the same positive locus (`app:ch_regular:lem:finite-chain`). -/
theorem packedPhase_tangential_gradientSquare_pos_iff {ι : Type*} [Fintype ι]
    (e : Module.Basis ι ℝ (TangentialVariables E)) (xi xo : ℝ × E)
    (x : ℝ × TangentialVariables E) :
    0 < Localization.phaseGradientSquare e (fun w => packedPhase xi xo (x.1, w)) x.2 ↔
      0 < tangentialDefect xi xo x.1 x.2.1.1 x.2.1.2 x.2.2.1.1 x.2.2.1.2
        x.2.2.2.1 x.2.2.2.2 := by
  rw [phaseGradientSquare_basis_pos_iff, ne_eq, fderiv_packedPhase_tangential_eq_zero_iff,
    ← tangentialDefect_eq_zero_iff]
  exact ⟨fun hn => lt_of_le_of_ne (tangentialDefect_nonneg ..) (fun he => hn he.symm), ne_of_gt⟩

/-- The interior geometric defect and analytic denominator have the
same positive locus (`app:ch_regular:lem:finite-chain`). -/
theorem packedPhase_gradientSquare_pos_iff {ι : Type*} [Fintype ι]
    (e : Module.Basis ι ℝ (ℝ × TangentialVariables E)) (xi xo : ℝ × E)
    (x : ℝ × TangentialVariables E) :
    0 < Localization.phaseGradientSquare e (packedPhase xi xo) x ↔
      0 < fullDefect xi xo x.1 x.2.1.1 x.2.1.2 x.2.2.1.1 x.2.2.1.2
        x.2.2.2.1 x.2.2.2.2 := by
  rw [phaseGradientSquare_basis_pos_iff, ne_eq, fderiv_packedPhase_eq_zero_iff,
    ← fullDefect_eq_zero_iff]
  exact ⟨fun hn => lt_of_le_of_ne (fullDefect_nonneg ..) (fun he => hn he.symm), ne_of_gt⟩

attribute [local fun_prop] Continuous.inner

/-- Joint continuity of the tangential denominator, including external
input/output bases (`app:ch_regular:lem:finite-chain`). -/
theorem continuous_packedPhase_tangential_gradientSquare {X ι : Type*}
    [TopologicalSpace X] [Fintype ι] (e : ι → TangentialVariables E)
    (xi xo : X → ℝ × E) (x : X → ℝ × TangentialVariables E)
    (hi : Continuous xi) (ho : Continuous xo) (hx : Continuous x) :
    Continuous (fun p => Localization.phaseGradientSquare e
      (fun w => packedPhase (xi p) (xo p) ((x p).1, w)) (x p).2) := by
  simp only [Localization.phaseGradientSquare, fderiv_packedPhase_tangential_apply]
  fun_prop

/-- Joint continuity of the full denominator, including external
input/output bases (`app:ch_regular:lem:finite-chain`). -/
theorem continuous_packedPhase_gradientSquare {X ι : Type*}
    [TopologicalSpace X] [Fintype ι] (e : ι → ℝ × TangentialVariables E)
    (xi xo : X → ℝ × E) (x : X → ℝ × TangentialVariables E)
    (hi : Continuous xi) (ho : Continuous xo) (hx : Continuous x) :
    Continuous (fun p => Localization.phaseGradientSquare e (packedPhase (xi p) (xo p)) (x p)) := by
  simp only [Localization.phaseGradientSquare, fderiv_packedPhase_apply]
  fun_prop

private theorem exists_positive_minimum {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {f : X → ℝ} (hf : Continuous f)
    (hpos : ∀ p ∈ K, 0 < f p) : ∃ δ > 0, ∀ p ∈ K, δ ≤ f p := by
  rcases K.eq_empty_or_nonempty with he | hn
  · exact ⟨1, zero_lt_one, by simp [he]⟩
  · obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hn hf.continuousOn
    exact ⟨f p, hpos p hp, hmin⟩

/-- Convert a positive tangential defect on a compact parameter set
into the uniform squared-gradient gap needed by integration by parts
(`app:ch_regular:lem:finite-chain`). -/
theorem exists_packedPhase_tangential_gradient_gap {X ι : Type*}
    [TopologicalSpace X] [Fintype ι] {K : Set X} (hK : IsCompact K)
    (e : Module.Basis ι ℝ (TangentialVariables E))
    (xi xo : X → ℝ × E) (x : X → ℝ × TangentialVariables E)
    (hi : Continuous xi) (ho : Continuous xo) (hx : Continuous x)
    (hgap : ∀ p ∈ K, 0 < tangentialDefect (xi p) (xo p) (x p).1 (x p).2.1.1
      (x p).2.1.2 (x p).2.2.1.1 (x p).2.2.1.2 (x p).2.2.2.1 (x p).2.2.2.2) :
    ∃ δ > 0, ∀ p ∈ K, δ ≤ Localization.phaseGradientSquare e
      (fun w => packedPhase (xi p) (xo p) ((x p).1, w)) (x p).2 :=
  exists_positive_minimum hK (continuous_packedPhase_tangential_gradientSquare e xi xo x hi ho hx)
    (fun p hp => (packedPhase_tangential_gradientSquare_pos_iff e (xi p) (xo p) (x p)).mpr (hgap p hp))

/-- Convert a positive full defect on a compact parameter set into the
uniform squared-gradient gap needed in the interior
(`app:ch_regular:lem:finite-chain`). -/
theorem exists_packedPhase_interior_gradient_gap {X ι : Type*}
    [TopologicalSpace X] [Fintype ι] {K : Set X} (hK : IsCompact K)
    (e : Module.Basis ι ℝ (ℝ × TangentialVariables E))
    (xi xo : X → ℝ × E) (x : X → ℝ × TangentialVariables E)
    (hi : Continuous xi) (ho : Continuous xo) (hx : Continuous x)
    (hgap : ∀ p ∈ K, 0 < fullDefect (xi p) (xo p) (x p).1 (x p).2.1.1
      (x p).2.1.2 (x p).2.2.1.1 (x p).2.2.1.2 (x p).2.2.2.1 (x p).2.2.2.2) :
    ∃ δ > 0, ∀ p ∈ K, δ ≤ Localization.phaseGradientSquare e
      (packedPhase (xi p) (xo p)) (x p) :=
  exists_positive_minimum hK (continuous_packedPhase_gradientSquare e xi xo x hi ho hx)
    (fun p hp => (packedPhase_gradientSquare_pos_iff e (xi p) (xo p) (x p)).mpr (hgap p hp))

end JanetCartan.FiniteChain.Retarded
