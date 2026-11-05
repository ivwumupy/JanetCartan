module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveBudget.Expansion
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FirstDerivatives

/-!
# Local finite first-output jets

The fixed additional derivative in the gain-one paragraph of Step 3,
`app:ch_regular_base:thm:actual-calculus`. Joint words keep both physical positions
and physical covectors. The consumer is the order-zero estimate applied to the
first output amplitudes in `jc-deduce-fio-strong-sobolev`.
-/

@[expose] public noncomputable section
open Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FirstOutputJets
open FullAmplitudePrimitiveBudget
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "M" => Matrix (Fin r) (Fin r) ℂ

/-- Explicit local regularity of primitive jets, away from the zero covector.
Source: the gain-one paragraph of `app:ch_regular_base:thm:actual-calculus`. -/
def SmoothAwayZero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Field n V) : Prop :=
  ∀ w x y η, η ≠ 0 → ∀ p,
    DifferentiableAt ℝ (slice p (jet w f) x y η) (anchor p x y η)

private theorem slice_congr_awayZero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : Field n V} (h : ∀ x y η, η ≠ 0 → f x y η = g x y η)
    (p : Slot) (x y η : E) (hη : η ≠ 0) :
    slice p f x y η =ᶠ[𝓝 (anchor p x y η)] slice p g x y η := by
  cases p with
  | left => exact Filter.Eventually.of_forall (fun z ↦ h z y η hη)
  | right => exact Filter.Eventually.of_forall (fun z ↦ h x z η hη)
  | covector =>
    change ∀ᶠ z in 𝓝 η, f x y z = g x y z
    filter_upwards [isOpen_ne.mem_nhds hη] with z hz
    exact h x y z hz

private theorem derivative_congr_awayZero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : Field n V} (h : ∀ x y η, η ≠ 0 → f x y η = g x y η)
    (c : Coordinate n) (x y η : E) (hη : η ≠ 0) :
    derivative c f x y η = derivative c g x y η :=
  congrArg (fun D : E →L[ℝ] V ↦ D (EuclideanSpace.single c.2 1))
    (slice_congr_awayZero h c.1 x y η hη).fderiv_eq

/-- Local equality away from zero persists under every joint jet. Used to
identify phase-gradient jets with primitive phase jets in the gain-one budget.
Source: the gain-one paragraph of Step 3. -/
theorem jet_congr_awayZero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : Field n V} (h : ∀ x y η, η ≠ 0 → f x y η = g x y η)
    (w : List (Coordinate n)) (x y η : E) (hη : η ≠ 0) :
    jet w f x y η = jet w g x y η := by
  induction w generalizing x y η with
  | nil => exact h x y η hη
  | cons c w ih => exact derivative_congr_awayZero ih c x y η hη

/-- Ordered Leibniz terms with their multiplicities. Each derivative goes to
exactly one primitive. Source: the first-output gain-one argument in Step 3. -/
def splits : List (Coordinate n) → List (List (Coordinate n) × List (Coordinate n))
  | [] => [([], [])]
  | c :: w => (splits w).flatMap (fun p ↦ [(c :: p.1, p.2), (p.1, c :: p.2)])

/-- The finite product expansion has exactly `2^|w|` terms.
Source: gain one after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem length_splits (w : List (Coordinate n)) : (splits w).length = 2 ^ w.length := by
  induction w with
  | nil => simp [splits]
  | cons c w ih => simp [splits, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

/-- Primitive derivative orders sum to the length of the original joint word.
Source: the fixed shift in the gain-one paragraph of Step 3. -/
theorem lengths_split {w : List (Coordinate n)} {p : List (Coordinate n) × List (Coordinate n)}
    (hp : p ∈ splits w) : p.1.length + p.2.length = w.length := by
  induction w generalizing p with
  | nil => simp only [splits, List.mem_singleton] at hp; subst p; rfl
  | cons c w ih =>
    obtain ⟨q, hq, hp⟩ := List.mem_flatMap.mp hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp only [List.length_cons]
    all_goals have := ih hq; omega

private theorem derivative_product_at (c : Coordinate n) (f : Field n ℂ) (g : Field n M)
    (x y η : E)
    (hf : DifferentiableAt ℝ (slice c.1 f x y η) (anchor c.1 x y η))
    (hg : DifferentiableAt ℝ (slice c.1 g x y η) (anchor c.1 x y η)) :
    derivative c (multiply f g) x y η =
      derivative c f x y η • g x y η + f x y η • derivative c g x y η := by
  have hs : slice c.1 f x y η (anchor c.1 x y η) = f x y η := by cases c.1 <;> rfl
  have ht : slice c.1 g x y η (anchor c.1 x y η) = g x y η := by cases c.1 <;> rfl
  unfold derivative partialDeriv
  rw [slice_multiply, fderiv_fun_smul hf hg]
  change slice c.1 f x y η (anchor c.1 x y η) •
      (fderiv ℝ (slice c.1 g x y η) (anchor c.1 x y η)) (EuclideanSpace.single c.2 1) +
    (fderiv ℝ (slice c.1 f x y η) (anchor c.1 x y η)) (EuclideanSpace.single c.2 1) •
      slice c.1 g x y η (anchor c.1 x y η) = _
  rw [hs, ht]
  exact add_comm _ _

private theorem differentiable_sum_at (p : Slot) (l : List (Field n M)) (x y η : E)
    (h : ∀ f ∈ l, DifferentiableAt ℝ (slice p f x y η) (anchor p x y η)) :
    DifferentiableAt ℝ (slice p l.sum x y η) (anchor p x y η) := by
  induction l with
  | nil => simp
  | cons f l ih =>
    simp only [List.sum_cons, slice_add]
    exact (h f (by simp)).add (ih (fun g hg ↦ h g (by simp [hg])))

private theorem derivative_sum_at (c : Coordinate n) (l : List (Field n M)) (x y η : E)
    (h : ∀ f ∈ l, DifferentiableAt ℝ (slice c.1 f x y η) (anchor c.1 x y η)) :
    derivative c l.sum x y η = (l.map (fun f ↦ derivative c f x y η)).sum := by
  induction l with
  | nil => simp
  | cons f l ih =>
    have hl := differentiable_sum_at c.1 l x y η (fun g hg ↦ h g (by simp [hg]))
    simp only [List.sum_cons, List.map_cons]
    have hd : derivative c (f + l.sum) x y η =
        derivative c f x y η + derivative c l.sum x y η := by
      simp only [derivative, slice_add, partialDeriv,
        fderiv_add (h f (by simp)) hl, add_apply]
    rw [hd, ih (fun g hg ↦ h g (by simp [hg]))]

/-- Actual finite Leibniz formula, valid away from zero without a globally smooth
phase extension. Source: gain one in `app:ch_regular_base:thm:actual-calculus`. -/
theorem jet_multiply (f : Field n ℂ) (A : FullAmplitude n r)
    (hf : SmoothAwayZero f) (hA : SmoothAwayZero A)
    (w : List (Coordinate n)) (x y η : E) (hη : η ≠ 0) :
    jet w (multiply f A) x y η =
      ((splits w).map (fun p ↦ jet p.1 f x y η • jet p.2 A x y η)).sum := by
  induction w generalizing x y η with
  | nil => simp [splits, multiply]
  | cons c w ih =>
    let l := (splits w).map (fun p ↦ multiply (jet p.1 f) (jet p.2 A))
    have he : ∀ x y η, η ≠ 0 → jet w (multiply f A) x y η = l.sum x y η := by
      intro x y η hη
      rw [ih x y η hη]
      change _ = ((splits w).map (fun p ↦ multiply (jet p.1 f) (jet p.2 A))).sum x y η
      generalize splits w = ps
      induction ps with
      | nil => rfl
      | cons p ps ih =>
        simpa only [List.map_cons, List.sum_cons, Pi.add_apply, multiply] using
          congrArg (jet p.1 f x y η • jet p.2 A x y η + ·) ih
    rw [jet_cons, derivative_congr_awayZero he c x y η hη]
    rw [derivative_sum_at]
    · simp only [l, List.map_map, Function.comp_def]
      simp_rw [derivative_product_at c _ _ x y η (hf _ x y η hη c.1) (hA _ x y η hη c.1)]
      simp [splits, List.flatMap_def, List.sum_flatten, List.map_map, Function.comp_def]
    · intro g hg
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp hg
      rw [slice_multiply]
      exact (hf p.1 x y η hη c.1).smul (hA p.2 x y η hη c.1)

private theorem sum_fields_apply (l : List (Field n M)) (x y η : E) :
    l.sum x y η = (l.map (fun f ↦ f x y η)).sum := by
  induction l with
  | nil => rfl
  | cons f l ih => simpa only [List.sum_cons, List.map_cons, Pi.add_apply] using congrArg (f x y η + ·) ih

/-- Primitive product jets remain smooth on the punctured covector domain.
Source: the gain-one argument of `app:ch_regular_base:thm:actual-calculus`. -/
theorem SmoothAwayZero.mulField {f : Field n ℂ} {A : FullAmplitude n r}
    (hf : SmoothAwayZero f) (hA : SmoothAwayZero A) : SmoothAwayZero (multiply f A) := by
  intro w x y η hη p
  let l := (splits w).map (fun q ↦ FullAmplitudePrimitiveBudget.multiply (jet q.1 f) (jet q.2 A))
  have he : ∀ x y η, η ≠ 0 → jet w (multiply f A) x y η = l.sum x y η := by
    intro x y η hη
    rw [jet_multiply f A hf hA w x y η hη, sum_fields_apply]
    simp only [l, List.map_map, Function.comp_def, multiply]
  apply (slice_congr_awayZero he p x y η hη).differentiableAt_iff.mpr
  apply differentiable_sum_at
  intro g hg
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hg
  rw [slice_multiply]
  exact (hf q.1 x y η hη p).smul (hA q.2 x y η hη p)

/-- Ordered words compose by concatenation; appending the output derivative
costs exactly one primitive derivative. Source: the gain-one paragraph in Step 3. -/
theorem jet_append {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w v : List (Coordinate n)) (f : Field n V) : jet (w ++ v) f = jet w (jet v f) := by
  induction w with
  | nil => rfl
  | cons c w ih => simp only [List.cons_append, jet_cons, ih]

/-- Differentiating a primitive once preserves local smoothness away from zero.
Source: the gain-one paragraph in Step 3. -/
theorem SmoothAwayZero.derivative {A : FullAmplitude n r} (hA : SmoothAwayZero A)
    (c : Coordinate n) : SmoothAwayZero (derivative c A) := by
  intro w x y η hη p
  simpa only [jet_append, jet_cons, jet_nil] using hA (w ++ [c]) x y η hη p

/-- Actual addition of local jets; used only to assemble the two first-output
terms. Source: gain one after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem jet_add (A B : FullAmplitude n r) (hA : SmoothAwayZero A) (hB : SmoothAwayZero B)
    (w : List (Coordinate n)) (x y η : E) (hη : η ≠ 0) :
    jet w (A + B) x y η = jet w A x y η + jet w B x y η := by
  induction w generalizing x y η with
  | nil => rfl
  | cons c w ih =>
    rw [jet_cons, derivative_congr_awayZero ih c x y η hη]
    change derivative c (jet w A + jet w B) x y η = _
    simp only [derivative, slice_add, partialDeriv,
      fderiv_add (hA w x y η hη c.1) (hB w x y η hη c.1), add_apply]
    rfl

/-- Finite primitive formula for a first output amplitude. The derivative term
uses `|w|+1` amplitude derivatives; every product has total primitive order
`|w|+1` when the scalar is a first phase derivative.
Source: the gain-one paragraph of `app:ch_regular_base:thm:actual-calculus`. -/
theorem jet_firstOutput (A : FullAmplitude n r) (f : Field n ℂ) (c : Coordinate n)
    (hA : SmoothAwayZero A) (hf : SmoothAwayZero f)
    (w : List (Coordinate n)) (x y η : E) (hη : η ≠ 0) :
    jet w (derivative c A + multiply f A) x y η =
      jet (w ++ [c]) A x y η +
        ((splits w).map (fun p ↦ jet p.1 f x y η • jet p.2 A x y η)).sum := by
  rw [jet_add _ _ (hA.derivative c) (hf.mulField hA) w x y η hη,
    jet_multiply f A hf hA w x y η hη, jet_append]
  rfl

/-- First phase derivative in the forward output amplitude, with its physical
covector and the factor `i` intact. Source: gain one in Step 3. -/
def phaseOutputCoefficient (S : E → E → ℝ) (i : Fin n) : Field n ℂ :=
  fun x _ η ↦ Complex.I * ((partialDeriv (fun z ↦ S z η) x i : ℝ) : ℂ)

/-- The finite jet formula for the actual forward first output amplitude.
Source: gain one after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem jet_graphFirstOutputAmplitude (S : E → E → ℝ) (A : FullAmplitude n r) (i : Fin n)
    (hA : SmoothAwayZero A) (hS : SmoothAwayZero (phaseOutputCoefficient S i))
    (w : List (Coordinate n)) (x y η : E) (hη : η ≠ 0) :
    jet w (graphFirstOutputAmplitude S A i) x y η =
      jet (w ++ [(.left, i)]) A x y η +
        ((splits w).map (fun p ↦ jet p.1 (phaseOutputCoefficient S i) x y η •
          jet p.2 A x y η)).sum := by
  have he : graphFirstOutputAmplitude S A i =
      derivative (.left, i) A + multiply (phaseOutputCoefficient S i) A := by
    funext x y η
    simp only [graphFirstOutputAmplitude, derivative, phaseOutputCoefficient, multiply,
      slice, anchor, Pi.add_apply]
  rw [he]
  exact jet_firstOutput A _ (.left, i) hA hS w x y η hη

/-- Each forward product spends at most one additional primitive derivative,
independently of the requested Sobolev order. Source: gain one in Step 3. -/
theorem firstOutput_primitive_order {w : List (Coordinate n)}
    {p : List (Coordinate n) × List (Coordinate n)} (hp : p ∈ splits w) :
    (p.1.length + 1) + p.2.length = w.length + 1 := by
  have := lengths_split hp
  omega

end JanetCartan.FourierIntegral.FirstOutputJets
