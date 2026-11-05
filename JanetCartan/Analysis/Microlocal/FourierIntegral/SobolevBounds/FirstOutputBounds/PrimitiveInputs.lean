module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FirstOutputBounds.AdjointJets

/-!
# Primitive smoothness inputs for first-output bounds

Discharge the local jet regularity from ordinary phase/amplitude smoothness,
and identify the extra phase derivative in the gain-one paragraph of
`app:ch_regular_base:thm:actual-calculus`, Step 3.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FirstOutputJets
open FullAmplitudePrimitiveBudget
variable {n r : ℕ}
local notation "E" => Euclidean n

private theorem contDiffAt_joint_derivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Field n V) (c : Coordinate n) (x y η : E)
    (h : ContDiffAt ℝ ∞ (fun p : E × (E × E) ↦ f p.1 p.2.1 p.2.2) (x, y, η)) :
    ContDiffAt ℝ ∞ (fun p : E × (E × E) ↦ derivative c f p.1 p.2.1 p.2.2) (x, y, η) := by
  rcases c with ⟨s, i⟩
  cases s with
  | left =>
    have hh : ContDiffAt ℝ ∞ (fun q : (E × (E × E)) × E ↦ f q.2 q.1.2.1 q.1.2.2)
        ((x, y, η), x) :=
      h.comp ((x, y, η), x) (contDiffAt_snd.prodMk (contDiffAt_fst.snd.fst.prodMk contDiffAt_fst.snd.snd))
    exact (hh.fderiv contDiffAt_fst (by simp)).clm_apply contDiffAt_const
  | right =>
    have hh : ContDiffAt ℝ ∞ (fun q : (E × (E × E)) × E ↦ f q.1.1 q.2 q.1.2.2)
        ((x, y, η), y) :=
      h.comp ((x, y, η), y) (contDiffAt_fst.fst.prodMk (contDiffAt_snd.prodMk contDiffAt_fst.snd.snd))
    exact (hh.fderiv contDiffAt_snd.fst (by simp)).clm_apply contDiffAt_const
  | covector =>
    have hh : ContDiffAt ℝ ∞ (fun q : (E × (E × E)) × E ↦ f q.1.1 q.1.2.1 q.2)
        ((x, y, η), η) :=
      h.comp ((x, y, η), η) (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.fst.prodMk contDiffAt_snd))
    exact (hh.fderiv contDiffAt_snd.snd (by simp)).clm_apply contDiffAt_const

/-- Ordinary joint smoothness away from zero supplies every primitive jet's
local slice regularity. Source: gain one in Step 3. -/
theorem smoothAwayZero_of_contDiffAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : Field n V)
    (h : ∀ x y η, η ≠ 0 →
      ContDiffAt ℝ ∞ (fun p : E × (E × E) ↦ f p.1 p.2.1 p.2.2) (x, y, η)) :
    SmoothAwayZero f := by
  have hj (w : List (Coordinate n)) (x y η : E) (hη : η ≠ 0) :
      ContDiffAt ℝ ∞ (fun p : E × (E × E) ↦ jet w f p.1 p.2.1 p.2.2) (x, y, η) := by
    induction w with
    | nil => exact h x y η hη
    | cons c w ih => exact contDiffAt_joint_derivative (jet w f) c x y η ih
  intro w x y η hη p
  cases p with
  | left => exact ((hj w x y η hη).comp x
      (contDiffAt_id.prodMk (contDiffAt_const.prodMk contDiffAt_const))).differentiableAt (by simp)
  | right => exact ((hj w x y η hη).comp y
      (contDiffAt_const.prodMk (contDiffAt_id.prodMk contDiffAt_const))).differentiableAt (by simp)
  | covector => exact ((hj w x y η hη).comp η
      (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))).differentiableAt (by simp)

/-- Actual local phase smoothness produces the first phase-gradient jet regularity;
no extension across the zero covector is required. Source: gain one in Step 3. -/
theorem smooth_phaseOutputCoefficient (S : E → E → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η)) (i : Fin n) :
    SmoothAwayZero (phaseOutputCoefficient S i) := by
  apply smoothAwayZero_of_contDiffAt
  intro x y η hη
  have h : ContDiffAt ℝ ∞
      (fun p : E × (E × E) ↦ S p.1 p.2.2) (x, y, η) :=
    (hS x η hη).comp (x, y, η) (contDiffAt_fst.prodMk contDiffAt_snd.snd)
  have hd := contDiffAt_joint_derivative (fun x (_ : E) η ↦ S x η) (.left, i) x y η h
  exact contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp _ hd)

/-- A primitive phase field with only the fixed unit factor `i`; its jets have the
same norms as the real phase jets. The dummy source position remains explicit.
Source: the gain-one paragraph of Step 3. -/
def phasePrimitive (S : E → E → ℝ) : Field n ℂ := fun x _ η ↦ Complex.I * (S x η : ℂ)

/-- The coefficient in the first output amplitude is exactly one physical
position derivative of the primitive phase, away from the zero covector.
Source: gain one in Step 3. -/
theorem phaseOutputCoefficient_eq_derivative (S : E → E → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (i : Fin n) (x y η : E) (hη : η ≠ 0) :
    phaseOutputCoefficient S i x y η = derivative (.left, i) (phasePrimitive S) x y η := by
  have hs := ((hS x η hη).comp x (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hd := ((Complex.I • Complex.ofRealCLM).hasFDerivAt.comp x hs.hasFDerivAt).fderiv
  exact (congrArg (fun D : E →L[ℝ] ℂ ↦ D (EuclideanSpace.single i 1)) hd).symm

/-- The extra phase derivative is literally appended to the joint primitive word.
Source: the fixed shift in the gain-one paragraph of Step 3. -/
theorem jet_phaseOutputCoefficient (S : E → E → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (i : Fin n) (w : List (Coordinate n)) (x y η : E) (hη : η ≠ 0) :
    jet w (phaseOutputCoefficient S i) x y η =
      jet (w ++ [(.left, i)]) (phasePrimitive S) x y η := by
  rw [jet_append]
  exact jet_congr_awayZero (phaseOutputCoefficient_eq_derivative S hS i) w x y η hη

/-- Primitive-input forward bound: joint amplitude and phase jets through exactly
one additional derivative imply order-zero first-output jets. All smoothness
premises are ordinary local phase/amplitude smoothness. The parent supplies these
primitive bounds from its normalized symbol seminorms, then applies its order-zero
operator theorem. Source: gain one in `app:ch_regular_base:thm:actual-calculus`. -/
theorem weighted_graphFirstOutputAmplitude_of_primitive_jets
    (S : E → E → ℝ) (A : FullAmplitude n r) (i : Fin n)
    (hA : ∀ x y η, η ≠ 0 →
      ContDiffAt ℝ ∞ (fun p : E × (E × E) ↦ A p.1 p.2.1 p.2.2) (x, y, η))
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (w : List (Coordinate n)) (x y η : E) (hη : η ≠ 0)
    (ρ a b : ℝ) (hρ : 1 ≤ ρ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAj : ∀ v, v.length ≤ w.length + 1 →
      ρ ^ frequencyOrder v * ‖jet v A x y η‖ ≤ a / ρ)
    (hSj : ∀ v, v.length ≤ w.length + 1 →
      ρ ^ frequencyOrder v * ‖jet v (phasePrimitive S) x y η‖ ≤ b * ρ) :
    ρ ^ frequencyOrder w * ‖jet w (graphFirstOutputAmplitude S A i) x y η‖ ≤
      a + (2 : ℝ) ^ w.length * (b * a) := by
  apply weighted_graphFirstOutputAmplitude_le S A i (smoothAwayZero_of_contDiffAt A hA)
    (smooth_phaseOutputCoefficient S hS i) w x y η hη ρ a b hρ ha hb hAj
  intro v hv
  rw [jet_phaseOutputCoefficient S hS i v x y η hη]
  have h := hSj (v ++ [(.left, i)]) (by simpa using Nat.add_le_add_right hv 1)
  simpa [frequencyOrder, List.countP_append] using h

/-- Primitive-input literal-adjoint bound, using only local amplitude smoothness
and its order-minus-one weighted jets through one extra derivative. Conjugate
transposition preserves the Frobenius primitive budgets. Source: gain one in
Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem weighted_adjointFirstOutputAmplitude_of_primitive_jets
    (A : FullAmplitude n r) (i : Fin n)
    (hA : ∀ x y η, η ≠ 0 →
      ContDiffAt ℝ ∞ (fun p : E × (E × E) ↦ A p.1 p.2.1 p.2.2) (x, y, η))
    (w : List (Coordinate n)) (x y η : E) (hη : η ≠ 0)
    (ρ a : ℝ) (hρ : 1 ≤ ρ) (ha : 0 ≤ a) (hηρ : ‖η‖ ≤ ρ)
    (hAj : ∀ v, v.length ≤ w.length + 1 →
      ρ ^ frequencyOrder v * ‖jet v A x y η‖ ≤ a / ρ) :
    ρ ^ frequencyOrder w * ‖jet w (adjointFirstOutputAmplitude A i) x y η‖ ≤
      a + (2 : ℝ) ^ w.length * a :=
  weighted_adjointFirstOutputAmplitude_le A i (smoothAwayZero_of_contDiffAt A hA)
    w x y η hη ρ a hρ ha hηρ hAj

end JanetCartan.FourierIntegral.FirstOutputJets
