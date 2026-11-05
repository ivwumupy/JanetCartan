module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.LocalBranchBounds.Calculus
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FirstOutputBounds.WeightedJets
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveProfiles.NormalizedSeminorms
/-!
# Ordered physical jets on normalized charts

This connects the literal ordered words in the weighted branch bounds to joint
Fréchet derivatives, retaining both physical positions and all covector slots.
It supplies the primitive-jet inputs of the strong forward and adjoint estimates
in Step 3 of `app:ch_regular_base:thm:actual-calculus`.
-/

@[expose] public noncomputable section
open scoped ContDiff
open Filter
namespace JanetCartan.FourierIntegral.PrimitiveProfiles
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- The joint coordinate direction for Step 3 of
`app:ch_regular_base:thm:actual-calculus`, with the two positions distinct. -/
def coordinateDirection (c : Coordinate n) : Point n :=
  match c.1 with
  | .left => ((EuclideanSpace.single c.2 1, 0), 0)
  | .right => ((0, EuclideanSpace.single c.2 1), 0)
  | .covector => ((0, 0), EuclideanSpace.single c.2 1)

/-- The actual slice derivative equals the joint directional derivative.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem derivative_eq_fderiv {f : Field n F} {p : Point n}
    (hf : DifferentiableAt ℝ (uncurry f) p) (c : Coordinate n) :
    uncurry (derivative c f) p = fderiv ℝ (uncurry f) p (coordinateDirection c) := by
  rcases c with ⟨c, i⟩
  cases c with
  | left =>
    have h := hf.hasFDerivAt.comp (f := fun z ↦ ((z, p.1.2), p.2)) p.1.1
      (((hasFDerivAt_id p.1.1).prodMk (hasFDerivAt_const p.1.2 p.1.1)).prodMk
        (hasFDerivAt_const p.2 p.1.1))
    exact congrArg (fun L ↦ L (EuclideanSpace.single i 1)) h.fderiv
  | right =>
    have h := hf.hasFDerivAt.comp (f := fun z ↦ ((p.1.1, z), p.2)) p.1.2
      (((hasFDerivAt_const p.1.1 p.1.2).prodMk (hasFDerivAt_id p.1.2)).prodMk
        (hasFDerivAt_const p.2 p.1.2))
    exact congrArg (fun L ↦ L (EuclideanSpace.single i 1)) h.fderiv
  | covector =>
    have h := hf.hasFDerivAt.comp (f := fun z ↦ (p.1, z)) p.2
      ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))
    exact congrArg (fun L ↦ L (EuclideanSpace.single i 1)) h.fderiv

/-- Ordered primitive words are evaluations of the joint Fréchet derivative,
in the original order. Source: Step 3 of the actual-calculus theorem. -/
theorem jet_eq_iteratedFDeriv {f : Field n F} {U : Set (Point n)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ (uncurry f) U)
    (w : List (Coordinate n)) {p : Point n} (hp : p ∈ U) :
    uncurry (jet w f) p = iteratedFDeriv ℝ w.length (uncurry f) p
      (fun i ↦ coordinateDirection (w.get i)) := by
  induction w generalizing p with
  | nil => simp [uncurry]
  | cons c w ih =>
    rw [jet_cons, derivative_eq_fderiv
      ((contDiffAt_jet (hf.contDiffAt (hU.mem_nhds hp)) w).differentiableAt (by simp))]
    have he : uncurry (jet w f) =ᶠ[nhds p]
        (fun p ↦ iteratedFDeriv ℝ w.length (uncurry f) p
          (fun i ↦ coordinateDirection (w.get i))) :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hp) (fun q hq ↦ ih hq)
    rw [he.fderiv_eq]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ w.length (uncurry f)) p :=
      (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top w.length)
    exact (hd.iteratedFDeriv_succ_apply_left'
      (m := fun i ↦ coordinateDirection ((c :: w).get i))).symm
/-- Coordinate directions have unit norm in the joint product space used
for `app:ch_regular_base:eq:fio-input`. -/
theorem norm_coordinateDirection (c : Coordinate n) : ‖coordinateDirection c‖ = 1 := by
  rcases c with ⟨c, i⟩
  have h : ‖(EuclideanSpace.single i 1 : Euclidean n)‖ = 1 :=
    EuclideanSpace.orthonormal_single.norm_eq_one i
  cases c <;> simp [coordinateDirection, Prod.norm_def, h]

/-- The positions of covector letters in a joint derivative word. Source:
Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
def frequencySlots (w : List (Coordinate n)) : Finset (Fin w.length) :=
  Finset.univ.filter fun i ↦ (w.get i).1 = .covector

/-- The existing `frequencyOrder` is exactly the number of covector slots,
so the normalized weight agrees with `StrongAssembly`. Source: Step 3. -/
theorem card_frequencySlots (w : List (Coordinate n)) :
    (frequencySlots w).card = FirstOutputJets.frequencyOrder w := by
  simp only [frequencySlots, Finset.card_filter, FirstOutputJets.frequencyOrder]
  induction w with
  | nil => simp
  | cons c w ih =>
    simp only [List.length_cons, Fin.sum_univ_succ, List.get_eq_getElem,
      List.getElem_cons_zero, Fin.val_zero, Fin.val_succ, List.getElem_cons_succ,
      List.countP_cons]
    simp only [List.get_eq_getElem] at ih
    rw [ih]
    cases c with
    | mk c i => cases c <;> simp [Nat.add_comm]

/-- Only the covector letters contribute frequency weights; neither physical
position does. Source: Step 3 of the actual-calculus theorem. -/
theorem coordinateDirection_slots (w : List (Coordinate n)) (i : Fin w.length) :
    if i ∈ frequencySlots w then (coordinateDirection (w.get i)).1 = 0
    else (coordinateDirection (w.get i)).2 = 0 := by
  simp only [frequencySlots, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases h : w.get i with ⟨c, j⟩
  cases c <;> simp [coordinateDirection]

/-- The exact weighted ordered-jet bound consumed by `StrongAssembly`, from
the actual normalized seminorm of the complete field. Matrix amplitudes and
scalar primitives use the same statement. Source: `app:ch_regular_base:eq:fio-input`. -/
theorem weighted_jet_le_normalizedSeminorm
    (z : Point n) {ρ : ℝ} {U V : Set (Point n)}
    (hU : IsOpen U) (hV : IsOpen V) (hball : Metric.closedBall z ρ ⊆ U)
    {f : Field n F} (hf : ContDiffOn ℝ ∞ (uncurry f) V)
    (hn : ∀ R : ℝ, 1 ≤ R → ContDiffOn ℝ ∞ (normalizedField R (uncurry f)) U)
    (w : List (Coordinate n))
    (hb : BoundedNormalizedSeminorm (Metric.closedBall z ρ) w.length (uncurry f))
    {R : ℝ} (hR : 1 ≤ R) (p : Point n) (hp : p ∈ Metric.closedBall z ρ)
    (hpV : (p.1, R • p.2) ∈ V) :
    R ^ FirstOutputJets.frequencyOrder w * ‖uncurry (jet w f) (p.1, R • p.2)‖ ≤
      normalizedSeminorm (Metric.closedBall z ρ) w.length (uncurry f) := by
  rw [jet_eq_iteratedFDeriv hV hf w hpV, ← card_frequencySlots]
  exact weighted_mixedJet_le_normalizedSeminorm z hU hV hball
    (hf.of_le (by exact_mod_cast (le_top : (w.length : ℕ∞) ≤ ⊤)))
    (fun R hR ↦ (hn R hR).of_le (by exact_mod_cast (le_top : (w.length : ℕ∞) ≤ ⊤)))
    hb hR p hp hpV (frequencySlots w) (fun i ↦ coordinateDirection (w.get i))
    (coordinateDirection_slots w) (fun i ↦ (norm_coordinateDirection (w.get i)).le)
end JanetCartan.FourierIntegral.PrimitiveProfiles
