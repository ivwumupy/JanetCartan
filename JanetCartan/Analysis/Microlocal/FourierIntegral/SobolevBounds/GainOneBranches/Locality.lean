module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.GainOneBranches.FirstOutput

/-!
# First-output smoothness and support on the actual carrier

Only the punctured covector domain and the actual mixed inverse region enter
the gain-one argument after `app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.GainOneBranches
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local FirstOutputJets
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- Ordinary local smoothness of the original amplitude produces the joint
jet regularity used in the first-output Leibniz formula. Source: `app:ch_regular_base:thm:actual-calculus`, gain one. -/
theorem smoothAwayZero_of_joint (A : FullAmplitude n r)
    (hA : ∀ p : Point n, p.2 ≠ 0 → ContDiffAt ℝ ∞ (uncurry A) p) :
    SmoothAwayZero A := by
  apply smoothAwayZero_of_contDiffAt
  intro x y η hη
  exact (hA ((x, y), η) hη).comp (x, y, η)
    ((contDiffAt_fst.prodMk contDiffAt_snd.fst).prodMk contDiffAt_snd.snd)

/-- The actual forward first-output amplitude is smooth away from zero;
there is no global homogeneous extension hypothesis. Source: `app:ch_regular_base:thm:actual-calculus`, gain one. -/
theorem smooth_graphFirstOutput (S : E → E → ℝ) (A : FullAmplitude n r)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hA : ∀ p : Point n, p.2 ≠ 0 → ContDiffAt ℝ ∞ (uncurry A) p)
    (i : Fin n) (p : Point n) (hp : p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (uncurry (graphFirstOutputAmplitude S A i)) p := by
  have hs : ContDiffAt ℝ ∞ (uncurry (fun x (_ : E) η ↦ S x η)) p :=
    (hS p.1.1 p.2 hp).comp p (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hd := contDiffAt_derivative hs (.left, i)
  have hc : ContDiffAt ℝ ∞ (uncurry (phaseOutputCoefficient S i)) p :=
    contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp p hd)
  exact (contDiffAt_derivative (hA p hp) (.left, i)).add (hc.smul (hA p hp))

/-- Smoothness for the literal adjoint keeps the original coordinate order
and conjugates the amplitude exactly once. Source: `app:ch_regular_base:thm:actual-calculus`, gain one. -/
theorem smooth_adjointFirstOutput (A : FullAmplitude n r)
    (hA : ∀ p : Point n, p.2 ≠ 0 → ContDiffAt ℝ ∞ (uncurry A) p)
    (i : Fin n) (p : Point n) (hp : p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (uncurry (adjointFirstOutputAmplitude A i)) p := by
  have ha : ContDiffAt ℝ ∞ (uncurry (fun x y η ↦ (A x y η).conjTranspose)) p :=
    (starL ℝ : Matrix (Fin r) (Fin r) ℂ ≃L[ℝ] Matrix (Fin r) (Fin r) ℂ).contDiff.contDiffAt.comp p (hA p hp)
  have hc : ContDiffAt ℝ ∞ (uncurry (covectorOutputCoefficient i)) p := by
    exact (((Complex.I • Complex.ofRealCLM).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i)).contDiff.contDiffAt).comp p contDiffAt_snd
  exact (contDiffAt_derivative ha (.right, i)).add (hc.smul ha)

/-- First differentiation of the full graph cannot enlarge its closed support.
This localizes all later branch jets to the original masks. Source: gain one,
following `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem support_graphFirstOutput (S : E → E → ℝ) (A : FullAmplitude n r) (i : Fin n) :
    tsupport (uncurry (graphFirstOutputAmplitude S A i)) ⊆ tsupport (uncurry A) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_contra hn
  have ha : uncurry A p = 0 := image_eq_zero_of_notMem_tsupport hn
  have hd : uncurry (derivative (.left, i) A) p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm ↦ hn (tsupport_derivative_subset _ A hm))
  apply hp
  change uncurry (derivative (.left, i) A) p + _ • uncurry A p = 0
  rw [ha, hd, smul_zero, add_zero]

/-- Literal first-output differentiation also preserves the original support,
including the source mask. Source: `app:ch_regular_base:eq:actual-adjoint-trade`,
gain-one paragraph. -/
theorem support_adjointFirstOutput (A : FullAmplitude n r) (i : Fin n) :
    tsupport (uncurry (adjointFirstOutputAmplitude A i)) ⊆ tsupport (uncurry A) := by
  have hstar : tsupport (uncurry (fun x y η ↦ (A x y η).conjTranspose)) ⊆
      tsupport (uncurry A) := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro p hp
    apply subset_tsupport (uncurry A)
    intro hz
    exact hp (by change (uncurry A p).conjTranspose = 0; rw [hz, Matrix.conjTranspose_zero])
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_contra hn
  have ha : uncurry (fun x y η ↦ (A x y η).conjTranspose) p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm ↦ hn (hstar hm))
  have hd : uncurry (derivative (.right, i) (fun x y η ↦ (A x y η).conjTranspose)) p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm ↦ hn (hstar (tsupport_derivative_subset _ _ hm)))
  apply hp
  change uncurry (derivative (.right, i) (fun x y η ↦ (A x y η).conjTranspose)) p +
    _ • uncurry (fun x y η ↦ (A x y η).conjTranspose) p = 0
  rw [ha, hd, smul_zero, add_zero]

end JanetCartan.FourierIntegral.GainOneBranches
