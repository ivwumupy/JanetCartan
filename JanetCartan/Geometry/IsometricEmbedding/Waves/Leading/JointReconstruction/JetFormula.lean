module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Reconstruction.FieldBounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition

/-!
# Joint jets for the actual leading reconstruction

For `app:ch_waves:eq:joint-tame`, the geometric input is the physical second
jet of the immersion, the value and physical first derivative of the joint
covector, and the joint phase covector. The latter two fields may depend on
any finite-dimensional parameter space. These formulas use the existing
normal inverse and reconstruction, in the shared Frobenius convention.

The compact-range and quantitative estimates consume these definitions. No
compact containment, derivative bound, or existence of transport is asserted
by the definitions.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open Set

namespace JanetCartan.LeadingWave.JointReconstruction

open GeometricProfile AmbientResponse

/-- The finite joint input for `app:ch_waves:eq:joint-tame`. The first factor
is the already published reconstruction jet; the last is the phase covector. -/
abbrev JointJet (n N : ℕ) := ReconstructionJet n N × Euclidean n

/-- The literal joint jet for `app:ch_waves:eq:joint-tame`. Restricting the
joint differential to the physical variables costs only one derivative of `b`. -/
def jointJet {n N : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : Euclidean n → Euclidean N) (b ξ : Euclidean n × Z → Euclidean n)
    (p : Euclidean n × Z) : JointJet n N :=
  ((secondJet F p.1, b p,
    (fderiv ℝ b p).comp (ContinuousLinearMap.inl ℝ (Euclidean n) Z)), ξ p)

/-- The actual principal normal as a finite-jet expression
(`app:ch_waves:eq:arbitrary-b-amplitudes`). -/
def principalNormalValue {n N : ℕ} (q : JointJet n N) : Euclidean N :=
  secondJetNormalInverse q.1.1 (symmetricProduct q.2 q.1.2.1)

/-- The actual principal matrix as a finite-jet expression
(`app:ch_waves:eq:arbitrary-b-amplitudes`). -/
def principalMatrixValue {n N : ℕ} (q : JointJet n N) : Matrix (Fin N) (Fin n) ℝ :=
  principalMatrix (principalNormalValue q) q.2

private def matrixOfEntries (m n : ℕ) :
    (Fin m → Fin n → ℝ) →L[ℝ] Matrix (Fin m) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap LinearMap.id

/-- The principal-normal coefficient in `app:ch_waves:eq:joint-tame` is
smooth on the same immersion and normal-rank jet domain as reconstruction. -/
theorem contDiffAt_principalNormalValue {n N : ℕ} {q : JointJet n N}
    (hi : Function.Injective q.1.1.1)
    (hrank : Set.range (secondJetNormalMap q.1.1) =
      ((LinearMap.range q.1.1.1.toLinearMap)ᗮ : Set (Euclidean N))) :
    ContDiffAt ℝ ∞ (@principalNormalValue n N) q := by
  have hξ (i : Fin n) : ContDiffAt ℝ ∞ (fun p : JointJet n N ↦ p.2 i) q :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.comp q contDiffAt_snd
  have hb (i : Fin n) : ContDiffAt ℝ ∞ (fun p : JointJet n N ↦ p.1.2.1 i) q :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.comp q contDiffAt_fst.snd.fst
  have hs : ContDiffAt ℝ ∞ (fun p : JointJet n N ↦ symmetricProduct p.2 p.1.2.1) q := by
    apply (matrixOfEntries n n).contDiff.contDiffAt.comp q
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    exact ((hξ i |>.mul (hb j)).add (hb i |>.mul (hξ j))).div_const 2
  exact ((contDiffAt_secondJetNormalInverse (firstJetMetric_isUnit_of_injective hi)
    (secondJetAmbientOperator_isUnit hi hrank)).comp q contDiffAt_fst.fst).clm_apply hs

/-- The literal principal matrix is smooth on the same admissible jet domain
(`app:ch_waves:eq:joint-tame`), including the shared Frobenius matrix norm. -/
theorem contDiffAt_principalMatrixValue {n N : ℕ} {q : JointJet n N}
    (hi : Function.Injective q.1.1.1)
    (hrank : Set.range (secondJetNormalMap q.1.1) =
      ((LinearMap.range q.1.1.1.toLinearMap)ᗮ : Set (Euclidean N))) :
    ContDiffAt ℝ ∞ (@principalMatrixValue n N) q := by
  have hν := contDiffAt_principalNormalValue hi hrank
  apply (matrixOfEntries N n).contDiff.contDiffAt.comp q
  apply contDiffAt_pi.mpr
  intro a
  apply contDiffAt_pi.mpr
  intro i
  exact (((EuclideanSpace.proj (𝕜 := ℝ) a).contDiff.contDiffAt.comp q hν).mul
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.comp q contDiffAt_snd)).neg

/-- Reconstruction uses exactly the first factor of the common joint jet
(`app:ch_waves:eq:joint-tame`). -/
theorem contDiffAt_reconstructionValue {n N : ℕ} {q : JointJet n N}
    (hi : Function.Injective q.1.1.1)
    (hrank : Set.range (secondJetNormalMap q.1.1) =
      ((LinearMap.range q.1.1.1.toLinearMap)ᗮ : Set (Euclidean N))) :
    ContDiffAt ℝ ∞ (fun p : JointJet n N ↦ reconstructionJetValue p.1) q :=
  (contDiffAt_reconstructionJetValue hi hrank).comp q contDiffAt_fst

/-- Physical differentiation of the joint covector is restriction of its
joint differential (`app:ch_waves:eq:reconstruction`). -/
theorem fderiv_physical_slice {n : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {b : Euclidean n × Z → Euclidean n} {p : Euclidean n × Z}
    (hb : DifferentiableAt ℝ b p) :
    fderiv ℝ (fun y ↦ b (y, p.2)) p.1 =
      (fderiv ℝ b p).comp (ContinuousLinearMap.inl ℝ (Euclidean n) Z) := by
  exact (hb.hasFDerivAt.comp p.1
    ((hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1))).fderiv

/-- The common joint jet agrees with the published reconstruction jet of
each physical slice (`app:ch_waves:eq:reconstruction`). -/
theorem jointJet_fst_eq {n N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : Euclidean n → Euclidean N) {b : Euclidean n × Z → Euclidean n}
    (ξ : Euclidean n × Z → Euclidean n) {p : Euclidean n × Z}
    (hb : DifferentiableAt ℝ b p) :
    (jointJet F b ξ p).1 = reconstructionJet F (fun y ↦ b (y, p.2)) p.1 := by
  simp only [jointJet, reconstructionJet, fderiv_physical_slice hb]

/-- The actual common jet is smooth on the supplied open product domain.
No extension or global smoothness is a premise (`app:ch_waves:eq:joint-tame`). -/
theorem contDiffOn_jointJet {n N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} {b ξ : Euclidean n × Z → Euclidean n}
    {U : Set (Euclidean n)} {V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F U) (hb : ContDiffOn ℝ ∞ b (U ×ˢ V))
    (hξ : ContDiffOn ℝ ∞ ξ (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (jointJet F b ξ) (U ×ˢ V) := by
  have hdF : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by simp)
  have hddF : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ F)) U :=
    hdF.fderiv_of_isOpen hU (by simp)
  have hJF : ContDiffOn ℝ ∞ (fun p : Euclidean n × Z ↦ secondJet F p.1) (U ×ˢ V) :=
    (hdF.prodMk hddF).comp contDiffOn_fst (fun _ hp ↦ hp.1)
  have hdb : ContDiffOn ℝ ∞ (fderiv ℝ b) (U ×ˢ V) :=
    hb.fderiv_of_isOpen (hU.prod hV) (by simp)
  exact (hJF.prodMk (hb.prodMk (hdb.clm_comp contDiffOn_const))).prodMk hξ

end JanetCartan.LeadingWave.JointReconstruction
