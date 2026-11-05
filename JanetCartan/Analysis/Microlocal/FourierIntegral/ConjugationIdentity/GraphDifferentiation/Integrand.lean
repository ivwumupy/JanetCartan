module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.Kernel
public import JanetCartan.Analysis.Microlocal.FourierIntegral.Differential
public import JanetCartan.Analysis.Microlocal.FourierIntegral.Transport
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Pointwise graph differentiation

The chain and product rules for the integrand in
`app:ch_regular_base:eq:direct-graph-identity`, preserving matrix order.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.GraphDifferentiation
variable {n r : ℕ}

/-- Joint smoothness of the graph integrand on the open output domain, used by
`physicalOperator_graphOperator` (`app:ch_regular_base:eq:direct-graph-identity`). -/
theorem contDiffOn_integrand {U : Set (Euclidean n)}
    {S : Euclidean n → Euclidean n → ℝ}
    {b : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    {v : Euclidean n → Fin r → ℂ}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ univ))
    (hb : ContDiffOn ℝ ∞ (Function.uncurry b) (U ×ˢ univ))
    (hv : ContDiff ℝ ∞ v) :
    ContDiffOn ℝ ∞ (fun p : Euclidean n × (Euclidean n × Euclidean n) ↦
      graphOscillation S p.1 p.2.2 p.2.1 • (b p.1 p.2.1).mulVec (v p.2.2))
      (U ×ˢ univ) := by
  have hm : MapsTo (fun p : Euclidean n × (Euclidean n × Euclidean n) ↦
      (p.1, p.2.1)) (U ×ˢ univ) (U ×ˢ univ) := fun _ hp ↦ ⟨hp.1, mem_univ _⟩
  have hS' := hS.comp (contDiffOn_fst.prodMk contDiffOn_snd.fst) hm
  have hb' := hb.comp (contDiffOn_fst.prodMk contDiffOn_snd.fst) hm
  have hv' : ContDiffOn ℝ ∞ (fun p : Euclidean n × (Euclidean n × Euclidean n) ↦
      v p.2.2) (U ×ˢ univ) := hv.contDiffOn.comp contDiffOn_snd.snd (mapsTo_univ _ _)
  have hphase : ContDiffOn ℝ ∞ (fun p : Euclidean n × (Euclidean n × Euclidean n) ↦
      graphOscillation S p.1 p.2.2 p.2.1) (U ×ˢ univ) :=
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hS'.sub (contDiffOn_snd.snd.inner ℝ contDiffOn_snd.fst)))).cexp
  let M : Matrix (Fin r) (Fin r) ℂ →L[ℝ] (Fin r → ℂ) →L[ℝ] (Fin r → ℂ) :=
    (Matrix.mulVecBilin ℝ ℝ).toContinuousBilinearMap
  exact hphase.smul ((M.contDiff.comp_contDiffOn hb').clm_apply hv')

/-- The actual output derivative of the graph oscillation in
`app:ch_regular_base:eq:direct-graph-identity`. -/
theorem partialDeriv_graphOscillation
    (S : Euclidean n → Euclidean n → ℝ) (x y η : Euclidean n)
    (hS : DifferentiableAt ℝ (fun z ↦ S z η) x) (j : Fin n) :
    partialDeriv (fun z ↦ graphOscillation S z y η) x j =
      graphOscillation S x y η * (Complex.I * ((partialDeriv (fun z ↦ S z η) x j : ℝ) : ℂ)) := by
  have hd := (((Complex.ofRealCLM.hasFDerivAt.comp x
    (hS.hasFDerivAt.sub_const (inner ℝ y η))).const_mul Complex.I).cexp).fderiv
  simpa [graphOscillation, partialDeriv, Function.comp_def] using
    congrArg (fun L : Euclidean n →L[ℝ] ℂ ↦ L (EuclideanSpace.single j 1)) hd

/-- Pointwise physical differentiation of a source-independent graph amplitude.
The matrix product and transport remainder are exactly those of
`app:ch_regular_base:eq:direct-graph-identity`. -/
theorem physicalOperator_integrand
    (A : Euclidean n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (B : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (S : Euclidean n → Euclidean n → ℝ)
    (b : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (v : Euclidean n → Fin r → ℂ) (x y η : Euclidean n)
    (hS : DifferentiableAt ℝ (fun z ↦ S z η) x)
    (hb : DifferentiableAt ℝ (fun z ↦ b z η) x) :
    physicalOperator A B (fun z ↦ graphOscillation S z y η • (b z η).mulVec (v y)) x =
      graphOscillation S x y η •
        (((∑ j, ((partialDeriv (fun z ↦ S z η) x j : ℝ) : ℂ) • A x j) * b x η +
          transportRemainder (A x) (fun j ↦ partialDeriv (fun z ↦ b z η) x j)
            (B x) (b x η)).mulVec (v y)) := by
  let M : Matrix (Fin r) (Fin r) ℂ →L[ℝ] (Fin r → ℂ) →L[ℝ] (Fin r → ℂ) :=
    (Matrix.mulVecBilin ℝ ℝ).toContinuousBilinearMap
  have hm : DifferentiableAt ℝ (fun z ↦ (b z η).mulVec (v y)) x :=
    (M.differentiableAt.comp x hb).clm_apply (differentiableAt_const _)
  have he : DifferentiableAt ℝ (fun z ↦ graphOscillation S z y η) x :=
    (((Complex.ofRealCLM.differentiableAt.comp x
      (hS.sub_const (inner ℝ y η))).const_mul Complex.I).cexp)
  have hd (j : Fin n) : partialDeriv (fun z ↦ (b z η).mulVec (v y)) x j =
      (partialDeriv (fun z ↦ b z η) x j).mulVec (v y) := by
    have h : partialDeriv (fun z ↦ (b z η).mulVec (v y)) x j =
        (b x η).mulVec (partialDeriv (fun _ : Euclidean n ↦ v y) x j) +
          (partialDeriv (fun z ↦ b z η) x j).mulVec (v y) :=
      congrArg (fun L : Euclidean n →L[ℝ] (Fin r → ℂ) ↦
        L (EuclideanSpace.single j 1)) (M.fderiv_of_bilinear hb (differentiableAt_const _))
    simpa [partialDeriv] using h
  simp only [physicalOperator, partialDeriv_cutoff_mul _ _ x _ he hm, hd,
    partialDeriv_graphOscillation S x y η hS, Matrix.mulVec_add, Matrix.mulVec_smul,
    Finset.sum_add_distrib, transportRemainder, Matrix.add_mulVec, Matrix.smul_mulVec,
    Finset.sum_mul, Matrix.sum_mulVec, ← Matrix.mulVec_mulVec,
    ← Finset.smul_sum]
  have hsum : (∑ j, (graphOscillation S x y η *
        (Complex.I * ((partialDeriv (fun z ↦ S z η) x j : ℝ) : ℂ))) •
        (A x j).mulVec ((b x η).mulVec (v y))) =
      (Complex.I * graphOscillation S x y η) •
        ∑ j, ((partialDeriv (fun z ↦ S z η) x j : ℝ) : ℂ) •
          (A x j).mulVec ((b x η).mulVec (v y)) := by
    simp only [Finset.smul_sum, smul_smul]
    congr 1
    funext j
    congr 1
    ring
  rw [hsum]
  simp only [smul_add, smul_smul, ← mul_assoc, neg_mul, Complex.I_mul_I,
    neg_neg, one_mul]
  module

end JanetCartan.FourierIntegral.GraphDifferentiation
