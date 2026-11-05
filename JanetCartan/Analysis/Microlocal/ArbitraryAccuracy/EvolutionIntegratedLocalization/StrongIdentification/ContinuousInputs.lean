module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.LiteralAdjoint.IntegratedKernel
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.Kernels

/-!
# Extending finite graph realizations to continuous L² inputs

The input proof localizer need not preserve compact support. At a finite graph
cutoff, the continuous compact full kernel gives a bounded operator on all L².
Density identifies it with the primitive producer's test realization, and
compact Fubini gives its literal action on continuous L² representatives.
Consumer: localized finite elapsed kernels in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FourierIntegral.FullLowBounds NormalComparison Pseudodifferential AmplitudeBound
variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private theorem compactFullKernelOperator_ae_representative
    {k : Fin q → Fin q → E → E → ℂ}
    (hc : ∀ i j, Continuous (Function.uncurry (k i j)))
    (hs : ∀ i j, HasCompactSupport (Function.uncurry (k i j)))
    (u : H) (v : E → Fin q → ℂ)
    (he : u =ᵐ[volume] fun x ↦ WithLp.toLp 2 (v x)) :
    compactFullKernelOperator hc hs u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ ∑ j, ∫ y, k i j x y * v y j) := by
  apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
  intro i
  simp only [compactFullKernelOperator, finiteL2CoordinateIsometry_vectorMatrixL2Operator]
  refine (matrixOperator_ae_kernel _ _
    (fun i j f ↦ compactKernelOperator_ae_integral (hc i j) (hs i j) f) _ i).trans ?_
  apply Eventually.of_forall
  intro x
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [finiteL2Coordinates_apply_ae volume u j, he] with y hy hv
  rw [show (finiteL2CoordinateIsometry volume u) j y = v y j
    from hy.trans (congrArg (fun w : EuclideanSpace ℂ (Fin q) ↦ w j) hv)]

/-- The finite compact full-integrand action on tests determines its action
on every continuous L² representative. The primitive graph producer supplies
`hreal`; compact kernel construction and density discharge its extension to
the right-localized input, without assuming a realization on such inputs.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem compactEntry_test_realization_on_continuous_input
    (F : Fin q → Fin q → (E × E) × E → ℂ)
    (hc : ∀ i j, Continuous (F i j)) (hs : ∀ i j, HasCompactSupport (F i j))
    (T : H →L[ℂ] H)
    (hreal : ∀ u : graphTestSpace n q, T (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (∫ η, ∫ y, fun i ↦ ∑ j, F i j ((x, y), η) * u.val y j))
    (u : H) (v : E → Fin q → ℂ) (hv : Continuous v)
    (he : u =ᵐ[volume] fun x ↦ WithLp.toLp 2 (v x)) :
    T u =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (∫ η, ∫ y, fun i ↦ ∑ j, F i j ((x, y), η) * v y j) := by
  have hreg i j := compactEntry_integral_regular (hc i j) (hs i j)
  let k : Fin q → Fin q → E → E → ℂ := fun i j x y ↦ ∫ η, F i j ((x, y), η)
  let U := compactFullKernelOperator (k := k) (fun i j ↦ (hreg i j).1)
    (fun i j ↦ (hreg i j).2)
  have hf (w : E → Fin q → ℂ) (hw : Continuous w) (x : E) :
      WithLp.toLp 2 (fun i ↦ ∑ j, ∫ y, k i j x y * w y j) =
        WithLp.toLp 2 (∫ η, ∫ y, fun i ↦ ∑ j, F i j ((x, y), η) * w y j) := by
    apply congrArg (WithLp.toLp 2)
    funext i
    exact (compactEntry_integral_sum (fun i j p ↦ F i j ((x, p.2), p.1))
      (fun i j ↦ (hc i j).comp ((continuous_const.prodMk continuous_snd).prodMk continuous_fst))
      (fun i j ↦ compactEntry_forward_section (hs i j) x) w hw i).symm
  have hTU : T = U := by
    apply DFunLike.coe_injective
    apply denseRange_graphTestToLp.equalizer T.continuous U.continuous
    funext w
    apply Lp.ext
    exact (hreal w).trans ((compactFullKernelOperator_test_ae
      (fun i j ↦ (hreg i j).1) (fun i j ↦ (hreg i j).2) w).trans
      (Eventually.of_forall (hf (fun y ↦ (w.val y).ofLp)
        ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin q ↦ ℂ)).continuous.comp
          w.property.1.continuous)))).symm
  rw [hTU]
  exact (compactFullKernelOperator_ae_representative
    (fun i j ↦ (hreg i j).1) (fun i j ↦ (hreg i j).2) u v he).trans
    (Eventually.of_forall (hf v hv))

/-- Finite forward and literal reverse graph test realizations extend to
continuous L² representatives. The compact amplitude includes the graph
frequency cutoff and both physical masks. Thus this applies to every finite
graph sum, including its low-frequency pieces, before the quantitative shell
bound. Consumer: the right-localized finite elapsed compositions for
`app:ch_regular_base:eq:fixed-time-representation` and
`app:ch_regular:eq:chain-tail`. -/
theorem compactOrientedGraph_test_realization_on_continuous_input
    (backward : Bool) (S : E → E → ℝ) (A : FullAmplitude n q)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (E × E) × E ↦ A p.1.1 p.1.2 p.2))
    (hs : HasCompactSupport (fun p : (E × E) × E ↦ A p.1.1 p.1.2 p.2))
    (T : H →L[ℂ] H)
    (hreal : ∀ u : graphTestSpace n q, T (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (((if backward then reverseGraphOperator else graphOperator)
        S A (fun y ↦ (u.val y).ofLp)) x))
    (u : H) (v : E → Fin q → ℂ) (hv : Continuous v)
    (he : u =ᵐ[volume] fun x ↦ WithLp.toLp 2 (v x)) :
    T u =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (((if backward then reverseGraphOperator else graphOperator) S A v) x) := by
  let c : ℂ := ((2 * Real.pi) ^ n : ℂ)⁻¹
  let G : (E × E) × E → Matrix (Fin q) (Fin q) ℂ := fun p ↦
    if backward then star (graphOscillation S p.1.2 p.1.1 p.2) • A p.1.2 p.1.1 p.2
    else graphOscillation S p.1.1 p.1.2 p.2 • A p.1.1 p.1.2 p.2
  have hg : Continuous G := by
    have hp : Continuous (fun p : (E × E) × E ↦ graphOscillation S p.1.1 p.1.2 p.2) := by
      have hh : Continuous (fun p : (E × E) × E ↦ S p.1.1 p.2) :=
        hS.comp (continuous_fst.fst.prodMk continuous_snd)
      unfold graphOscillation
      fun_prop
    have hc := hp.smul hA
    cases backward
    · exact hc
    · exact (hp.star.smul hA).comp
        ((continuous_fst.snd.prodMk continuous_fst.fst).prodMk continuous_snd)
  have hgs : HasCompactSupport G := by
    cases backward
    · apply HasCompactSupport.intro hs
      intro p hp
      have hz : A p.1.1 p.1.2 p.2 = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun p : (E × E) × E ↦ A p.1.1 p.1.2 p.2) hp
      simp [G, hz]
    · apply HasCompactSupport.of_support_subset_isCompact
        (hs.image ((continuous_fst.snd.prodMk continuous_fst.fst).prodMk continuous_snd))
      intro p hp
      refine ⟨((p.1.2, p.1.1), p.2), subset_tsupport _ ?_, by simp⟩
      intro hz
      exact hp (by simp [G, hz])
  let F : Fin q → Fin q → (E × E) × E → ℂ := fun i j p ↦ c * G p i j
  have hc (i j : Fin q) : Continuous (F i j) :=
    continuous_const.mul ((matrixEntryEvaluation i j).continuous.comp hg)
  have hfs (i j : Fin q) : HasCompactSupport (F i j) := by
    apply HasCompactSupport.intro hgs
    intro p hp
    simp [F, image_eq_zero_of_notMem_tsupport hp]
  have hf (w : E → Fin q → ℂ) (x : E) :
      WithLp.toLp 2 (∫ η, ∫ y, fun i ↦ ∑ j, F i j ((x, y), η) * w y j) =
        WithLp.toLp 2 (((if backward then reverseGraphOperator else graphOperator) S A w) x) := by
    apply congrArg (WithLp.toLp 2)
    cases backward <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, graphOperator, reverseGraphOperator]
    all_goals
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with η
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with y
      funext i
      simp only [F, G, Bool.false_eq_true, ite_false, ite_true, Pi.smul_apply,
        Matrix.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
  exact (compactEntry_test_realization_on_continuous_input F hc hfs T
    (fun w ↦ (hreal w).trans (Eventually.of_forall (fun x ↦ (hf _ x).symm)))
    u v hv he).trans (Eventually.of_forall (hf v))

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
