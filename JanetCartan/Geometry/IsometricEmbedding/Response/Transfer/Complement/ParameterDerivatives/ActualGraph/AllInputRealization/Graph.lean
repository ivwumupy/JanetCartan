module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.ActualGraph.AllInputRealization.CompactKernel
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.Operators

/-!
# Literal compact full graphs on arbitrary L² inputs

The canonical full graph and its actual Hilbert adjoint are the literal
frequency-first integrals on every original Euclidean vector L² input.
Compact physical/frequency support supplies Fubini; density identifies the
canonical operator. Consumer: the low/high source split in
`app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullLowBounds
open AmplitudeBound
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The canonical compact-frequency full graph and its Hilbert adjoint act by
literal integrals on EVERY original vector L² input. Both physical positions,
Lebesgue measure and the physical `(2 * π)⁻ⁿ` normalization are retained.
Consumer: the `hreal` inputs of the forward/reverse original Leibniz decay
assembly in `app:ch_response:thm:response-literal-transfer`. -/
theorem fullGraphOperator_frequencyCut_allInput
    (S : E → E → ℝ) (hS : ContDiff ℝ ∞ (Function.uncurry S))
    (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : E × E × E ↦ A p.1 p.2.1 p.2.2))
    {X Y : Set E} (hX : IsCompact X) (hY : IsCompact Y)
    (hs : ∀ x y η, x ∉ X ∨ y ∉ Y → A x y η = 0)
    (θ : E → ℂ) (hθ : ContDiff ℝ ∞ θ) (hθs : HasCompactSupport θ) :
    (∀ w : H, fullGraphOperator S (frequencyCutFullAmplitude θ A) w =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator S (frequencyCutFullAmplitude θ A)
        (fun y ↦ (w y).ofLp) x)) ∧
    (∀ w : H, (fullGraphOperator S (frequencyCutFullAmplitude θ A)).adjoint w =ᵐ[volume]
      fun y ↦ WithLp.toLp 2 (reverseGraphOperator S
        (frequencyCutFullAmplitude (fun η ↦ star (θ η))
          (fun x y η ↦ (A x y η).conjTranspose)) (fun x ↦ (w x).ofLp) y)) := by
  let c : ℂ := ((2 * Real.pi) ^ n : ℂ)⁻¹
  let F : Fin r → Fin r → (E × E) × E → ℂ := fun i j p ↦
    c * graphOscillation S p.1.1 p.1.2 p.2 * (θ p.2 * A p.1.1 p.1.2 p.2 i j)
  have hc (i j : Fin r) : Continuous (F i j) := by
    have ha := ((matrixEntryEvaluation i j).continuous.comp hA.continuous).comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
    have hp : Continuous (fun p : (E × E) × E ↦ S p.1.1 p.2) :=
      hS.continuous.comp (continuous_fst.fst.prodMk continuous_snd)
    have hg : Continuous (fun p : (E × E) × E ↦ graphOscillation S p.1.1 p.1.2 p.2) := by
      unfold graphOscillation
      fun_prop
    exact (continuous_const.mul hg).mul ((hθ.continuous.comp continuous_snd).mul ha)
  have hfs (i j : Fin r) : HasCompactSupport (F i j) := by
    apply HasCompactSupport.intro ((hX.prod hY).prod hθs)
    rintro ⟨⟨x, y⟩, η⟩ hp
    by_cases hx : x ∈ X
    · by_cases hy : y ∈ Y
      · have hη : η ∉ tsupport θ := fun hη ↦ hp ⟨⟨hx, hy⟩, hη⟩
        simp [F, image_eq_zero_of_notMem_tsupport hη]
      · simp [F, hs x y η (Or.inr hy)]
    · simp [F, hs x y η (Or.inl hx)]
  obtain ⟨U, hU, hUa⟩ := exists_compactFullEntryOperator_allInput F hc hfs
  have hf (v : E → Fin r → ℂ) (x : E) :
      WithLp.toLp 2 (∫ η, ∫ y, fun i ↦ ∑ j, F i j ((x, y), η) * v y j) =
        WithLp.toLp 2 (graphOperator S (frequencyCutFullAmplitude θ A) v x) := by
    change WithLp.toLp 2 _ = WithLp.toLp 2 (c • _)
    apply congrArg (WithLp.toLp 2)
    rw [← integral_smul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro η
    dsimp only
    rw [← integral_smul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    funext i
    simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, frequencyCutFullAmplitude, Matrix.smul_apply,
      smul_eq_mul, Finset.mul_sum, F]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hforward (w : H) : U w =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (graphOperator S (frequencyCutFullAmplitude θ A) (fun y ↦ (w y).ofLp) x) :=
    (hU w).trans (Eventually.of_forall (hf (fun y ↦ (w y).ofLp)))
  have hcanonical : fullGraphOperator S (frequencyCutFullAmplitude θ A) = U := by
    apply fullGraphOperator_eq_of_realizes
    intro u
    refine (hforward (graphTestToLp u)).trans (Eventually.of_forall fun x ↦ ?_)
    apply congrArg (WithLp.toLp 2)
    unfold graphOperator
    congr 1
    apply integral_congr_ae
    apply Eventually.of_forall
    intro η
    apply integral_congr_ae
    filter_upwards [(graphTest_memLp u).coeFn_toLp] with y hy
    rw [show graphTestToLp u y = u.val y from hy]
  rw [hcanonical]
  refine ⟨hforward, fun w ↦ (hUa w).trans (Eventually.of_forall fun y ↦ ?_)⟩
  change WithLp.toLp 2 _ = WithLp.toLp 2 (c • _)
  apply congrArg (WithLp.toLp 2)
  rw [← integral_smul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro η
  dsimp only
  rw [← integral_smul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  funext j
  simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, frequencyCutFullAmplitude,
    Matrix.smul_apply, Matrix.conjTranspose_apply, smul_eq_mul, Finset.mul_sum,
    F]
  apply Finset.sum_congr rfl
  intro i _
  have hcstar : star c = c := by simp [c]
  simp only [star_mul, hcstar]
  ring
end JanetCartan.FourierIntegral.FullLowBounds
