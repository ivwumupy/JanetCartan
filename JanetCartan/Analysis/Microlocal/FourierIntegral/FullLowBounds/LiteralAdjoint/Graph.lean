module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.LiteralAdjoint.IntegratedKernel
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.Distributional
public import JanetCartan.Analysis.Microlocal.FourierIntegral.L2Realization

/-!
# The literal compact full-graph adjoint

The finite-cutoff identification needed by `FullLowBounds.Uniform` in
`app:ch_regular_base:thm:actual-calculus`, Step 1, and
`app:ch_regular_base:eq:actual-adjoint-trade`. The only operator premise is
its forward realization on compact smooth tests.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullLowBounds
open AmplitudeBound
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The actual Hilbert adjoint of a compact-frequency full graph is its literal
reverse integral on tests. Smoothness and compact physical/frequency support
supply all integrability through `exists_compactFullEntryOperator`; only the
forward test realization of `T` is assumed. Consumer:
`FullLowBounds.Uniform.exists_fullGraphL2_of_primitive_inputs`, for
`app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem compactFullGraph_adjoint_ae
    (S : E → E → ℝ) (hS : ContDiff ℝ ∞ (Function.uncurry S))
    (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : E × E × E ↦ A p.1 p.2.1 p.2.2))
    {X Y : Set E} (hX : IsCompact X) (hY : IsCompact Y)
    (hs : ∀ x y η, x ∉ X ∨ y ∉ Y → A x y η = 0)
    (θ : E → ℂ) (hθ : ContDiff ℝ ∞ θ) (hθs : HasCompactSupport θ)
    (T : H →L[ℂ] H)
    (hreal : ∀ u : graphTestSpace n r, T (graphTestToLp u) =ᵐ[volume]
      graphTestOutput S (fun x y η ↦ θ η • A x y η) u)
    (u : graphTestSpace n r) :
    T.adjoint (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
      (reverseGraphOperator S (frequencyCutFullAmplitude (fun η ↦ star (θ η))
        (fun x y η ↦ (A x y η).conjTranspose)) (fun x ↦ (u.val x).ofLp) y) := by
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
  obtain ⟨U, hU, hUa⟩ := exists_compactFullEntryOperator F hc hfs
  have hf (v : graphTestSpace n r) (x : E) :
      WithLp.toLp 2 (∫ η, ∫ y, fun i ↦ ∑ j, F i j ((x, y), η) * v.val y j) =
        graphTestOutput S (fun x y η ↦ θ η • A x y η) v x := by
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
    simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, Matrix.smul_apply,
      smul_eq_mul, Finset.mul_sum, F]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hTU : T = U := by
    apply DFunLike.coe_injective
    apply denseRange_graphTestToLp.equalizer T.continuous U.continuous
    funext v
    apply Lp.ext
    exact (hreal v).trans ((hU v).trans (Eventually.of_forall (hf v))).symm
  rw [hTU]
  refine (hUa u).trans (Eventually.of_forall fun y ↦ ?_)
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

/-- Strong convergence of the actual regularized adjoints gives the reverse
weak realization. The regularized reverse identities are proved above from the
forward identities, smoothness and compact support. The actual producer of
`hreal` and `hlim` is `FullLowBounds.Uniform.exists_fullGraphL2_of_primitive_inputs`;
its geometric instantiation is not needed for this implication. Source:
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graphDistributionalRealization_adjoint_of_strong_limit
    (S : E → E → ℝ) (hS : ContDiff ℝ ∞ (Function.uncurry S))
    (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : E × E × E ↦ A p.1 p.2.1 p.2.2))
    {X Y : Set E} (hX : IsCompact X) (hY : IsCompact Y)
    (hs : ∀ x y η, x ∉ X ∨ y ∉ Y → A x y η = 0)
    (χ : ℕ → E → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (hχs : ∀ j, HasCompactSupport (χ j))
    (T : H →L[ℂ] H) (Treg : ℕ → H →L[ℂ] H)
    (hreal : ∀ j (u : graphTestSpace n r), Treg j (graphTestToLp u) =ᵐ[volume]
      graphTestOutput S (fun x y η ↦ χ j η • A x y η) u)
    (hlim : ∀ u, Tendsto (fun j ↦ (Treg j).adjoint u) atTop (𝓝 (T.adjoint u))) :
    GraphDistributionalRealization (reverseGraphOperator S) (fun j η ↦ star (χ j η))
      (fun x y η ↦ (A x y η).conjTranspose) T.adjoint :=
  graphDistributionalRealization_of_strong_limit (reverseGraphOperator S)
    (fun j η ↦ star (χ j η)) (fun x y η ↦ (A x y η).conjTranspose)
    T.adjoint (fun j ↦ (Treg j).adjoint)
    (fun j u ↦ compactFullGraph_adjoint_ae S hS A hA hX hY hs
      (χ j) (hχ j) (hχs j) (Treg j) (hreal j) u) hlim

end JanetCartan.FourierIntegral.FullLowBounds
