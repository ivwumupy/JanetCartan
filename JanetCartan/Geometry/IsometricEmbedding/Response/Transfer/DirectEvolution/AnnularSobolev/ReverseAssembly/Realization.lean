module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.ReverseBranches.Construction

/-!
# Removing the reverse annular frequency regularization

The normalized support produces a smooth compact frequency cutoff equal to one
on the actual amplitude. The compact full-graph adjoint theorem then identifies
the uncut reverse integral. The forward test identity is supplied by the
primitive branch constructor in `ReverseAssembly.UniformBranches`; no reverse
realization or modified-operator bound is assumed there. Consumer:
`WeakTransfer.annularEnvelope_adjoint_joint_derivative_expansion`, for
`new:eq:carrier-ibp` and `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 4
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
open FourierIntegral FourierIntegral.FullLowBounds FourierIntegral.SourceExpansion
open FullAmplitudePrimitiveBudget.Local ModifiedLow NearCarrierSymbol
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)
local instance reverseRealizationComplexMatrixTopology : TopologicalSpace Mat :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- Compact original physical supports and bounded normalized frequency support
remove the cutoff in the literal adjoint test identity. Global smoothness here
is only that of the supported normalized branch, produced from local primitive
smoothness by `contDiff_normalizedTermAmplitude`. The carrier itself need not
be globally smooth. Source: the reversed case of `new:eq:carrier-ibp`. -/
theorem modifiedAmplitude_adjoint_ae_of_normalized_support
    (S : E → E → ℝ) (hS : ContDiff ℝ ∞ (Function.uncurry S))
    {f : Point n → Mat} (hf : ContDiff ℝ ∞ f)
    {lam radius : ℝ} (hlam : 0 < lam) (hradius : 0 ≤ radius) (p : ℤ)
    {X Y : Set E} (hX : IsCompact X) (hY : IsCompact Y)
    (hs : ∀ q ∈ tsupport f, q.1.2 ∈ X ∧ q.1.1 ∈ Y)
    (hsfreq : ∀ q ∈ tsupport f, ‖q.2‖ ≤ radius)
    (T : H →L[ℂ] H)
    (hreal : ∀ u : graphTestSpace n r, T (graphTestToLp u) =ᵐ[volume]
      graphTestOutput S (fun x y ξ => (modifiedAmplitude lam p f y x ξ).conjTranspose) u)
    (u : graphTestSpace n r) :
    T.adjoint (graphTestToLp u) =ᵐ[volume] fun x => WithLp.toLp 2
      (reverseGraphOperator S (fun y z ξ => modifiedAmplitude lam p f z y ξ)
        (fun y => (u.val y).ofLp) x) := by
  let A : FullAmplitude n r := fun x y ξ => (modifiedAmplitude lam p f y x ξ).conjTranspose
  have hA : ContDiff ℝ ∞ (fun q : E × E × E => A q.1 q.2.1 q.2.2) :=
    (starL ℝ : Mat ≃L[ℝ] Mat).contDiff.comp
      ((contDiff_modifiedAmplitude lam p hf).comp
        ((contDiff_snd.fst.prodMk contDiff_fst).prodMk contDiff_snd.snd))
  have hAs : ∀ x y ξ, x ∉ X ∨ y ∉ Y → A x y ξ = 0 := by
    intro x y ξ hout
    have hz : f ((y, x), lam⁻¹ • ξ) = 0 := by
      by_contra hn
      have h := hs ((y, x), lam⁻¹ • ξ) (subset_tsupport f hn)
      exact hout.elim (fun hx => hx h.1) (fun hy => hy h.2)
    simp [A, modifiedAmplitude, physicalAmplitudeOfNormalized, hz]
  let b : ContDiffBump (0 : E) :=
    { rIn := lam * radius + 1
      rOut := lam * radius + 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let θ : E → ℂ := fun ξ => (b ξ : ℂ)
  have hθ : ContDiff ℝ ∞ θ := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hθs : HasCompactSupport θ :=
    b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero
  have hθone (x y ξ : E) (hn : f ((y, x), lam⁻¹ • ξ) ≠ 0) : θ ξ = 1 := by
    have hbound := hsfreq ((y, x), lam⁻¹ • ξ) (subset_tsupport f hn)
    have he : ξ = lam • (lam⁻¹ • ξ) := by simp [smul_smul, hlam.ne']
    have hnorm : ‖ξ‖ ≤ lam * radius := by
      calc
        ‖ξ‖ = lam * ‖lam⁻¹ • ξ‖ := by
          conv_lhs => rw [he]
          rw [norm_smul, Real.norm_of_nonneg hlam.le]
        _ ≤ lam * radius := mul_le_mul_of_nonneg_left hbound hlam.le
    have hb : b ξ = 1 := b.one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall, dist_zero_right, b] using
        (show ‖ξ‖ ≤ lam * radius + 1 by linarith))
    simp [θ, hb]
  have hcut : (fun x y ξ => θ ξ • A x y ξ) = A := by
    funext x y ξ
    by_cases hn : f ((y, x), lam⁻¹ • ξ) = 0
    · simp [A, modifiedAmplitude, physicalAmplitudeOfNormalized, hn]
    · rw [hθone x y ξ hn, one_smul]
  have hrevcut : frequencyCutFullAmplitude (fun ξ => star (θ ξ))
      (fun x y ξ => (A x y ξ).conjTranspose) =
        fun x y ξ => modifiedAmplitude lam p f y x ξ := by
    funext x y ξ
    by_cases hn : f ((y, x), lam⁻¹ • ξ) = 0
    · simp [frequencyCutFullAmplitude, A, modifiedAmplitude, physicalAmplitudeOfNormalized, hn]
    · simp [frequencyCutFullAmplitude, hθone x y ξ hn, A]
  have h := compactFullGraph_adjoint_ae S hS A hA hX hY hAs θ hθ hθs T
    (fun v => by rw [hcut]; exact hreal v) u
  simpa only [hrevcut] using h

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
