module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.OneFactor.Operator
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.OneFactor.WeakAction
public import JanetCartan.Analysis.Microlocal.RegularSector.Realization.L2

/-!
# The actual one-factor channel comparison

For `app:ch_background:prop:bg-frame`, Step 1, the weak periodic channel and
the Euclidean channel differ by the concrete differentiated lattice kernel.
The proved integral actions identify them on real Schwartz data; density
extends the equality to all real L². The final existence theorem chooses
the interior plateau and supplies the support and paired H¹ estimates
required by `normalCrossTerms_periodic_endpoints`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff SchwartzMap
open JanetCartan.PeriodicLocalL2 JanetCartan.Pseudodifferential
open JanetCartan.Pseudodifferential.DifferentialChart

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "R²" => EuclideanL2 d E

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem eq_of_schwartz_inclusion (T U : R² →L[ℝ] R²)
    (h : ∀ (v : Fin d → 𝓢(E, ℂ)) (f : R²),
      l2ComplexInclusion volume f =ᵐ[volume] (fun x ↦ WithLp.toLp 2 (fun i ↦ v i x)) →
      l2ComplexInclusion volume (T f) = l2ComplexInclusion volume (U f)) : T = U := by
  have he : (T : R² → R²) = U := by
    apply (SchwartzMap.denseRange_toLpCLM (F := EuclideanSpace ℝ (Fin d))
      (p := 2) (μ := volume) (by norm_num)).equalizer T.continuous U.continuous
    funext u
    let v : Fin d → 𝓢(E, ℂ) := fun i ↦ SchwartzMap.postcompCLM
      (Complex.ofRealCLM.comp (EuclideanSpace.proj i)) u
    have hu : l2ComplexInclusion volume (u.toLp 2) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (fun i ↦ v i x) := by
      filter_upwards [euclideanComplexInclusion.coeFn_compLpL (u.toLp 2),
        u.coeFn_toLp 2] with x hx hy
      change l2ComplexInclusion volume (u.toLp 2) x = euclideanComplexInclusion _ at hx
      rw [hx, hy]
      rfl
    change T (u.toLp 2) = U (u.toLp 2)
    have hh := h v (u.toLp 2) hu
    calc
      T (u.toLp 2) = l2RealPart volume (l2ComplexInclusion volume (T (u.toLp 2))) :=
        (RegularSector.Realization.realPart_inclusion _).symm
      _ = l2RealPart volume (l2ComplexInclusion volume (U (u.toLp 2))) := congrArg _ hh
      _ = U (u.toLp 2) := RegularSector.Realization.realPart_inclusion _
  exact DFunLike.coe_injective he

/-- The actual periodic channel equals the Euclidean channel plus the
concrete differentiated lattice remainder, on all real L². The only input
about `B` is the forward test action of
`normal_schwartz_action_of_channel_actions`; the local coefficient agreements
are supplied by ImageGeometry (`app:ch_background:prop:bg-frame`, Step 1).
The auxiliary plateau is discharged in
`exists_periodicChannel_oneFactorRemainder`. -/
theorem periodicChannel_eq_add_oneFactorRemainder (hd : 0 < d)
    {r R : ℝ} (hr : r < 1 / 2) (hR₀ : 0 < R) (hrR : r < R) (hR : R < 1 / 2)
    (c : GeometricProfile.ReducedCoefficientIndex d → C(Torus d, ℝ))
    (hc : ∀ k, IsSmoothPeriodic (c k))
    (χ μ ρ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ)
    (hρ : ContDiff ℝ ∞ ρ)
    (hχs : tsupport χ ⊆ chartBox r) (hμs : tsupport μ ⊆ chartBox r)
    (hρs : tsupport ρ ⊆ chartBox R)
    (hplateau : ∀ x ∈ tsupport μ, ρ =ᶠ[nhds x] (fun _ ↦ 1))
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hcA : ∀ x ∈ tsupport μ, ∀ a i j,
      periodicLift (c (.inl (a, i, j))) =ᶠ[nhds x] (fun y ↦ A y a i j))
    (hcZ : ∀ x ∈ tsupport μ, ∀ i j,
      periodicLift (c (.inr (i, j))) =ᶠ[nhds x] (fun y ↦ Z y i j))
    (B : R² →L[ℝ] R²)
    (hB : ∀ (v : Fin d → 𝓢(E, ℂ)) (f : R²),
      l2ComplexInclusion volume f =ᵐ[volume] (fun x ↦ WithLp.toLp 2 (fun i ↦ v i x)) →
      l2ComplexInclusion volume (B f) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (fun i ↦ channelSchwartz A Z χ μ v i x)) :
    periodicChannel hr c χ μ hχ hμ hχs hμs = B +
      realOneFactorRemainderOperator hR ρ χ μ hρ hχ hμ
        (fun _x hx ↦ hρs (subset_tsupport ρ hx))
        (fun _x hx a ↦ (hχs (subset_tsupport χ hx) a).trans hrR.le)
        (fun _x hx a ↦ (hμs (subset_tsupport μ hx) a).trans hrR.le) A Z hA hZ := by
  let hρb : ∀ x, ρ x ≠ 0 → ∀ a, |x a| ≤ R :=
    fun x hx ↦ hρs (subset_tsupport ρ hx)
  let hχb : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ R :=
    fun x hx a ↦ (hχs (subset_tsupport χ hx) a).trans hrR.le
  let hμb : ∀ x, μ x ≠ 0 → ∀ a, |x a| ≤ R :=
    fun x hx a ↦ (hμs (subset_tsupport μ hx) a).trans hrR.le
  let D := realOneFactorRemainderOperator hR ρ χ μ hρ hχ hμ hρb hχb hμb A Z hA hZ
  change periodicChannel hr c χ μ hχ hμ hχs hμs = B + D
  apply eq_of_schwartz_inclusion
  intro v f hf
  have hD : l2ComplexInclusion volume (D f) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ ∑ j, ∫ y,
        (oneFactorRemainderKernel ρ χ μ A Z i j (x, y) : ℂ) * v j y) := by
    rw [show l2ComplexInclusion volume (D f) =
      complexOneFactorRemainderOperator hR ρ χ μ hρ hχ hμ hρb hχb hμb A Z hA hZ
        (l2ComplexInclusion volume f) from
      l2ComplexInclusion_realOneFactorRemainderOperator
        hR ρ χ μ hρ hχ hμ hρb hχb hμb A Z hA hZ f]
    filter_upwards [complexOneFactorRemainderOperator_ae_integral
      hR ρ χ μ hρ hχ hμ hρb hχb hμb A Z hA hZ (l2ComplexInclusion volume f)] with x hx
    rw [hx]
    apply PiLp.ext
    intro i
    simp only
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [hf] with y hy
    rw [hy]
  have hP := periodicChannel_schwartz_action hd hr hR₀ hrR hR c hc χ μ ρ hχ hμ hρ
    hχs hμs hρs hplateau A Z hA hZ hcA hcZ v f hf
  rw [add_apply, map_add]
  apply Lp.ext
  filter_upwards [hP, hB v f hf, hD,
    Lp.coeFn_add (l2ComplexInclusion volume (B f)) (l2ComplexInclusion volume (D f))]
    with x hx hb hd hs
  rw [hx, hs, Pi.add_apply, hb, hd]
  rfl

/-- The completed one-factor comparison for the original fixed data of
`app:ch_background:prop:bg-frame`, Step 1. The remainder is constructed from
`oneFactorRemainderKernel` with the plateau supplied by
`exists_oneFactorPlateau`; it retains the measurement support, and it and its
literal adjoint satisfy exactly the paired L²-to-H¹ input of
`normalCrossTerms_sobolev_one_bounds`. The only channel assumption is the
original forward Schwartz action of `B`. The actual instantiation of `B`
and all three normal cross terms belong to the parent normal comparison. -/
theorem exists_periodicChannel_oneFactorRemainder (hd : 0 < d)
    {r : ℝ} (hr : r < 1 / 2)
    (c : GeometricProfile.ReducedCoefficientIndex d → C(Torus d, ℝ))
    (hc : ∀ k, IsSmoothPeriodic (c k))
    (χ μ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ)
    (hχs : tsupport χ ⊆ chartBox r) (hμs : tsupport μ ⊆ chartBox r)
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hcA : ∀ x ∈ tsupport μ, ∀ a i j,
      periodicLift (c (.inl (a, i, j))) =ᶠ[nhds x] (fun y ↦ A y a i j))
    (hcZ : ∀ x ∈ tsupport μ, ∀ i j,
      periodicLift (c (.inr (i, j))) =ᶠ[nhds x] (fun y ↦ Z y i j))
    (B : R² →L[ℝ] R²)
    (hB : ∀ (v : Fin d → 𝓢(E, ℂ)) (f : R²),
      l2ComplexInclusion volume f =ᵐ[volume] (fun x ↦ WithLp.toLp 2 (fun i ↦ v i x)) →
      l2ComplexInclusion volume (B f) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (fun i ↦ channelSchwartz A Z χ μ v i x)) :
    ∃ D : R² →L[ℝ] R²,
      periodicChannel hr c χ μ hχ hμ hχs hμs = B + D ∧
      (∀ f, ∀ᵐ x ∂volume, x ∉ tsupport μ → D f x = 0) ∧
      ∃ CD : ℝ, 0 ≤ CD ∧ ∀ f : R²,
        MemVectorFourierSobolev 1 (l2ComplexInclusion volume (D f)) ∧
        vectorFourierSobolevNorm 1 (l2ComplexInclusion volume (D f)) ≤ CD * ‖f‖ ∧
        MemVectorFourierSobolev 1 (l2ComplexInclusion volume (D.adjoint f)) ∧
        vectorFourierSobolevNorm 1 (l2ComplexInclusion volume (D.adjoint f)) ≤ CD * ‖f‖ := by
  obtain ⟨R, hR₀, hrR, hR, ρ, hρ, hρs, hplateau⟩ := exists_oneFactorPlateau (d := d) hr
  let hρb : ∀ x, ρ x ≠ 0 → ∀ a, |x a| ≤ R :=
    fun x hx ↦ hρs (subset_tsupport ρ hx)
  let hχb : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ R :=
    fun x hx a ↦ (hχs (subset_tsupport χ hx) a).trans hrR.le
  let hμb : ∀ x, μ x ≠ 0 → ∀ a, |x a| ≤ R :=
    fun x hx a ↦ (hμs (subset_tsupport μ hx) a).trans hrR.le
  refine ⟨realOneFactorRemainderOperator hR ρ χ μ hρ hχ hμ hρb hχb hμb A Z hA hZ,
    ?_, ?_, ?_⟩
  · exact periodicChannel_eq_add_oneFactorRemainder hd hr hR₀ hrR hR c hc χ μ ρ
      hχ hμ hρ hχs hμs hρs (fun x hx ↦ hplateau x (hμs hx)) A Z hA hZ hcA hcZ B hB
  · exact realOneFactorRemainderOperator_support hR ρ χ μ hρ hχ hμ hρb hχb hμb A Z hA hZ
  · exact realOneFactorRemainderOperator_sobolev_one_bounds
      hR ρ χ μ hρ hχ hμ hρb hχb hμb A Z hA hZ

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
