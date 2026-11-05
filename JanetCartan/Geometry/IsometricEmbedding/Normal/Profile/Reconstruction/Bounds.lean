module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Reconstruction.Symmetric
public import JanetCartan.Geometry.IsometricEmbedding.Normal.RankStability

/-!
# One-high bounds for the actual normal inverse

Compact low second-jet ranges with immersion and normal-rank gaps give the
normal-inverse part of `app:ch_waves:eq:joint-tame`. The reserve is two at
every order. No coefficient profile or interpolation estimate is assumed.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius
open scoped JanetCartan.NormalRankStability JanetCartan.TensorFrobenius

namespace JanetCartan.GeometricProfile

/-- `app:ch_waves:eq:joint-tame`: the actual normal-inverse jet coefficient
has one high map norm with the order-independent reserve two. Compactness
and geometric rank supply the inverse gap. -/
theorem exists_cNorm_secondJetNormalInverse_le_closedBall
    {n N : ℕ} (x : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (SecondJet (Euclidean n) (Euclidean N))} (ht : IsCompact t)
    (htimm : ∀ J ∈ t, Function.Injective J.1)
    (htrank : ∀ J ∈ t, Set.range (secondJetNormalMap J) =
      ((LinearMap.range J.1.toLinearMap)ᗮ : Set (Euclidean N))) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Euclidean n → Euclidean N, ContDiff ℝ ∞ f →
      Set.MapsTo (secondJet f) (Metric.closedBall x ρ) t →
        cNorm (Metric.closedBall x ρ) r (secondJetNormalInverse ∘ secondJet f) ≤
          C * (1 + cNorm (Metric.closedBall x ρ) (r + 2) f) :=
  exists_cNorm_secondJet_comp_le_closedBall x hρ ht (fun J hJ ↦
    (contDiffAt_secondJetNormalInverse (firstJetMetric_isUnit_of_injective (htimm J hJ))
      (secondJetAmbientOperator_isUnit (htimm J hJ) (htrank J hJ))).of_le
        (by simp : (r : ℕ∞ω) ≤ ∞))

/-- `app:ch_waves:eq:joint-tame`: the ambient Gram operator itself has the
same fixed second-jet reserve; no normal rank is needed for this coefficient. -/
theorem exists_cNorm_secondJetAmbientOperator_le_closedBall
    {n N : ℕ} (x : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (SecondJet (Euclidean n) (Euclidean N))} (ht : IsCompact t)
    (htimm : ∀ J ∈ t, Function.Injective J.1) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Euclidean n → Euclidean N, ContDiff ℝ ∞ f →
      Set.MapsTo (secondJet f) (Metric.closedBall x ρ) t →
        cNorm (Metric.closedBall x ρ) r (secondJetAmbientOperator ∘ secondJet f) ≤
          C * (1 + cNorm (Metric.closedBall x ρ) (r + 2) f) :=
  exists_cNorm_secondJet_comp_le_closedBall x hρ ht (fun J hJ ↦
    (contDiffAt_secondJetAmbientOperator
      (firstJetMetric_isUnit_of_injective (htimm J hJ))).of_le
        (by simp : (r : ℕ∞ω) ≤ ∞))

/-- `app:ch_waves:eq:ambient-normal-inverse`: equality of the actual
completion and the jet formula holds on a neighborhood of every full-rank
immersion point, so it also identifies all ambient boundary derivatives. -/
theorem eventuallyEq_canonicalNormalCompletion_secondJetNormalInverse
    {n N : ℕ} {f : Euclidean n → Euclidean N} (hf : ContDiff ℝ ∞ f)
    {x : Euclidean n} (hi : Function.Injective (fderiv ℝ f x))
    (hrank : Set.range (normalMap f x) = (normalSpace f x : Set (Euclidean N))) :
    (fun y ↦ (AmbientResponse.canonicalNormalCompletion f y).toContinuousLinearMap) =ᶠ[𝓝 x]
      (secondJetNormalInverse ∘ secondJet f) := by
  have ho := NormalRankStability.isOpen_fullNormalRank_immersionDomain
    isOpen_univ (hf.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffOn
  have he := ho.mem_nhds (show x ∈ {y | y ∈ immersionDomain f Set.univ ∧
      Set.range (normalMap f y) = (normalSpace f y : Set (Euclidean N))} from
    ⟨⟨Set.mem_univ x, hi⟩, hrank⟩)
  filter_upwards [he] with y hy
  ext H : 1
  exact LinearMap.congr_fun
    (secondJetNormalInverse_eq_canonicalNormalCompletion hf hy.1.2 hy.2).symm H

/-- `app:ch_waves:eq:joint-tame`: a one-high estimate for the existing
canonical completion itself, including derivatives at the closed-ball boundary. -/
theorem exists_cNorm_canonicalNormalCompletion_le_closedBall
    {n N : ℕ} (x : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (SecondJet (Euclidean n) (Euclidean N))} (ht : IsCompact t)
    (htimm : ∀ J ∈ t, Function.Injective J.1)
    (htrank : ∀ J ∈ t, Set.range (secondJetNormalMap J) =
      ((LinearMap.range J.1.toLinearMap)ᗮ : Set (Euclidean N))) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Euclidean n → Euclidean N, ContDiff ℝ ∞ f →
      Set.MapsTo (secondJet f) (Metric.closedBall x ρ) t →
        cNorm (Metric.closedBall x ρ) r
          (fun y ↦ (AmbientResponse.canonicalNormalCompletion f y).toContinuousLinearMap) ≤
          C * (1 + cNorm (Metric.closedBall x ρ) (r + 2) f) := by
  obtain ⟨C, hC, hbound⟩ := exists_cNorm_secondJetNormalInverse_le_closedBall
    x hρ ht htimm htrank r
  refine ⟨C, hC, fun f hf hft ↦ ?_⟩
  have he : cNorm (Metric.closedBall x ρ) r
      (fun y ↦ (AmbientResponse.canonicalNormalCompletion f y).toContinuousLinearMap) =
      cNorm (Metric.closedBall x ρ) r (secondJetNormalInverse ∘ secondJet f) := by
    apply cNorm_eq_of_eventuallyEq
    intro y hy
    have hi : Function.Injective (fderiv ℝ f y) := htimm _ (hft hy)
    apply eventuallyEq_canonicalNormalCompletion_secondJetNormalInverse hf hi
    have hr := htrank _ (hft hy)
    rw [secondJetNormalMap_eq hf hi] at hr
    exact hr
  rw [he]
  exact hbound f hf hft

/-- `app:cor:fixed-profile-transfer`: the actual normal completion transfers
profiles with one reserve of two, independent of the differentiated order. -/
theorem exists_canonicalNormalCompletion_profiles_closedBall
    {n N : ℕ} (x : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (SecondJet (Euclidean n) (Euclidean N))} (ht : IsCompact t)
    (htimm : ∀ J ∈ t, Function.Injective J.1)
    (htrank : ∀ J ∈ t, Set.range (secondJetNormalMap J) =
      ((LinearMap.range J.1.toLinearMap)ᗮ : Set (Euclidean N))) :
    ∃ C : ℕ → ℝ, (∀ r, 0 < C r) ∧
      ∀ f : Euclidean n → Euclidean N, ContDiff ℝ ∞ f →
      Set.MapsTo (secondJet f) (Metric.closedBall x ρ) t →
      ∀ (R ν : ℕ) (T : ℝ) (A : ℕ → ℝ),
      HasDerivativeProfile (Metric.closedBall x ρ) f R T A →
      1 ≤ T → (∀ r, 0 ≤ A r) → 2 + ν ≤ R →
        HasDerivativeProfile (Metric.closedBall x ρ)
          (fun y ↦ (AmbientResponse.canonicalNormalCompletion f y).toContinuousLinearMap) ν T
          (fun r ↦ C r * (1 + A (r + 2))) := by
  have hbound := fun r ↦ exists_cNorm_canonicalNormalCompletion_le_closedBall
    x hρ ht htimm htrank r
  choose C hC hCf using hbound
  refine ⟨C, hC, ?_⟩
  intro f hf hft R ν T A hp hT hA hloss
  exact hp.transfer hT hA (fun r ↦ (hC r).le) hloss (fun r ↦ hCf r f hf hft)

end JanetCartan.GeometricProfile
