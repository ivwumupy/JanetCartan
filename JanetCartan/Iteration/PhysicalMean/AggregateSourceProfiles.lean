module

public import JanetCartan.Iteration.PhysicalMean.NativeSourceProfiles

/-!
# Fixed aggregate source profiles for the original native inverse adjoint

The prechosen source-profile prefix is applied to the ACTUAL aggregate row
of AggregateSource. It yields genuine radial L² membership and the high-factor
budget without a moment-success hypothesis or a sum of samplewise norms
(`app:ch_mean_pairs:eq:block-bilinear`, `new:eq:source-bound`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.PhysicalMean
open Pseudodifferential PeriodicLocalL2 ContinuumRow

/-- The aggregate source budget is chosen before its native measure,
original sample, current inverse and source. Only derivative orders are summed. -/
def nativeAggregateSourceProfileConstant {n : ℕ}
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ halfOpenCell n) (Rbox : ℝ) (B Cinv M : ℕ → ℝ) (Ctest : ℝ) (q : ℕ) : ℝ :=
  nativeAggregateSourceConstant χ hχ hc hs Rbox B Cinv q*Ctest*((q : ℝ)+1)*sourceProfilePrefix M q

/-- Nonnegativity of the prechosen original aggregate input profile. -/
theorem nativeAggregateSourceProfileConstant_nonneg {n : ℕ}
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ halfOpenCell n) (Rbox : ℝ) (B Cinv M : ℕ → ℝ)
    (hB : ∀ k, 0 ≤ B k) (hCinv : ∀ k, 0 ≤ Cinv k) (hM : ∀ k, 0 ≤ M k)
    (Ctest : ℝ) (hCtest : 0 ≤ Ctest) (q : ℕ) :
    0 ≤ nativeAggregateSourceProfileConstant χ hχ hc hs Rbox B Cinv M Ctest q := by
  have hC := nativeAggregateSourceConstant_nonneg χ hχ hc hs Rbox B Cinv hB hCinv q
  have hP := sourceProfilePrefix_nonneg M hM q
  unfold nativeAggregateSourceProfileConstant
  positivity

/-- Apply the same current inverse's genuine aggregate radial moment theorem
to the original source profile. The full half-weighted scalar tester is used;
no bare individual tester or diagonal shell replacement enters this estimate. -/
theorem nativeRealMeasuredInverseAdjoint_source_profile {n : ℕ}
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ halfOpenCell n) (Rbox : ℝ) (B Cinv M : ℕ → ℝ)
    (hB : ∀ k, 0 ≤ B k) (hCinv : ∀ k, 0 ≤ Cinv k) (hM : ∀ k, 0 ≤ M k)
    (Ctest : ℝ) (q r₀ : ℕ)
    {ι : Type*} [Fintype ι] [MetricSpace ι] [DiscreteTopology ι] [MeasurableSpace ι] [BorelSpace ι]
    (μ : Measure (ι × Euclidean (n-1))) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ : (ι × Euclidean (n-1)) → Euclidean n → ℝ) (m : (ι × Euclidean (n-1)) → ℝ)
    (a : Fin n → ι → Euclidean (n-1) → Euclidean n → ℂ)
    (L : ι → Euclidean (n-1) → Euclidean (n-1) → Euclidean n → Euclidean n)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (ha : ∀ i k, ContDiff ℝ ∞ (Function.uncurry (a i k)))
    (hL : ∀ i v, ContDiff ℝ ∞ (fun p : Euclidean (n-1) × Euclidean n ↦ L i p.1 v p.2))
    {K : Set (Euclidean n)} (hK : IsCompact K) (has : ∀ i k η, tsupport (a i k η) ⊆ K)
    (hχK : ∀ x ∈ K, χ x = 1) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
    (Tfull : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hTfull : ∀ f : Lp ℂ 2 μ, Tfull f =ᵐ[volume] fun x ↦ ∫ z,
      sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)) x z*f z ∂μ)
    (hTfullBound : ‖Tfull‖ ≤ Ctest)
    (hφsmooth : ∀ z, ContDiff ℝ ∞ (φ z))
    (hphase : ∀ z, m z ≠ 0 → ∀ v x, x ∈ K →
      inner ℝ v z.2 = fderiv ℝ (φ z) x (L z.1 z.2 v x))
    {T R h : ℝ} (hT : 1 ≤ T) (hR : 1 ≤ R) (hTR : T ≤ R) (hh : 0 ≤ h)
    (hamp : ∀ i k η, m (k,η) ≠ 0 → ∀ x ∈ K, ∀ s,
      ‖iteratedFDeriv ℝ s (a i k η) x‖ ≤ B s*T^(s-(r₀+(n/2+1))))
    (hcoeff : ∀ k η, m (k,η) ≠ 0 → ∀ v, ‖v‖ ≤ 1 → ∀ x ∈ K, ∀ s,
      ‖iteratedFDeriv ℝ s (L k η v) x‖ ≤ B s*T^(s-(r₀+(n/2+1))))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (u : OutputL2 n)
    (hregular : ∀ s, Q₀ u ∈ periodicSobolevLevel n (Euclidean n) s)
    (hinverse : ∀ k, k ≤ q → periodicSobolevNorm k (Q₀ u) ≤
      Cinv k*(periodicSobolevNorm k u+T^(k-r₀)*‖u‖))
    (hsource : ∀ k ≤ q, periodicSobolevNorm k u ≤ M k*h*R^(k-r₀)) :
    let raw := nativeRealMeasuredInverseAdjoint μ φ m a hφ hm hms ha hK has Q₀ u
    MemLp (fun z ↦ (‖z.2‖ : ℂ)^q*raw z) 2 μ ∧
      lpNorm (fun z ↦ (‖z.2‖ : ℂ)^q*raw z) 2 μ ≤
        nativeAggregateSourceProfileConstant χ hχ hc hs Rbox B Cinv M Ctest q*h*R^(q-r₀) := by
  intro raw
  have hb := nativeRealMeasuredInverseAdjoint_radial_bounds μ φ m a hφ hm hms ha hK has
    L hL χ hχ hc hs hχK Rbox hbox Tfull hTfull hφsmooth hphase B hB q r₀ hT hamp hcoeff
    Q₀ u hregular Cinv hCinv hinverse
  have hP := sourceProfilePrefix_nonneg M hM q
  have hsource' : ∀ k ≤ q, periodicSobolevNorm k u ≤ (sourceProfilePrefix M q*h)*R^(k-r₀) := by
    intro k hk
    exact (hsource k hk).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (sourceProfile_le_prefix M hM hk) hh) (pow_nonneg (zero_le_one.trans hR) _))
  have hbound := hb.2.2 R (sourceProfilePrefix M q*h) hR hTR (mul_nonneg hP hh) hsource'
  have hC := nativeAggregateSourceConstant_nonneg χ hχ hc hs Rbox B Cinv hB hCinv q
  refine ⟨hb.1, hbound.trans ?_⟩
  calc
    _ ≤ nativeAggregateSourceConstant χ hχ hc hs Rbox B Cinv q*Ctest*((q : ℝ)+1)*
        (sourceProfilePrefix M q*h)*R^(q-r₀) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTfullBound hC) (by positivity))
        (mul_nonneg hP hh)) (pow_nonneg (zero_le_one.trans hR) _)
    _ = _ := by unfold nativeAggregateSourceProfileConstant; ring

end JanetCartan.PhysicalMean
