module

public import JanetCartan.Iteration.PhysicalMean.NativeCross
public import JanetCartan.Iteration.PhysicalMean.InverseMomentProfile

/-!
# Actual aggregate radial input from the SAME current inverse

Compose the original HALFWEIGHTED aggregate real adjoint with the SAME
uncut current inverse, removing the artificial singleton input coordinate.
Both the unprofiled source moment budget and the sharp source-profile grade
are proved for this actual scalar native input. Consumers are the full high
quadratic branches and the fixed-cutoff linear normal profile
(`app:ch_mean_pairs:eq:raw-adjoint-moments`, `app:ch_mean_pairs:eq:block-bilinear`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.PhysicalMean

open Pseudodifferential PeriodicLocalL2 AmplitudeBound.PaperEstimates ContinuumRow

variable {n : ℕ}

/-- The predata aggregate inverse-moment constant. It depends on the fixed
physical cutoff/box, primitive moment profile, inverse profile and derivative
order, but not on history, samples, native measure, source or frequency. -/
def nativeAggregateSourceConstant
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ halfOpenCell n) (Rbox : ℝ) (B Cinv : ℕ → ℝ) (q : ℕ) : ℝ :=
  nativeRealMomentConstant χ hχ hc hs Rbox B q*((q : ℝ)+2)*
    (∑ k ∈ Finset.range (q+1), Cinv k)

/-- Positivity of the fixed actual aggregate source constant. -/
theorem nativeAggregateSourceConstant_nonneg
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ halfOpenCell n) (Rbox : ℝ) (B Cinv : ℕ → ℝ)
    (hB : ∀ k, 0 ≤ B k) (hCinv : ∀ k, 0 ≤ Cinv k) (q : ℕ) :
    0 ≤ nativeAggregateSourceConstant χ hχ hc hs Rbox B Cinv q := by
  have hmoment : 0 ≤ nativeRealMomentConstant χ hχ hc hs Rbox B q :=
    mul_nonneg (mul_nonneg (by norm_num) (sampledRadialMomentConstant_nonneg n Rbox B hB q))
      (sourceMomentConstant_nonneg χ hχ hc hs q)
  exact mul_nonneg (mul_nonneg hmoment (by positivity)) (Finset.sum_nonneg fun k _ ↦ hCinv k)

section ActualRow

variable {ι : Type*} [Fintype ι] [MetricSpace ι] [DiscreteTopology ι]
    [MeasurableSpace ι] [BorelSpace ι]
    (μ : Measure (ι × Euclidean (n-1))) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ : (ι × Euclidean (n-1)) → Euclidean n → ℝ) (m : (ι × Euclidean (n-1)) → ℝ)
    (a : Fin n → ι → Euclidean (n-1) → Euclidean n → ℂ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (ha : ∀ i k, ContDiff ℝ ∞ (Function.uncurry (a i k)))
    {K : Set (Euclidean n)} (hK : IsCompact K) (has : ∀ i k η, tsupport (a i k η) ⊆ K)

/-- The actual scalar-input measured vector row, built directly from its
complete original scalar kernels. The Unit coordinate appears only in the
existing matrix moment proof, never in this input Hilbert space. -/
def nativeMeasuredRow :
    Lp ℂ 2 μ →L[ℂ] Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)) :=
  nativeScalarRowsToVector μ (fun i ↦ sampledMomentOperator μ φ m
    (fun u ↦ a i u.1 u.2) hφ hm (continuous_originalSampledAmplitude (a i) (ha i))
      hms hK (fun u ↦ has i u.1 u.2))

/-- This is the SAME current inverse followed by the actual original real
measured adjoint, with no successful moment field or different inverse supplied. -/
def nativeRealMeasuredInverseAdjoint (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (u : OutputL2 n) : Lp ℂ 2 μ :=
  (transferOutputOperator (realQuadratureChannel
    (nativeMeasuredRow μ φ m a hφ hm hms ha hK has))).adjoint (Q₀ u)

variable (L : ι → Euclidean (n-1) → Euclidean (n-1) → Euclidean n → Euclidean n)
    (hL : ∀ i h, ContDiff ℝ ∞ (fun p : Euclidean (n-1) × Euclidean n ↦ L i p.1 h p.2))
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ halfOpenCell n) (hχK : ∀ x ∈ K, χ x = 1)
    (Rbox : ℝ) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
    (Tfull : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hTfull : ∀ f : Lp ℂ 2 μ, Tfull f =ᵐ[volume] fun x ↦ ∫ z,
      sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)) x z*f z ∂μ)
    (hφsmooth : ∀ z, ContDiff ℝ ∞ (φ z))
    (hphase : ∀ z, m z ≠ 0 → ∀ h x, x ∈ K →
      inner ℝ h z.2 = fderiv ℝ (φ z) x (L z.1 z.2 h x))
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (q r₀ : ℕ) {T : ℝ} (hT : 1 ≤ T)
    (hamp : ∀ i k η, m (k,η) ≠ 0 → ∀ x ∈ K, ∀ s,
      ‖iteratedFDeriv ℝ s (a i k η) x‖ ≤ B s*T^(s-(r₀+(n/2+1))))
    (hcoeff : ∀ k η, m (k,η) ≠ 0 → ∀ h, ‖h‖ ≤ 1 → ∀ x ∈ K, ∀ s,
      ‖iteratedFDeriv ℝ s (L k η h) x‖ ≤ B s*T^(s-(r₀+(n/2+1))))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (u : OutputL2 n)
    (hregular : ∀ s, Q₀ u ∈ periodicSobolevLevel n (Euclidean n) s)
    (Cinv : ℕ → ℝ) (hCinv : ∀ k, 0 ≤ Cinv k)
    (hinverse : ∀ k, k ≤ q → periodicSobolevNorm k (Q₀ u) ≤
      Cinv k*(periodicSobolevNorm k u + T^(k-r₀)*‖u‖))

include hL hχ hc hs hχK hbox hTfull hφsmooth hphase hB hT hamp hcoeff hregular hCinv hinverse

/-- The actual scalar native real adjoint after the SAME current inverse has
its aggregate integer moment, with genuine L² membership. The first bound is
the unprofiled source convolution needed by the linear normal. The second
inserts the already-produced source profile for balanced high quadratic terms.
Both apply the ACTUAL CurrentAdjoint theorem and the ACTUAL inverse moment
convolution; no radial input norm, hcoord, or successful block bound is assumed. -/
theorem nativeRealMeasuredInverseAdjoint_radial_bounds :
    let raw := nativeRealMeasuredInverseAdjoint μ φ m a hφ hm hms ha hK has Q₀ u
    MemLp (fun z ↦ (‖z.2‖ : ℂ)^q*raw z) 2 μ ∧
      lpNorm (fun z ↦ (‖z.2‖ : ℂ)^q*raw z) 2 μ ≤
        nativeAggregateSourceConstant χ hχ hc hs Rbox B Cinv q*‖Tfull‖*
          ∑ k ∈ Finset.range (q+1), T^(q-k-r₀)*periodicSobolevNorm k u ∧
      ∀ R M : ℝ, 1 ≤ R → T ≤ R → 0 ≤ M →
        (∀ k, k ≤ q → periodicSobolevNorm k u ≤ M*R^(k-r₀)) →
        lpNorm (fun z ↦ (‖z.2‖ : ℂ)^q*raw z) 2 μ ≤
          nativeAggregateSourceConstant χ hχ hc hs Rbox B Cinv q*‖Tfull‖*((q : ℝ)+1)*M*R^(q-r₀) := by
  intro raw
  let entries := fun i ↦ sampledMomentOperator μ φ m (fun z ↦ a i z.1 z.2) hφ hm
    (continuous_originalSampledAmplitude (a i) (ha i)) hms hK (fun z ↦ has i z.1 z.2)
  have he := nativeRealScalarRow_adjoint_eq_matrixCoordinate μ entries
    (nativeMeasuredRow μ φ m a hφ hm hms ha hK has)
    (fun f i ↦ nativeScalarRowsToVector_coordinate μ entries f i) (Q₀ u)
  have hmom := nativeRealSampledAdjoint_radial_L2_bound μ φ m (fun i (_ : Unit) ↦ a i) L
    hφ hm hms (fun i _ ↦ ha i) hL hK (fun i _ ↦ has i)
    χ hχ hc hs hχK Rbox hbox Tfull hTfull hφsmooth hphase B hB q r₀ hT
    (fun i _ ↦ hamp i) hcoeff (Q₀ u) hregular ()
  dsimp only at hmom
  change raw = _ at he
  have hactual : MemLp (fun z ↦ (‖z.2‖ : ℂ)^q*raw z) 2 μ ∧
      lpNorm (fun z ↦ (‖z.2‖ : ℂ)^q*raw z) 2 μ ≤
        nativeRealMomentConstant χ hχ hc hs Rbox B q*‖Tfull‖*
          ∑ k ∈ Finset.range (q+1), T^(q-k-r₀)*periodicSobolevNorm k (Q₀ u) := by
    constructor
    · rw [he]
      exact hmom.1
    · rw [he]
      exact hmom.2
  have hc0 : 0 ≤ nativeRealMomentConstant χ hχ hc hs Rbox B q :=
    mul_nonneg (mul_nonneg (by norm_num) (sampledRadialMomentConstant_nonneg n Rbox B hB q))
      (sourceMomentConstant_nonneg χ hχ hc hs q)
  have hc1 : 0 ≤ nativeRealMomentConstant χ hχ hc hs Rbox B q*‖Tfull‖ :=
    mul_nonneg hc0 (norm_nonneg Tfull)
  refine ⟨hactual.1, ?_, ?_⟩
  · exact (hactual.2.trans (mul_le_mul_of_nonneg_left
      (inverseSource_moment_sum_le Q₀ u Cinv hCinv q r₀ hT hinverse) hc1)).trans_eq
        (by dsimp only [nativeAggregateSourceConstant]; ring)
  · intro R M hR hTR hM hsource
    exact (hactual.2.trans (mul_le_mul_of_nonneg_left
      (inverseSource_profile_moment_sum_le Q₀ u Cinv hCinv q r₀ hT hR hTR M hM hinverse hsource) hc1)).trans_eq
        (by dsimp only [nativeAggregateSourceConstant]; ring)

end ActualRow
end JanetCartan.PhysicalMean
