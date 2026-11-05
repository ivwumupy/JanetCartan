module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.GainOneBranches.Bounds
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.GainOneBranches.Locality

/-!
# Weighted primitive bounds for the actual gain-one transfer branches

The gain-one paragraph following
`app:ch_regular_base:eq:graph-derivative-transfer`. The original amplitude has
order minus one; the first phase derivative or literal adjoint covector has
order one. Their exact Leibniz expansion precedes all product estimates. Mixed
entries and derivatives of the actual inverse have order zero. Both physical
positions, all masks, and the literal adjoint's original coordinate order remain.

For a low joint reserve `μ₀`, one fixed enlargement to `μ₀+1` absorbs the
initial output derivative. The remaining excess is `s-1-k`, giving precisely
`H^((s-1-k)/(s-1))`. The explicit constant `branchConstant n μ₀ (s-1) C`
depends only on low data and orders, and is defined before the high bound and
primitive fields. The case `s=1` is stated separately without high inputs.

Individual weighted primitive profiles are explicit inputs, with producer
`jc-fio-sobolev-normalized-profiles`; `profile_of_interpolation` converts the
usual low/high endpoint data to this form. The parent
`jc-deduce-fio-strong-sobolev` must instantiate these profiles, apply its fixed
low L² reserve and the supplied actual weak identities, and reconstruct Sobolev
membership. No operator estimate or first-output branch bound is assumed here.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.GainOneBranches
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
open FirstOutputJets
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- Uniform weighted bounds for transfer branches initialized at the actual
forward first-output amplitude. Only original primitive profiles are inputs.
All nonzero jets are localized to the original carrier before using the inverse.
Source: gain one after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graph_branch_jet_norm_le_of_profiles (μ₀ s : ℕ) (hs : 1 ≤ s)
    (C : ℝ) (hC : 1 ≤ C) (H : ℝ) (hH : 1 ≤ H)
    (S : E → E → ℝ) (A : FullAmplitude n r)
    {K₀ : Set (E × E)} {F₀ : Set E}
    (hK₀ : IsCompact K₀) (hF₀ : IsClosed F₀) (hF₀0 : (0 : E) ∉ F₀)
    (hphase : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hinv : ∀ p ∈ K₀, ∀ η, η ≠ 0 → IsUnit (mixedPhaseMatrix S p.1 η).det)
    (hsmooth : ∀ p : Point n, p.2 ≠ 0 → ContDiffAt ℝ ∞ (uncurry A) p)
    (hsupport : ∀ p : Point n, p ∉ K₀ ×ˢ F₀ → uncurry A p = 0)
    (ρ : E → ℝ) (hρ : ∀ η, 1 ≤ ρ η)
    (hA : ∀ p ∈ K₀ ×ˢ F₀, ∀ v : List (Coordinate n), v.length ≤ μ₀ + s →
      (ρ p.2) ^ frequencyOrder v * ‖uncurry (jet v A) p‖ ≤
        C * profile (μ₀ + 1) (s - 1) H v.length / ρ p.2)
    (hphaseJets : ∀ p ∈ K₀ ×ˢ F₀, ∀ v : List (Coordinate n), v.length ≤ μ₀ + s →
      (ρ p.2) ^ frequencyOrder v * ‖uncurry (jet v (phasePrimitive S)) p‖ ≤
        C * profile (μ₀ + 1) (s - 1) H v.length * ρ p.2)
    (hscalar : ∀ p ∈ K₀ ×ˢ F₀, ∀ a (v : List (Coordinate n)), v.length ≤ μ₀ + s →
      (ρ p.2) ^ frequencyOrder v * ‖uncurry (jet v (scalarPrimitive S a)) p‖ ≤
        C * profile (μ₀ + 1) (s - 1) H v.length)
    (i : Fin n) (is : List (Fin n)) (his : is.length ≤ s - 1)
    (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
      (graphTransferDatum S) (graphFirstOutputAmplitude S A i) is)
    (w : List (Coordinate n)) (hw : w.length ≤ μ₀) (x y η : E) :
    (ρ η) ^ frequencyOrder w * ‖jet w p.1 x y η‖ ≤
      branchConstant n μ₀ (s - 1) C * H ^ (((s - 1 - p.2.length : ℕ) : ℝ) / ((s - 1 : ℕ) : ℝ)) := by
  by_cases hz : jet w p.1 x y η = 0
  · rw [hz, norm_zero, mul_zero]
    exact mul_nonneg (branchConstant_nonneg _ _ _ hC) (Real.rpow_nonneg (zero_le_one.trans hH) _)
  have hcarrier := tsupport_subset_carrier hK₀ hF₀ hsupport
  have hc : ((x, y), η) ∈ K₀ ×ˢ F₀ := hcarrier
    (support_graphFirstOutput S A i (graph_branch_jet_support is p hp w
      (subset_tsupport (uncurry (jet w p.1)) hz)))
  have hreg := mem_regularRegion_of_carrier hF₀0 hinv hc
  have hopen := isOpen_regularRegion hphase
  have hpr := smoothPrimitivesOn_regularRegion hphase (smooth_graphFirstOutput S A hphase hsmooth i)
  have he := (Weighted.graph_branch_bounded_expansion hopen hpr is p hp).mono
    (Nat.sub_le_sub_right his _) (branchTermCount_monotone n his) (Nat.add_le_add_right his 1)
  apply expansion_firstOutput_profile μ₀ (s - 1) p.2.length C H hC hH S
    (graphFirstOutputAmplitude S A i) p.1 (regularRegion S) hopen hpr he
    x y η hreg (ρ η) (zero_le_one.trans (hρ η)) ?_ ?_ w hw
  · intro v hv
    exact graphFirstOutput_jet_profile (μ₀ + 1) (s - 1) (μ₀ + (s - 1)) C H hC hH
      S A i (smoothAwayZero_of_joint A hsmooth) hphase x y η hreg.1 (ρ η) (hρ η)
      (fun z hz ↦ hA ((x, y), η) hc z (by omega))
      (fun z hz ↦ hphaseJets ((x, y), η) hc z (by omega)) v hv
  · intro a v hv
    exact hscalar ((x, y), η) hc a v (by omega)

/-- Uniform gain-one branch bounds for the literal adjoint, initialized at
`adjointFirstOutputAmplitude A i`, in original physical coordinates. The
Frobenius conjugate-transpose identities and actual covector bound are proved,
so only the original amplitude and actual mixed/inverse profiles remain inputs.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`, gain-one paragraph. -/
theorem adjoint_branch_jet_norm_le_of_profiles (μ₀ s : ℕ) (hs : 1 ≤ s)
    (C : ℝ) (hC : 1 ≤ C) (H : ℝ) (hH : 1 ≤ H)
    (S : E → E → ℝ) (A : FullAmplitude n r)
    {K₀ : Set (E × E)} {F₀ : Set E}
    (hK₀ : IsCompact K₀) (hF₀ : IsClosed F₀) (hF₀0 : (0 : E) ∉ F₀)
    (hphase : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hinv : ∀ p ∈ K₀, ∀ η, η ≠ 0 → IsUnit (mixedPhaseMatrix S p.1 η).det)
    (hsmooth : ∀ p : Point n, p.2 ≠ 0 → ContDiffAt ℝ ∞ (uncurry A) p)
    (hsupport : ∀ p : Point n, p ∉ K₀ ×ˢ F₀ → uncurry A p = 0)
    (ρ : E → ℝ) (hρ : ∀ η, 1 ≤ ρ η) (hηρ : ∀ η, ‖η‖ ≤ ρ η)
    (hA : ∀ p ∈ K₀ ×ˢ F₀, ∀ v : List (Coordinate n), v.length ≤ μ₀ + s →
      (ρ p.2) ^ frequencyOrder v * ‖uncurry (jet v A) p‖ ≤
        C * profile (μ₀ + 1) (s - 1) H v.length / ρ p.2)
    (hscalar : ∀ p ∈ K₀ ×ˢ F₀, ∀ a (v : List (Coordinate n)), v.length ≤ μ₀ + s →
      (ρ p.2) ^ frequencyOrder v * ‖uncurry (jet v (scalarPrimitive S a)) p‖ ≤
        C * profile (μ₀ + 1) (s - 1) H v.length)
    (i : Fin n) (is : List (Fin n)) (his : is.length ≤ s - 1)
    (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
      (adjointTransferDatum S) (adjointFirstOutputAmplitude A i) is)
    (w : List (Coordinate n)) (hw : w.length ≤ μ₀) (x y η : E) :
    (ρ η) ^ frequencyOrder w * ‖jet w p.1 x y η‖ ≤
      branchConstant n μ₀ (s - 1) C * H ^ (((s - 1 - p.2.length : ℕ) : ℝ) / ((s - 1 : ℕ) : ℝ)) := by
  by_cases hz : jet w p.1 x y η = 0
  · rw [hz, norm_zero, mul_zero]
    exact mul_nonneg (branchConstant_nonneg _ _ _ hC) (Real.rpow_nonneg (zero_le_one.trans hH) _)
  have hcarrier := tsupport_subset_carrier hK₀ hF₀ hsupport
  have hc : ((x, y), η) ∈ K₀ ×ˢ F₀ := hcarrier
    (support_adjointFirstOutput A i (adjoint_branch_jet_support is p hp w
      (subset_tsupport (uncurry (jet w p.1)) hz)))
  have hreg := mem_regularRegion_of_carrier hF₀0 hinv hc
  have hopen := isOpen_regularRegion hphase
  have hpr := smoothPrimitivesOn_regularRegion hphase (smooth_adjointFirstOutput A hsmooth i)
  have he := (Weighted.adjoint_branch_bounded_expansion hopen hpr is p hp).mono
    (Nat.sub_le_sub_right his _) (branchTermCount_monotone n his) (Nat.add_le_add_right his 1)
  apply expansion_firstOutput_profile μ₀ (s - 1) p.2.length C H hC hH S
    (adjointFirstOutputAmplitude A i) p.1 (regularRegion S) hopen hpr he
    x y η hreg (ρ η) (zero_le_one.trans (hρ η)) ?_ ?_ w hw
  · intro v hv
    exact adjointFirstOutput_jet_profile (μ₀ + 1) (s - 1) (μ₀ + (s - 1)) C H hC hH
      A i (smoothAwayZero_of_joint A hsmooth) x y η hreg.1 (ρ η) (hρ η) (hηρ η)
      (fun z hz ↦ hA ((x, y), η) hc z (by omega)) v hv
  · intro a v hv
    exact hscalar ((x, y), η) hc a v (by omega)

/-- The forward `s=1` case uses only low primitive jets through `μ₀+1`.
There are no further transfer derivatives and no high majorant. Source: the
gain-one paragraph following `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graph_firstOutput_low_jet_norm_le (μ₀ : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (S : E → E → ℝ) (A : FullAmplitude n r)
    {K₀ : Set (E × E)} {F₀ : Set E}
    (hK₀ : IsCompact K₀) (hF₀ : IsClosed F₀) (hF₀0 : (0 : E) ∉ F₀)
    (hphase : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hsmooth : ∀ p : Point n, p.2 ≠ 0 → ContDiffAt ℝ ∞ (uncurry A) p)
    (hsupport : ∀ p : Point n, p ∉ K₀ ×ˢ F₀ → uncurry A p = 0)
    (ρ : E → ℝ) (hρ : ∀ η, 1 ≤ ρ η)
    (hA : ∀ p ∈ K₀ ×ˢ F₀, ∀ v : List (Coordinate n), v.length ≤ μ₀ + 1 →
      (ρ p.2) ^ frequencyOrder v * ‖uncurry (jet v A) p‖ ≤ C / ρ p.2)
    (hphaseJets : ∀ p ∈ K₀ ×ˢ F₀, ∀ v : List (Coordinate n), v.length ≤ μ₀ + 1 →
      (ρ p.2) ^ frequencyOrder v * ‖uncurry (jet v (phasePrimitive S)) p‖ ≤ C * ρ p.2)
    (i : Fin n) (w : List (Coordinate n)) (hw : w.length ≤ μ₀) (x y η : E) :
    (ρ η) ^ frequencyOrder w * ‖jet w (graphFirstOutputAmplitude S A i) x y η‖ ≤
      (1 + (2 : ℝ) ^ μ₀) * C ^ 2 := by
  by_cases hz : jet w (graphFirstOutputAmplitude S A i) x y η = 0
  · rw [hz, norm_zero, mul_zero]
    positivity
  have hc : ((x, y), η) ∈ K₀ ×ˢ F₀ := tsupport_subset_carrier hK₀ hF₀ hsupport
    (support_graphFirstOutput S A i (tsupport_jet_subset w _
      (subset_tsupport (uncurry (jet w (graphFirstOutputAmplitude S A i))) hz)))
  have hη : η ≠ 0 := fun h ↦ hF₀0 (h ▸ hc.2)
  have hb := graphFirstOutput_jet_profile (μ₀ + 1) 0 μ₀ C 1 hC le_rfl S A i
    (smoothAwayZero_of_joint A hsmooth) hphase x y η hη (ρ η) (hρ η)
    (fun v hv ↦ by simpa only [uncurry, profile, Real.one_rpow, mul_one] using hA ((x, y), η) hc v hv)
    (fun v hv ↦ by simpa only [uncurry, profile, Real.one_rpow, mul_one] using hphaseJets ((x, y), η) hc v hv)
    w hw
  simpa only [profile, Real.one_rpow, mul_one] using hb

/-- The literal adjoint `s=1` case needs only the order-minus-one amplitude's
low jets; the physical covector and conjugate transpose are handled explicitly.
Source: `app:ch_regular_base:thm:actual-calculus`, gain-one paragraph. -/
theorem adjoint_firstOutput_low_jet_norm_le (μ₀ : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (A : FullAmplitude n r) {K₀ : Set (E × E)} {F₀ : Set E}
    (hK₀ : IsCompact K₀) (hF₀ : IsClosed F₀) (hF₀0 : (0 : E) ∉ F₀)
    (hsmooth : ∀ p : Point n, p.2 ≠ 0 → ContDiffAt ℝ ∞ (uncurry A) p)
    (hsupport : ∀ p : Point n, p ∉ K₀ ×ˢ F₀ → uncurry A p = 0)
    (ρ : E → ℝ) (hρ : ∀ η, 1 ≤ ρ η) (hηρ : ∀ η, ‖η‖ ≤ ρ η)
    (hA : ∀ p ∈ K₀ ×ˢ F₀, ∀ v : List (Coordinate n), v.length ≤ μ₀ + 1 →
      (ρ p.2) ^ frequencyOrder v * ‖uncurry (jet v A) p‖ ≤ C / ρ p.2)
    (i : Fin n) (w : List (Coordinate n)) (hw : w.length ≤ μ₀) (x y η : E) :
    (ρ η) ^ frequencyOrder w * ‖jet w (adjointFirstOutputAmplitude A i) x y η‖ ≤
      (1 + (2 : ℝ) ^ μ₀) * C ^ 2 := by
  by_cases hz : jet w (adjointFirstOutputAmplitude A i) x y η = 0
  · rw [hz, norm_zero, mul_zero]
    positivity
  have hc : ((x, y), η) ∈ K₀ ×ˢ F₀ := tsupport_subset_carrier hK₀ hF₀ hsupport
    (support_adjointFirstOutput A i (tsupport_jet_subset w _
      (subset_tsupport (uncurry (jet w (adjointFirstOutputAmplitude A i))) hz)))
  have hη : η ≠ 0 := fun h ↦ hF₀0 (h ▸ hc.2)
  have hb := adjointFirstOutput_jet_profile (μ₀ + 1) 0 μ₀ C 1 hC le_rfl A i
    (smoothAwayZero_of_joint A hsmooth) x y η hη (ρ η) (hρ η) (hηρ η)
    (fun v hv ↦ by simpa only [uncurry, profile, Real.one_rpow, mul_one] using hA ((x, y), η) hc v hv)
    w hw
  simpa only [profile, Real.one_rpow, mul_one] using hb

end JanetCartan.FourierIntegral.GainOneBranches
