module

public import JanetCartan.Iteration.PhysicalMean.MomentPhysicalProfiles
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.Coordinates

/-!
# The same modified amplitude family for every original input frequency

The fixed templates construct the physical amplitudes used in
`app:ch_mean_pairs:eq:raw-adjoint-moments`. Their joint regularity follows from
that of the original amplitude and inverse phase directions. The finite test
budget spends exactly `ell` of the fixed reserve, independent of the length
of the moment word, cutoff, history and sample.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.PhysicalMean

open ContinuumAdjoint.DerivativeKernels ContinuumRow AmplitudeBound Pseudodifferential

variable {n : ℕ}

/-- Evaluate a fixed template at the SAME original sampled parameter and
frequency. The extra carrier coordinate in the shared syntax is frozen at
zero and is never differentiated in this initial-only word. -/
def physicalMomentAmplitude {P : Type*} (t : AdjointMomentTemplate n)
    (a : P → Euclidean n → ℂ)
    (L : P → Euclidean (n - 1) → Euclidean n → Euclidean n)
    (p : P) (x : Euclidean n) : ℂ :=
  t.1.evaluate (fun _ y h ↦ L p h y) (fun _ _ _ ↦ 0) (fun _ y _ ↦ a p y) 0 (0, x)

/-- The constructed modified amplitude is jointly smooth if the original
amplitude and inverse directions are. No choice of a template depends on the
frequency, and no frequency derivative enters the later norm estimate. -/
theorem contDiff_physicalMomentAmplitude
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (t : AdjointMomentTemplate n) (a : P → Euclidean n → ℂ)
    (L : P → Euclidean (n - 1) → Euclidean n → Euclidean n)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hL : ∀ h, ContDiff ℝ ∞ (fun q : P × Euclidean n ↦ L q.1 h q.2)) :
    ContDiff ℝ ∞ (Function.uncurry (physicalMomentAmplitude t a L)) := by
  have he := contDiff_adjointMomentExpression_family
    (fun p (_ : CarrierParameter) (x : Euclidean n) h ↦ L p h x)
    (fun (_ : P) (_ : CarrierParameter) (_ : Euclidean n) (_ : CarrierParameter) ↦ (0 : Euclidean n))
    (fun p (q : AdjointJetPoint n) ↦ a p q.2)
    (ha.comp (contDiff_fst.prodMk contDiff_snd.snd))
    (fun d j ↦ ?_) t.1
  · exact he.comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd))
  · cases d with
    | initial h =>
        exact Complex.ofRealCLM.contDiff.comp
          ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j).contDiff.comp
            ((hL h).comp (contDiff_fst.prodMk contDiff_snd.snd)))
    | carrier h => exact contDiff_const

/-- The original compact measurement support is unchanged for each actual
frequency-dependent template (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem physicalMomentAmplitude_supported
    {P : Type*} (ds : List (Euclidean (n - 1)))
    (t : AdjointMomentTemplate n)
    (ht : t ∈ adjointMomentTemplates (ds.map InitialCarrierDerivative.initial))
    (a : P → Euclidean n → ℂ)
    (L : P → Euclidean (n - 1) → Euclidean n → Euclidean n)
    {K : Set (Euclidean n)} (hK : IsClosed K)
    (ha : ∀ p, ContDiff ℝ ∞ (a p)) (has : ∀ p, tsupport (a p) ⊆ K)
    (hL : ∀ p h, ContDiff ℝ ∞ (L p h)) (p : P) :
    ContDiff ℝ ∞ (physicalMomentAmplitude t a L p) ∧
      tsupport (physicalMomentAmplitude t a L p) ⊆ K := by
  have hr := sampledAdjointMomentTemplate_regular hK (ha p) (has p) (hL p) ds t ht
  exact ⟨(hr.smooth 0).comp (contDiff_const.prodMk contDiff_id), hr.tsupport_subset hK 0 0⟩

/-- The finite scalar amplitude-test constant is chosen before the original
functions and their scales; only the word and fixed physical test order enter. -/
def momentAmplitudeTestConstant (B : ℕ → ℝ) (ds : List (Euclidean (n - 1))) (ell : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (ell + 1), adjointMomentJetConstant B
    (ds.map InitialCarrierDerivative.initial) q

/-- Nonnegativity of the fixed amplitude-test budget. -/
theorem momentAmplitudeTestConstant_nonneg (B : ℕ → ℝ) (hB : ∀ q, 0 ≤ B q)
    (ds : List (Euclidean (n - 1))) (ell : ℕ) : 0 ≤ momentAmplitudeTestConstant B ds ell :=
  Finset.sum_nonneg (fun q _ ↦ adjointMomentJetConstant_nonneg B hB _ q)

/-- The original physical primitive reserve gives the complete finite
Cartesian test budget of each actual moment amplitude. The power is exactly
`q-i-s0`, not `q-i`; all constants are uniform in the frozen frequency and
sample (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem physicalMomentAmplitude_coordinate_jet_le
    {P : Type*} (B : ℕ → ℝ) (hB : ∀ q, 0 ≤ B q)
    (ds : List (Euclidean (n - 1))) (t : AdjointMomentTemplate n)
    (ht : t ∈ adjointMomentTemplates (ds.map InitialCarrierDerivative.initial))
    (a : P → Euclidean n → ℂ)
    (L : P → Euclidean (n - 1) → Euclidean n → Euclidean n)
    (ha : ∀ p, ContDiff ℝ ∞ (a p)) (hL : ∀ p h, ContDiff ℝ ∞ (L p h))
    (ell r₀ : ℕ) {T : ℝ} (hT : 1 ≤ T)
    (hamp : ∀ p x i, ‖iteratedFDeriv ℝ i (a p) x‖ ≤ B i * T ^ (i - (r₀ + ell)))
    (hcoeff : ∀ p h, h ∈ ds → ∀ x i,
      ‖iteratedFDeriv ℝ i (L p h) x‖ ≤ B i * T ^ (i - (r₀ + ell)))
    (p : P) (is : List (Fin n)) (his : is.length ≤ ell) (x : Euclidean n) :
    ‖euclideanCoordinateDerivList is (physicalMomentAmplitude t a L p) x‖ ≤
      momentAmplitudeTestConstant B ds ell * T ^ (ds.length - t.2.length - r₀) := by
  have hf : ∀ d j, ContDiff ℝ ∞
      (branchField (fun _ y h ↦ L p h y) (fun _ _ _ ↦ 0) d j) := by
    intro d j
    cases d with
    | initial h =>
        exact Complex.ofRealCLM.contDiff.comp
          (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j).contDiff.comp (hL p h)).comp contDiff_snd)
    | carrier h => exact contDiff_const
  have hs : ContDiff ℝ ∞ (physicalMomentAmplitude t a L p) :=
    (t.1.contDiff_evaluate _ _ _ 0 ((ha p).comp contDiff_snd) hf).comp
      (contDiff_const.prodMk contDiff_id)
  apply (norm_euclideanCoordinateDerivList_le_iteratedFDeriv hs is x).trans
  have hb := sampledAdjointMomentTemplate_physical_jet_le B hB ds t ht (a p) (ha p)
    (L p) (hL p) (r₀ + ell) hT x (hamp p x) (fun h hh i ↦ hcoeff p h hh x i) is.length
  apply hb.trans
  apply mul_le_mul
  · exact Finset.single_le_sum (fun q _ ↦ adjointMomentJetConstant_nonneg B hB _ q)
      (Finset.mem_range.mpr (by omega))
  · apply pow_le_pow_right₀ hT
    omega
  · positivity
  · exact momentAmplitudeTestConstant_nonneg B hB ds ell

/-- The modified amplitude needs quantitative primitive jets only on the
ORIGINAL physical support. All its physical derivatives vanish off that
closed support; no profile of the global smooth localization is imposed. -/
theorem physicalMomentAmplitude_coordinate_jet_le_onSupport
    {P : Type*} (B : ℕ → ℝ) (hB : ∀ q, 0 ≤ B q)
    (ds : List (Euclidean (n - 1))) (t : AdjointMomentTemplate n)
    (ht : t ∈ adjointMomentTemplates (ds.map InitialCarrierDerivative.initial))
    (a : P → Euclidean n → ℂ)
    (L : P → Euclidean (n - 1) → Euclidean n → Euclidean n)
    (ha : ∀ p, ContDiff ℝ ∞ (a p)) (hL : ∀ p h, ContDiff ℝ ∞ (L p h))
    {K : Set (Euclidean n)} (hK : IsClosed K) (has : ∀ p, tsupport (a p) ⊆ K)
    (ell r₀ : ℕ) {T : ℝ} (hT : 1 ≤ T) (p : P)
    (hamp : ∀ x ∈ K, ∀ i, ‖iteratedFDeriv ℝ i (a p) x‖ ≤ B i * T ^ (i - (r₀ + ell)))
    (hcoeff : ∀ h ∈ ds, ∀ x ∈ K, ∀ i,
      ‖iteratedFDeriv ℝ i (L p h) x‖ ≤ B i * T ^ (i - (r₀ + ell)))
    (is : List (Fin n)) (his : is.length ≤ ell) (x : Euclidean n) :
    ‖euclideanCoordinateDerivList is (physicalMomentAmplitude t a L p) x‖ ≤
      momentAmplitudeTestConstant B ds ell * T ^ (ds.length - t.2.length - r₀) := by
  obtain ⟨hs, hsupport⟩ := physicalMomentAmplitude_supported ds t ht a L hK ha has hL p
  apply (norm_euclideanCoordinateDerivList_le_iteratedFDeriv hs is x).trans
  by_cases hx : x ∈ K
  · have hb := sampledAdjointMomentTemplate_physical_jet_le B hB ds t ht (a p) (ha p)
      (L p) (hL p) (r₀ + ell) hT x (hamp x hx) (fun h hh i ↦ hcoeff h hh x hx i) is.length
    apply hb.trans
    apply mul_le_mul
    · exact Finset.single_le_sum (fun q _ ↦ adjointMomentJetConstant_nonneg B hB _ q)
        (Finset.mem_range.mpr (by omega))
    · apply pow_le_pow_right₀ hT
      omega
    · positivity
    · exact momentAmplitudeTestConstant_nonneg B hB ds ell
  · have hz : iteratedFDeriv ℝ is.length (physicalMomentAmplitude t a L p) x = 0 :=
      Function.notMem_support.mp (fun h ↦ hx (hsupport (support_iteratedFDeriv_subset is.length h)))
    rw [hz, norm_zero]
    exact mul_nonneg (momentAmplitudeTestConstant_nonneg B hB ds ell) (by positivity)

/-- On a finite or discrete sample family, smoothness is needed only in
the physical and original frequency variables of EACH fixed sample. The
assembled amplitude is continuous without any sample-index derivative
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem continuous_discrete_physicalMomentAmplitude
    {ι P : Type*} [TopologicalSpace ι] [DiscreteTopology ι]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (t : AdjointMomentTemplate n) (a : ι → P → Euclidean n → ℂ)
    (L : ι → P → Euclidean (n - 1) → Euclidean n → Euclidean n)
    (ha : ∀ i, ContDiff ℝ ∞ (Function.uncurry (a i)))
    (hL : ∀ i h, ContDiff ℝ ∞ (fun q : P × Euclidean n ↦ L i q.1 h q.2)) :
    Continuous (Function.uncurry (physicalMomentAmplitude t
      (fun u : ι × P ↦ a u.1 u.2) (fun u : ι × P ↦ L u.1 u.2))) := by
  have hc : Continuous (fun q : ι × (P × Euclidean n) ↦
      physicalMomentAmplitude t (a q.1) (L q.1) q.2.1 q.2.2) :=
    continuous_prod_of_discrete_left.mpr
      (fun i ↦ (contDiff_physicalMomentAmplitude t (a i) (L i) (ha i) (hL i)).continuous)
  exact hc.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))

private theorem evaluate_frozen_frequency_eq
    (e : AdjointCoefficientExpression n)
    (L : Euclidean (n - 1) → Euclidean n → Euclidean n) (a : Euclidean n → ℂ)
    (η : Euclidean (n - 1)) :
    e.evaluate (fun _ x h ↦ L h x) (fun _ _ _ ↦ 0) (fun _ x _ ↦ a x) η =
      e.evaluate (fun _ x h ↦ L h x) (fun _ _ _ ↦ 0) (fun _ x _ ↦ a x) 0 := by
  induction e with
  | amplitude | field _ _ => rfl
  | add e f he hf | mul e f he hf => simp only [AdjointCoefficientExpression.evaluate, he, hf]
  | neg e he | deriv h e he => simp only [AdjointCoefficientExpression.evaluate, he]

/-- The FIXED template amplitudes realize the full original moment exactly.
Both the inverse directions and the amplitude may depend on the same frozen
sample and frequency. No pointwise choice or new source occurs
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem physicalMomentAmplitude_sum_realizes
    {P : Type*} (ds : List (Euclidean (n - 1)))
    (a : P → Euclidean n → ℂ)
    (L : P → Euclidean (n - 1) → Euclidean n → Euclidean n)
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (p : P) {φ : Euclidean n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (ha : ContDiff ℝ ∞ (a p)) (has : tsupport (a p) ⊆ K)
    (hL : ∀ h, ContDiff ℝ ∞ (L p h))
    (v : Euclidean n → ℂ) (hv : ContDiff ℝ ∞ v) (η : Euclidean (n - 1))
    (hphase : ∀ h x, x ∈ K → inner ℝ h η = fderiv ℝ φ x (L p h x)) :
    ((adjointMomentTemplates (ds.map InitialCarrierDerivative.initial)).map
      (fun t ↦ chartAdjoint φ (physicalMomentAmplitude t a L p)
        (euclideanCoordinateDerivList t.2 v))).sum =
      (ds.map (fun h ↦ Complex.I * (inner ℝ h η : ℂ))).prod * chartAdjoint φ (a p) v := by
  have hfield : ∀ d j, ContDiff ℝ ∞
      (branchField (fun _ x h ↦ L p h x) (fun _ _ _ ↦ 0) d j) := by
    intro d j
    cases d with
    | initial h =>
        exact Complex.ofRealCLM.contDiff.comp
          (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j).contDiff.comp (hL h)).comp contDiff_snd)
    | carrier h => exact contDiff_const
  have he := sampledAdjointMomentExpansion_realizes hK hφ ha hv has hL η hphase ds
  unfold sampledAdjointMomentExpansion at he
  rw [← map_adjointMomentTemplates_eq_expansion _ _ _
    (fun _ ↦ ha.comp contDiff_snd) hfield, List.map_map] at he
  convert he using 1
  congr 1
  apply List.map_congr_left
  intro t _
  unfold AdjointDerivativeTerm.realize AdjointMomentTemplate.toTerm physicalMomentAmplitude
  dsimp only [Function.comp_def]
  rw [evaluate_frozen_frequency_eq t.1 (L p) (a p) η]

end JanetCartan.PhysicalMean
