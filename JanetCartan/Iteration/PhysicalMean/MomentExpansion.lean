module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Iteration

/-!
# Exact sampled-adjoint frequency moments

For `app:ch_mean_pairs:eq:raw-adjoint-moments`, freeze one ORIGINAL sampled
parameter and one ORIGINAL frequency. The full phase difference may depend
nonlinearly on that frequency, and its inverse phase-derivative directions
may do so as well. No frequency or sample-index derivatives are taken.

The already proved compact integration-by-parts recursion then constructs
all modified amplitudes: a word of length `q` leaves at most `q` physical
derivatives on the datum and preserves the same compact measurement support.
The phase identity is the primitive inverse-matrix identity for the actual
full phase; quantitative coefficient bounds and the common scalar operator
estimate remain inputs to the subsequent norm estimate, not assumptions of
this exact expansion.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.PhysicalMean

open ContinuumAdjoint.DerivativeKernels ContinuumRow AmplitudeBound NormalComparison

variable {n : ℕ}

/-- The actual finite integration-by-parts expansion with the sampled
parameter and frequency frozen. The directions may depend on BOTH of those
spectators; only the physical variable is differentiated. -/
def sampledAdjointMomentExpansion
    (L : Euclidean (n - 1) → Euclidean n → Euclidean n)
    (ds : List (Euclidean (n - 1))) (a : Euclidean n → ℂ) : List (AdjointDerivativeTerm n) :=
  adjointDerivativeExpansion (fun _ x h ↦ L h x) (fun _ _ _ ↦ 0)
    (ds.map InitialCarrierDerivative.initial) (fun _ x _ ↦ a x)

/-- Each actual expanded amplitude remains smooth and on the original compact
measurement support. Derivatives of the inverse phase matrix and of the
original amplitude are both retained, as required by Step 2 of
`app:ch_mean_pairs:prop:canonical-estimates`. -/
theorem sampledAdjointMomentExpansion_regular
    {K : Set (Euclidean n)} (hK : IsClosed K) {a : Euclidean n → ℂ}
    (ha : ContDiff ℝ ∞ a) (has : tsupport a ⊆ K)
    {L : Euclidean (n - 1) → Euclidean n → Euclidean n}
    (hL : ∀ h, ContDiff ℝ ∞ (L h))
    (ds : List (Euclidean (n - 1))) (t : AdjointDerivativeTerm n)
    (ht : t ∈ sampledAdjointMomentExpansion L ds a) :
    t.dataDerivatives.length ≤ ds.length ∧ SmoothSupportedAdjointAmplitude K t.amplitude := by
  have ha' : SmoothSupportedAdjointAmplitude K (fun _ x _ ↦ a x) :=
    ⟨fun _ ↦ ha.comp contDiff_snd,
      fun _ x _ hx ↦ image_eq_zero_of_notMem_tsupport (fun h ↦ hx (has h))⟩
  refine ⟨?_, smoothSupported_adjointDerivativeExpansion hK ha'
    (fun h ↦ (hL h).comp contDiff_snd) (fun _ ↦ contDiff_const) _ t ht⟩
  simpa only [List.length_map] using dataDerivatives_length_le_expansion
    (fun _ x h ↦ L h x) (fun _ _ _ ↦ 0) (ds.map InitialCarrierDerivative.initial)
    (fun _ x _ ↦ a x) t ht

private theorem sum_map_flatMap {α β : Type*} (ts : List α) (g : α → List β) (f : β → ℂ) :
    ((ts.flatMap g).map f).sum = (ts.map (fun t ↦ ((g t).map f).sum)).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, ih]

/-- The literal sampled-adjoint moment is the sum of the constructed compact
amplitude terms. The hypothesis is only the physical phase-derivative
identity on the measurement support, not a moment bound or an asserted
expansion (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem sampledAdjointMomentExpansion_realizes
    {K : Set (Euclidean n)} (hK : IsCompact K)
    {φ : Euclidean n → ℝ} {a v : Euclidean n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (ha : ContDiff ℝ ∞ a) (hv : ContDiff ℝ ∞ v)
    (has : tsupport a ⊆ K)
    {L : Euclidean (n - 1) → Euclidean n → Euclidean n}
    (hL : ∀ h, ContDiff ℝ ∞ (L h)) (η : Euclidean (n - 1))
    (hphase : ∀ h x, x ∈ K → inner ℝ h η = fderiv ℝ φ x (L h x))
    (ds : List (Euclidean (n - 1))) :
    ((sampledAdjointMomentExpansion L ds a).map
      (fun t ↦ t.realize (fun _ x _ ↦ φ x) v (0, η))).sum =
      (ds.map (fun h ↦ Complex.I * (inner ℝ h η : ℂ))).prod * chartAdjoint φ a v := by
  induction ds with
  | nil => simp [sampledAdjointMomentExpansion, adjointDerivativeExpansion,
      AdjointDerivativeTerm.realize, euclideanCoordinateDerivList]
  | cons h ds ih =>
    have hstep (t : AdjointDerivativeTerm n) (ht : t ∈ sampledAdjointMomentExpansion L ds a) :
        ((differentiateAdjointTerm (fun _ x k ↦ L k x) (fun _ _ _ ↦ 0)
          (.initial h) t).map (fun q ↦ q.realize (fun _ x _ ↦ φ x) v (0, η))).sum =
          (Complex.I * (inner ℝ h η : ℂ)) * t.realize (fun _ x _ ↦ φ x) v (0, η) := by
      have hreg := (sampledAdjointMomentExpansion_regular hK.isClosed ha has hL ds t ht).2
      rw [sum_realize_differentiateAdjointTerm hK hreg
        (fun k ↦ (hL k).comp contDiff_snd) (fun _ ↦ contDiff_const)
        (fun _ ↦ hφ.comp contDiff_snd) hv (.initial h) (0, η)]
      exact (chartAdjoint_initial_trade hφ
        ((hreg.smooth η).comp (contDiff_const.prodMk contDiff_id))
        (contDiff_euclideanCoordinateDerivList hv _) (hL h)
        (hK.of_isClosed_subset (isClosed_tsupport _) (hreg.tsupport_subset hK.isClosed 0 η))
        (inner ℝ h η) (fun x hx ↦ hphase h x
          (hreg.tsupport_subset hK.isClosed 0 η (subset_tsupport _ hx)))).symm
    change (((sampledAdjointMomentExpansion L ds a).flatMap
      (differentiateAdjointTerm (fun _ x k ↦ L k x) (fun _ _ _ ↦ 0) (.initial h))).map
        (fun t ↦ t.realize (fun _ x _ ↦ φ x) v (0, η))).sum = _
    rw [sum_map_flatMap]
    calc
      _ = ((sampledAdjointMomentExpansion L ds a).map
          (fun t ↦ (Complex.I * (inner ℝ h η : ℂ)) * t.realize (fun _ x _ ↦ φ x) v (0, η))).sum := by
        congr 1
        exact List.map_congr_left hstep
      _ = (Complex.I * (inner ℝ h η : ℂ)) *
          ((sampledAdjointMomentExpansion L ds a).map
            (fun t ↦ t.realize (fun _ x _ ↦ φ x) v (0, η))).sum := by
        exact List.sum_map_mul_left _ _ _
      _ = _ := by rw [ih]; simp only [List.map_cons, List.prod_cons, mul_assoc]

end JanetCartan.PhysicalMean
