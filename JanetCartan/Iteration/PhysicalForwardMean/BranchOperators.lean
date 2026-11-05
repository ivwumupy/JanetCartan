module

public import JanetCartan.Iteration.PhysicalForwardMean.BranchProfiles
public import JanetCartan.Iteration.PhysicalMean.MomentRows

/-!
# Native scalar bounds for the exact forward physical branches

Each binary branch remains a row on the SAME sampled-shell measure, with the
SAME original full phase and input mask. Only its physical coefficient is
modified. The original scalar tester bounds the whole row at once; there is
no sum over samples or shells. All quantitative hypotheses are restricted to
the original active input mask and original physical support. Consumer: Step 3
of `app:ch_mean_pairs:eq:block-normal` and Step 4 of `block-fields`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.PhysicalForwardMean
open RawPrimary.SliceBounds PhysicalMean AmplitudeBound AmplitudeBound.PaperEstimates

variable {n : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
local notation "E" => Euclidean n

private theorem coordinateDerivList_star (js : List (Fin n)) (f : E → ℂ) :
    euclideanCoordinateDerivList js (fun y ↦ star (f y)) =
      fun y ↦ star (euclideanCoordinateDerivList js f y) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
      simp only [euclideanCoordinateDerivList, ih, fderiv_star,
        ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, starL'_apply]

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
/-- The original branch and its conjugate retain the compact physical support;
qualitative smoothness comes from the exact binary differentiation recursion
(`app:ch_mean_pairs:eq:block-normal`). -/
theorem forwardBranch_smooth_supported (θ : X → E → ℝ) (A : X → E → ℂ)
    (hθ : ∀ u, ContDiff ℝ ∞ (θ u)) (hA : ∀ u, ContDiff ℝ ∞ (A u))
    {K : Set E} (hK : IsClosed K) (hAK : ∀ u, tsupport (A u) ⊆ K)
    {s : ℕ} (v : Fin s → E) (b : SliceDerivativeBranch s) (u : X) :
    ContDiff ℝ ∞ (fun x ↦ star (sliceDerivativeAmplitude (θ u) (A u) v b x)) ∧
      tsupport (fun x ↦ star (sliceDerivativeAmplitude (θ u) (A u) v b x)) ⊆ K := by
  have hc : ContDiff ℝ ∞ (sliceDerivativeAmplitude (θ u) (A u) v b) :=
    contDiffOn_univ.mp (contDiffOn_sliceDerivativeAmplitude isOpen_univ
      (hθ u).contDiffOn (hA u).contDiffOn v b)
  refine ⟨(starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp hc, ?_⟩
  apply closure_minimal _ hK
  intro x hx
  apply hAK u
  apply tsupport_sliceDerivativeAmplitude_subset (θ u) (A u) v b
  exact subset_tsupport _ (fun hz ↦ hx (by simp only [hz, star_zero]))

/-- The full original scalar row bounds each exact differentiated coefficient,
with precisely `T^(s-phaseCount-s0)`. Only the qualitative joint continuity of
the explicitly computed branch is passed here; the original smooth parameter
families produce it. No derivative or bound in the source variable occurs
(`new:eq:amplitude-test`, `app:ch_mean_pairs:eq:block-normal`). -/
theorem norm_forwardBranchOperator_le_scalarTest
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ θ : X → E → ℝ) (m : X → ℝ) (A : X → E → ℂ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (hθ : ∀ u, ContDiff ℝ ∞ (θ u)) (hA : ∀ u, ContDiff ℝ ∞ (A u))
    {K : Set E} (hK : IsCompact K) (hAK : ∀ u, tsupport (A u) ⊆ K)
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχK : ∀ x ∈ K, χ x = 1) (Rbox : ℝ) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
    {s s0 : ℕ} {T : ℝ} (hT : 1 ≤ T) (a p : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j)
    (hAj : ∀ u, m u ≠ 0 → ∀ x ∈ K, ∀ j ≤ s + (n / 2 + 1),
      ‖iteratedFDeriv ℝ j (A u) x‖ ≤ a j * T ^ (j - (s0 + (n / 2 + 1))))
    (hθj : ∀ u, m u ≠ 0 → ∀ x ∈ K, ∀ j, 1 ≤ j → j ≤ s + (n / 2 + 1) →
      ‖iteratedFDeriv ℝ j (θ u) x‖ ≤ p j * T ^ (j - 1 - (s0 + (n / 2 + 1))))
    (v : Fin s → E) (hv : ∀ i, ‖v i‖ ≤ 1) (b : SliceDerivativeBranch s)
    (hbc : Continuous (fun q : X × E ↦ sliceDerivativeAmplitude (θ q.1) (A q.1) v b q.2))
    (T0 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (hT0 : ∀ f : Lp ℂ 2 μ, T0 f =ᵐ[volume] fun x ↦ ∫ u,
      sampledMomentKernel φ m (fun _ y ↦ (χ y : ℂ)) x u * f u ∂μ) :
    let hb := forwardBranch_smooth_supported θ A hθ hA hK.isClosed hAK v b
    ‖sampledMomentOperator μ φ m
      (fun u x ↦ star (sliceDerivativeAmplitude (θ u) (A u) v b x))
      hφ hm hbc.star hms hK (fun u ↦ (hb u).2)‖ ≤
        (finiteRowAmplitudeConstant n Rbox * forwardBranchConstant (n / 2 + 1) a p b) *
          ‖T0‖ * T ^ (s - b.phaseCount - s0) := by
  intro hb
  have hbase := norm_sampledMomentOperator_le_scalarTest_onMask μ φ m
    (fun u x ↦ star (sliceDerivativeAmplitude (θ u) (A u) v b x))
    hφ hm hbc.star hms hK (fun u ↦ (hb u).2) χ hχ hχs
    (fun u x hx ↦ hχK x ((hb u).2 (subset_tsupport _ hx))) Rbox
    (forwardBranchConstant (n / 2 + 1) a p b * T ^ (s - b.phaseCount - s0))
    (mul_nonneg (forwardBranchConstant_nonneg b ha hp) (by positivity))
    (fun u ↦ (hb u).1)
    (fun u x hx i ↦ hbox x ((hb u).2 (subset_tsupport _ hx)) i)
    (fun u hu ds hds x ↦ ?_) T0 hT0
  · convert hbase using 1
    ring
  · simpa only [coordinateDerivList_star, norm_star] using
      coordinateJet_branch_le_of_localPrimitiveJets (hθ u) (hA u) (hAK u) hT ha hp
        (hAj u hu) (hθj u hu) v hv b ds hds x

end JanetCartan.PhysicalForwardMean
