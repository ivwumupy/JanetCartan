module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.ExtendedReducedProfiles
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.FiberBounds

/-!
# Original history profiles for the retained direct amplitudes

The consumer is the primitive amplitude grade in
`IntegratedEnvelope.Assembly.fullElapsedEnvelope_hasEnvelopeProfile_of_primitive_jets`.
We use the actual admissible history and its prescribed affine Seeley extension.
The principal frame and the complete zeroth coefficient are extracted with their
Frobenius norms, rather than identifying them with the array's supremum norm.
The ten/nine derivative shifts are paid from one fixed history reserve.
These estimates do not construct the common critical carrier or the inverse.
Sources: `main:prop:current-scale`, `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.RetainedFactors
open GeometricProfile ProtectedFlow CurrentCoefficientProfiles
open FullPhaseCharts.InverseEstimates

/-- Extract the stress frame from the full reduced array, with its actual
matrix norm (`app:ch_waves:eq:reduced-symbol`). This is the continuous version
of the private projection in `ProtectedFlow.ReducedCoefficients`. -/
def reducedFrameProjection (n : ℕ) :
    (ReducedCoefficientIndex n → ℝ) →L[ℝ] (Fin n → MetricTensor n) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun a i j k ↦ a (.inl (j, i, k))
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

/-- Extract the full connection matrix, retaining its sign and every entry
(`app:ch_waves:eq:reduced-symbol`). -/
def reducedZerothProjection (n : ℕ) :
    (ReducedCoefficientIndex n → ℝ) →L[ℝ] MetricTensor n :=
  LinearMap.toContinuousLinearMap {
    toFun := fun a i k ↦ a (.inr (i, k))
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

/-- The projected extended array is the SAME prescribed extended stress
frame, everywhere, including outside the coefficient ball
(`app:ch_regular:eq:coefficient-extension`). -/
theorem reducedFrameProjection_extended_eq {n N : ℕ}
    (p : BallExtension.Parameters (Euclidean n)) (F : Euclidean n → Euclidean N)
    (hF : ∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ 2 F x)
    (hrank : HasFullNormalRankOn F (closedBall p.center p.radius)) :
    reducedFrameProjection n ∘ extendedReducedCoefficients p (fun _ _ ↦ 0) F =
      extendedProjectedStress p F := by
  funext x i j k
  exact extendedReducedCoefficients_principal p (fun _ _ ↦ 0) hF hrank x j i k

/-- On the original coefficient ball the extracted zeroth matrix is exactly
the negative Christoffel contraction of the geometric stress frame. There is
no dropped connection term (`app:ch_waves:eq:reduced-symbol`). -/
theorem reducedZerothProjection_extended_eqOn {n N : ℕ}
    (p : BallExtension.Parameters (Euclidean n)) (F : Euclidean n → Euclidean N) :
    EqOn (reducedZerothProjection n ∘ extendedReducedCoefficients p (fun _ _ ↦ 0) F)
      (fun x ↦ reducedZerothCoefficient F (fun i ↦ (StressFrame.geometricCubeStress F x i).val) x)
      (closedBall p.center p.radius) := by
  intro x hx
  have he := extendedReducedCoefficients_eqOn p (fun _ _ ↦ 0) F hx
  change reducedZerothProjection n (extendedReducedCoefficients p (fun _ _ ↦ 0) F x) = _
  rw [he]
  rfl

private theorem bddAbove_extended_array_jets {n : ℕ}
    {a : Euclidean n → ReducedCoefficientIndex n → ℝ}
    (ha : ContDiff ℝ ∞ a)
    (hc : HasCompactSupport (a - reducedCoefficientBackground (fun _ _ ↦ 0)))
    (m : ℕ) : BddAbove ((fun x ↦ ‖iteratedFDeriv ℝ m a x‖) '' univ) := by
  let a₀ : Euclidean n → ReducedCoefficientIndex n → ℝ :=
    reducedCoefficientBackground (fun _ _ ↦ 0)
  have ha₀ : a₀ = fun _ ↦ a₀ 0 := rfl
  have hs₀ : ContDiff ℝ ∞ a₀ := contDiff_reducedCoefficientBackground contDiff_const
  obtain ⟨M, _, hM⟩ := hc.exists_bound_iteratedFDeriv (ha.sub hs₀) m
  refine ⟨M + ‖a₀ 0‖, ?_⟩
  rintro _ ⟨x, _, rfl⟩
  have he : a = (a - a₀) + a₀ := by abel
  conv_lhs => rw [he]
  dsimp only
  rw [iteratedFDeriv_add_apply (f := a - a₀) (g := a₀) ((ha.sub hs₀).contDiffAt.of_le (by simp))
    (hs₀.contDiffAt.of_le (by simp))]
  apply (norm_add_le _ _).trans (add_le_add (hM m le_rfl x) ?_)
  rw [ha₀]
  cases m with
  | zero => simp
  | succ m => simp [iteratedFDeriv_succ_const]

/-- Produce the two ORIGINAL coefficient profiles for every admissible
history, with the SAME fixed reference and extension. The constants precede
the initial scale, history, compact measurement set and high order. The
principal field is literally `extendedProjectedStress`; the lower-order field
is the full extended reduced array's connection matrix. No coefficient profile
or current geometric gap is assumed (`main:prop:current-scale`). -/
theorem exists_admissible_history_retained_coefficient_profiles {n : ℕ}
    (G : FlatReference n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (p : BallExtension.Parameters (Euclidean n)) (hpcenter : p.center = 0)
    (hpradius : p.radius = r) {rStar reserve kMin : ℕ}
    (hStar : 8 ≤ rStar) (hreserve : 2 + reserve ≤ rStar)
    (horder : displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ AQ AB : ℕ → ℝ,
      (∀ m, 0 ≤ AQ m) ∧ (∀ m, 0 ≤ AB m) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
      let Q := extendedProjectedStress p F
      let B := reducedZerothProjection n ∘ extendedReducedCoefficients p (fun _ _ ↦ 0) F
      ContDiff ℝ ∞ Q ∧ ContDiff ℝ ∞ B ∧
      ∀ KQ : Set (Euclidean n), IsCompact KQ →
        HasDerivativeProfile KQ Q reserve (currentCoefficientScale R₀ j) AQ ∧
        HasDerivativeProfile KQ B reserve (currentCoefficientScale R₀ j) AB := by
  have h8 : displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin := by
    have hs : (8 : ℝ) ≤ rStar := by exact_mod_cast hStar
    have hb : 0 ≤ bandExponent := by norm_num [bandExponent]
    exact lt_of_le_of_lt (by nlinarith) horder
  obtain ⟨Sg, hSg, _, _, _, _, hgeom⟩ :=
    HistoryGeometry.exists_geometric_neighborhood G hr hrR hR h8 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Se, hSe, _, E, _, hE, hext⟩ :=
    exists_admissible_history_extended_reduced_profiles G hr hrR hR p hpcenter hpradius
      hStar hreserve horder
  refine ⟨max Sg Se, hSg.trans (le_max_left _ _),
    (fun m ↦ ‖reducedFrameProjection n‖ * E m),
    (fun m ↦ ‖reducedZerothProjection n‖ * E m),
    (fun m ↦ mul_nonneg (norm_nonneg _) (hE m)),
    (fun m ↦ mul_nonneg (norm_nonneg _) (hE m)), ?_⟩
  intro R₀ hR₀ j u ell hu F Q B
  have hF : ContDiff ℝ ∞ F := hu.contDiff_finiteHistoryMap G.contDiff
  obtain ⟨_, hrank, _⟩ := hgeom R₀ ((le_max_left _ _).trans hR₀) j u ell hu
  obtain ⟨ha, _, hsupp, _, hprofile⟩ :=
    hext R₀ ((le_max_right _ _).trans hR₀) j u ell hu
  let a := extendedReducedCoefficients p (fun _ _ ↦ 0) F
  have hcompact : HasCompactSupport (a - reducedCoefficientBackground (fun _ _ ↦ 0)) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (r + p.width / 2))
      ((subset_tsupport _).trans hsupp)
  have hQ : reducedFrameProjection n ∘ a = Q :=
    reducedFrameProjection_extended_eq p F (fun _ _ ↦ hF.contDiffAt.of_le (by simp))
      (fun x hx ↦ hrank x (closedBall_subset_ball hrR (by simpa [hpcenter, hpradius] using hx)))
  refine ⟨hQ ▸ (reducedFrameProjection n).contDiff.comp ha,
    (reducedZerothProjection n).contDiff.comp ha, ?_⟩
  intro KQ hKQ
  have hlocal (m : ℕ) : cNorm KQ m a ≤ E m * currentCoefficientScale R₀ j ^ (m - reserve) :=
    (cNorm_mono_set_of_bddAbove (subset_univ KQ)
      (fun k _ ↦ bddAbove_extended_array_jets ha hcompact k)).trans (hprofile m)
  constructor <;> intro m
  · rw [← hQ]
    exact (cNorm_postLinear_le_on hKQ m (reducedFrameProjection n)
      (fun _ _ ↦ ha.contDiffAt.of_le (by simp))).trans
        ((mul_le_mul_of_nonneg_left (hlocal m) (norm_nonneg _)).trans_eq (by ring))
  · exact (cNorm_postLinear_le_on hKQ m (reducedZerothProjection n)
      (fun _ _ ↦ ha.contDiffAt.of_le (by simp))).trans
        ((mul_le_mul_of_nonneg_left (hlocal m) (norm_nonneg _)).trans_eq (by ring))

end JanetCartan.ResponseTransfer.RetainedFactors
