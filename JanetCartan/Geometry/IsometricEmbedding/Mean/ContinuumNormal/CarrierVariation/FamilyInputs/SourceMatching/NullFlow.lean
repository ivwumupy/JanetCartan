module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.AdaptedCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.Adapted

/-!
# Uniqueness for the retained adapted null flow

The two independently constructed flows are compared after contracting the
current trajectory into the seed range. The inputs are the ODE, initial value,
range and regularity statements retained by
`NullTransport.exists_projected_local_positive_amplitude`. They contain no
flow-matching assertion. The common buffers still have to be instantiated for
the genuine seed and all source dilations by the parent construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius NNReal

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching
open HamiltonPhase NormalizedBackground.SourceGeometry
open ActualCarriers CurrentFullPhase NullTransport NullTransport.ActualFlow
open NullTransport.FlowAmplitude

private theorem labelDilation_mem_ball {X Z : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [PseudoMetricSpace Z]
    {σ r : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) {z : Z} {p : X × Z}
    (hp : p ∈ ball (0, z) r) : transportLabelDilation σ p ∈ ball (0, z) r := by
  simp only [transportLabelDilation, mem_ball, Prod.dist_eq, max_lt_iff,
    dist_zero_right] at hp ⊢
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
  exact ⟨(mul_le_of_le_one_left (norm_nonneg p.1) hσ1).trans_lt hp.1, hp.2⟩

private theorem mul_mem_timeInterval {σ τ t : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : t ∈ Ioo (-τ) τ) : σ * t ∈ Ioo (-τ) τ := by
  apply abs_lt.mp
  rw [abs_mul, abs_of_nonneg hσ]
  exact (mul_le_of_le_one_left (abs_nonneg t) hσ1).trans_lt (abs_lt.mpr ht)

variable {n N : ℕ} {P : FrozenMenu.Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))

include hF hrank hphysical hseed htrans hσ hσ1 hscaled

local notation "Label" => Euclidean (n - 1) × Euclidean 3
local notation "C" => coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)

/-- Identify independently selected adapted null flows by their actual ODEs.
The fixed radii, seed regularity and flow-tube bounds are the precise outputs
of `exists_projected_local_positive_amplitude` used here. Contraction proves
the common initial-label and state ranges, including negative times.
The inverse ODE footpoint is then matched using its own inverse identity;
it is distinct from the Hamilton transport. Consumer: scalar amplitude matching.
Source: `app:ch_background:eq:bg-Nsigma`, `new:lem:scaling`. -/
theorem current_nullFlow_source_dilation (row col : Fin n)
    {z₀ : Euclidean 3} {ρ R τ : ℝ} (_hR : 0 < R) (hτ : 0 < τ) (hτR : τ ≤ R / 16)
    (hbuffer : MapsTo (C).symm (closedBall (0, (0, z₀)) R) (closedBall (0, z₀) ρ))
    (hreg : ∀ w ∈ closedBall (0, z₀) ρ,
      ContDiffAt ℝ ∞ (carrierTransportDirection T Q₀ row col) w)
    {Φ₀ Φσ : ℝ × Label → Label}
    (hinit₀ : ∀ p ∈ ball (0, z₀) (R / 8), Φ₀ (0, p) = p)
    (hinitσ : ∀ p ∈ ball (0, z₀) (R / 8), Φσ (0, p) = p)
    (hrange₀ : ∀ p ∈ ball (0, z₀) (R / 8), ∀ t ∈ Ioo (-τ) τ,
      Φ₀ (t, p) ∈ ball (0, z₀) (R / 4))
    (hrangeσ : ∀ p ∈ ball (0, z₀) (R / 8), ∀ t ∈ Ioo (-τ) τ,
      Φσ (t, p) ∈ ball (0, z₀) (R / 4))
    (hpatchσ : ∀ p ∈ ball (0, z₀) (R / 8), ∀ t ∈ Ioo (-τ) τ,
      (C).symm (t, Φσ (t, p)) ∈ ball 0 T.physicalRadius ×ˢ
        FrozenMenu.parameterCube (2 * P.radius))
    (hvelocity₀ : ∀ p ∈ ball (0, z₀) (R / 8), ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun s ↦ Φ₀ (s, p))
        ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Q₀ row col
          ((C).symm (t, Φ₀ (t, p))))).2, 0) t)
    (hvelocityσ : ∀ p ∈ ball (0, z₀) (R / 8), ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun s ↦ Φσ (s, p))
        ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Qσ row col
          ((C).symm (t, Φσ (t, p))))).2, 0) t) :
    EqOn Φσ (sourceTransportFlow Φ₀ σ) (Ioo (-τ) τ ×ˢ ball (0, z₀) (R / 8)) ∧
    ∀ (Y₀ Yσ : ℝ × Label → Label) (Dσ : Set (ℝ × Label)),
      MapsTo (fun q ↦ (q.1, Yσ q)) Dσ (Ioo (-τ) τ ×ˢ ball (0, z₀) (R / 8)) →
      (∀ p ∈ ball (0, z₀) (R / 8), ∀ t ∈ Ioo (-τ) τ, Y₀ (t, Φ₀ (t, p)) = p) →
      (∀ q ∈ Dσ, Φσ (q.1, Yσ q) = q.2) →
      EqOn Yσ (sourceTransportFlow Y₀ σ) Dσ := by
  have hflow : EqOn Φσ (sourceTransportFlow Φ₀ σ)
      (Ioo (-τ) τ ×ˢ ball (0, z₀) (R / 8)) := by
    intro q hq
    have hp := labelDilation_mem_ball hσ.le hσ1 hq.2
    have htime (t : ℝ) (ht : t ∈ Ioo (-τ) τ) := mul_mem_timeInterval hσ.le hσ1 ht
    let u : ℝ → ℝ × Label := fun t ↦ transportCoordinateDilation σ (t, Φσ (t, q.2))
    let v : ℝ → ℝ × Label := fun t ↦ (σ * t, Φ₀ (σ * t, transportLabelDilation σ q.2))
    let V : ℝ × Label → ℝ × Label := fun p ↦ σ • liftedDirection T Q₀ row col p
    let K := closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z₀)) R
    have hVat (p) (hpK : p ∈ K) : ContDiffAt ℝ 2 V p := by
      have hd := (hreg _ (hbuffer hpK)).comp p (C).symm.contDiff.contDiffAt
      have he := (adaptedCoordinates T.data.adapted).contDiff.contDiffAt.comp p hd
      exact ((contDiffAt_const.prodMk (he.snd.prodMk contDiffAt_const)).const_smul σ).of_le
        (by simp)
    let M : ℝ≥0 := ⟨cNorm K 2 V, cNorm_nonneg _ _ _⟩
    have hlip : LipschitzOnWith M V K := by
      apply (convex_closedBall _ _).lipschitzOnWith_of_nnnorm_fderiv_le
        (fun p hpK ↦ (hVat p hpK).differentiableAt (by norm_num))
      intro p hpK
      exact_mod_cast (ODE.norm_and_fderiv_le_cNorm_two (isCompact_closedBall _ _) hVat hpK).2
    have hrange (t : ℝ) (ht : t ∈ Ioo (-τ) τ) {p : Label}
        (hpR : p ∈ ball (0, z₀) (R / 4)) : (σ * t, p) ∈ K := by
      rw [mem_closedBall, Prod.dist_eq, max_le_iff]
      constructor
      · have hs := abs_lt.mpr (htime t ht)
        simpa only [Real.dist_eq, sub_zero] using hs.le.trans (hτR.trans (by linarith [_hR]))
      · exact (mem_ball.mp hpR).le.trans (by linarith)
    have huK (t) (ht : t ∈ Ioo (-τ) τ) : u t ∈ K :=
      hrange t ht (labelDilation_mem_ball hσ.le hσ1 (hrangeσ q.2 hq.2 t ht))
    have hvK (t) (ht : t ∈ Ioo (-τ) τ) : v t ∈ K :=
      hrange t ht (hrange₀ _ hp _ (htime t ht))
    have hdu (t) (ht : t ∈ Ioo (-τ) τ) : HasDerivAt u (V (u t)) t := by
      have hpatch := hpatchσ q.2 hq.2 t ht
      have hdir := current_carrierTransportDirection_source_dilation T Q₀ Qσ hF hrank
        hphysical hseed htrans hσ hσ1 hscaled row col hpatch.1 hpatch.2
      rw [← coordinates_symm_source_dilation] at hdir
      have hd := hvelocityσ q.2 hq.2 t ht
      rw [hdir] at hd
      have hdf := (ContinuousLinearMap.fst ℝ (Euclidean (n - 1)) (Euclidean 3)).hasFDerivAt.comp_hasDerivAt t hd
      have hds := (ContinuousLinearMap.snd ℝ (Euclidean (n - 1)) (Euclidean 3)).hasFDerivAt.comp_hasDerivAt t hd
      have hh := ((hasDerivAt_id t).const_mul σ).prodMk
        ((hdf.const_smul σ).prodMk hds)
      simpa [u, V, transportCoordinateDilation, transportLabelDilation, liftedDirection] using hh
    have hdv (t) (ht : t ∈ Ioo (-τ) τ) : HasDerivAt v (V (v t)) t := by
      have hd := (hvelocity₀ _ hp _ (htime t ht)).scomp t ((hasDerivAt_id t).const_mul σ)
      simpa only [v, V, liftedDirection, Prod.smul_mk, smul_eq_mul, mul_one, smul_zero,
        Function.comp_def, id_eq] using
        ((hasDerivAt_id t).const_mul σ).prodMk hd
    have hzero : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
    have hi : u 0 = v 0 := by
      simp only [u, v, transportCoordinateDilation, mul_zero, hinitσ _ hq.2, hinit₀ _ hp]
    have he := ODE_solution_unique_of_mem_Ioo (v := fun _ ↦ V) (s := fun _ ↦ K)
      (fun _ _ ↦ hlip) hzero (fun t ht ↦ ⟨hdu t ht, huK t ht⟩)
      (fun t ht ↦ ⟨hdv t ht, hvK t ht⟩) hi hq.1
    have helabel := congrArg (fun p : ℝ × Label ↦ transportLabelDilation σ⁻¹ p.2) he
    simpa [u, v, sourceTransportFlow, transportCoordinateDilation,
      transportLabelDilation, smul_smul, hσ.ne'] using helabel

  refine ⟨hflow, ?_⟩
  intro Y₀ Yσ Dσ hYU hYΦ hΦY q hq
  have hp := hYU hq
  have he := congrArg (transportLabelDilation σ) (hflow hp)
  rw [hΦY q hq] at he
  simp only [sourceTransportFlow, transportLabelDilation_inv hσ.ne'] at he
  change transportLabelDilation σ q.2 = Φ₀ (σ * q.1, transportLabelDilation σ (Yσ q)) at he
  have hy := hYΦ _ (labelDilation_mem_ball hσ.le hσ1 hp.2)
    _ (mul_mem_timeInterval hσ.le hσ1 hp.1)
  dsimp only at hy
  rw [← he] at hy
  change Y₀ (transportCoordinateDilation σ q) = transportLabelDilation σ (Yσ q) at hy
  simp only [sourceTransportFlow, hy]
  simp [transportLabelDilation, smul_smul, hσ.ne']

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching
