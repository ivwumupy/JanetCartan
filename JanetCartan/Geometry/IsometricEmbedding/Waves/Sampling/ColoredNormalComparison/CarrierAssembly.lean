module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.ReassembledDisintegration
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSlices.Coordinates

/-!
# The literal carrier mean and all grouped prefixes

Fubini in the original carrier coordinates connects the smooth-band kernel
identities to `patchMeanNormal`, with its fixed ceiling, labels and weights.
The support input is only the support of the original patch weight. The
actual finite-family comparison consumes the resulting identity, for
`app:ch_waves:eq:colored-normal-comparison`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory Set
open scoped ENNReal
namespace JanetCartan.Sampling.ColoredNormalComparison
open NormalComparison SamplingKernelBounds RawInputPartition ContinuumRow
open SeparatedSampling LatticeQuadrature BackgroundQuadrature Realization

variable {n J p : ℕ}

/-- The actual colored slice mean, after grouping both sharp components of
each original band and keeping the original carrier coordinates
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def coloredWideSliceNormal
    (D : BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (ψ : Point → ℝ) (κ : ℝ → ℝ) (B h : ℝ) (I : Set ℝ) (L : ℕ) (v : Euclidean 2) :
    SamplingKernelBounds.Output n →L[ℂ] SamplingKernelBounds.Output n :=
  ∑ c, ∫ s in I,
    coloredBlockMask p (integerCube (blockCutoff p B h)) (convolvedBoxWindow κ p)
      h c (carrierSamplingEquiv (s, v)) •
      (ψ (carrierSamplingEquiv (s, v)) •
        ∑ j ∈ Finset.univ.filter (fun j : Fin J ↦ j.val < L),
          atomNormal (wideKernelOperator D j.val (j, (c, carrierSamplingEquiv (s, v)))))

private theorem integral_carrier_restrict
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : Point → E) (hi : Integrable H) (I : Set ℝ) (V : Set (Euclidean 2))
    (hsupport : ∀ s v, s ∉ I ∨ v ∉ V → H (carrierSamplingEquiv (s, v)) = 0) :
    Integrable (fun v ↦ ∫ s in I, H (carrierSamplingEquiv (s, v))) (volume.restrict V) ∧
      (∫ z, H z) = ∫ v in V, ∫ s in I, H (carrierSamplingEquiv (s, v)) := by
  have hs (v : Euclidean 2) : (∫ s in I, H (carrierSamplingEquiv (s, v))) =
      ∫ s : ℝ, H (carrierSamplingEquiv (s, v)) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun s h ↦ hsupport s v (Or.inl h))
  have hv : (∫ v in V, ∫ s : ℝ, H (carrierSamplingEquiv (s, v))) =
      ∫ v : Euclidean 2, ∫ s : ℝ, H (carrierSamplingEquiv (s, v)) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall (fun s ↦ hsupport s v (Or.inr hv))
  have hiv : Integrable (fun v ↦ ∫ s in I, H (carrierSamplingEquiv (s, v)))
      (volume.restrict V) := by
    simp_rw [hs]
    exact ((carrierSamplingEquiv_measurePreserving.integrable_comp_of_integrable hi).integral_prod_right).restrict
  refine ⟨hiv, ?_⟩
  simp_rw [hs, hv]
  rewrite [← integral_carrierSamplingEquiv]
  exact integral_prod_symm _
    (carrierSamplingEquiv_measurePreserving.integrable_comp_of_integrable hi)

/-- The complete literal mean is the compact spectator integral of the same
wide-band slice normals. Integrability is proved from the actual kernel
continuity and compact colored windows, rather than assumed
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem patchMeanNormal_refined_eq_spectator
    (D : BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    {ψ : Point → ℝ} {κ : ℝ → ℝ} {W B h : ℝ}
    (hw : WindowBounds p (convolvedBoxWindow κ p) W)
    (hψ : Continuous ψ) (hwc : Continuous (convolvedBoxWindow κ p)) (hh : h ≠ 0)
    (I : Set ℝ) (V : Set (Euclidean 2))
    (hsupport : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 → s ∈ I ∧ v ∈ V)
    (L : ℕ) :
    Integrable (coloredWideSliceNormal D ψ κ B h I L) (volume.restrict V) ∧
    patchMeanNormal p B ψ (convolvedBoxWindow κ p) h
      (fun c z ↦ refinedKernelPrefix D L (c, z)) =
      ∫ v in V, coloredWideSliceNormal D ψ κ B h I L v := by
  let H := fun c (z : Point) ↦
    coloredBlockMask p (integerCube (blockCutoff p B h)) (convolvedBoxWindow κ p) h c z •
      (ψ z • ∑ j ∈ Finset.univ.filter (fun j : Fin J ↦ j.val < L),
        atomNormal (wideKernelOperator D j.val (j, (c, z))))
  have hi (c : Fin 3 → Fin (p + 1)) : Integrable (H c) :=
    integrable_colored_wideKernelPrefix_normal D hw hψ hwc hh L c
  have hsplit (c : Fin 3 → Fin (p + 1)) := integral_carrier_restrict (H c) (hi c) I V
    (fun s v hv ↦ by
      have hz : ψ (carrierSamplingEquiv (s, v)) = 0 := by
        by_contra hne
        rcases hv with hv | hv
        · exact hv (hsupport s v hne).1
        · exact hv (hsupport s v hne).2
      simp only [H, hz, zero_smul, smul_zero])
  constructor
  · exact integrable_finsetSum (μ := volume.restrict V)
      (f := fun c v ↦ ∫ s in I, H c (carrierSamplingEquiv (s, v)))
      Finset.univ (fun c _ ↦ (hsplit c).1)
  · rewrite [patchMeanNormal_refinedKernelPrefix_eq_wide D hw hψ hwc hh L]
    change (∑ c, ∫ z, H c z) = ∫ v in V, ∑ c, ∫ s in I, H c (carrierSamplingEquiv (s, v))
    rewrite [integral_finsetSum (μ := volume.restrict V)
      (f := fun c v ↦ ∫ s in I, H c (carrierSamplingEquiv (s, v)))
      Finset.univ (fun c _ ↦ (hsplit c).1)]
    exact Finset.sum_congr rfl (fun c _ ↦ (hsplit c).2)

private theorem sum_fin_prefix_eq_sum_range {H : Type*} [AddCommMonoid H]
    (f : ℕ → H) {L : ℕ} (hL : L ≤ J) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin J ↦ j.val < L), f j.val) =
      ∑ j ∈ Finset.range L, f j := by
  classical
  apply Finset.sum_bij (fun j _ ↦ j.val)
  · intro j hj
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
  · intro j _ k _ h
    exact Fin.ext h
  · intro j hj
    exact ⟨⟨j, (Finset.mem_range.mp hj).trans_le hL⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hj⟩, rfl⟩
  · intro _ _
    rfl

/-- Reassemble every prefix of one fixed ceiling into the actual colored
slice integral. The only matching inputs are the normalized forward kernels,
the unchanged smooth-band support and the measure-preserving input charts.
This consumes `samplingNormal_eq_integral_wideKernel` before summation
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem coloredPrefixNormal_eq_wideSlices
    {G : UniformNormalGeometry n n} {C : ℕ → ℝ}
    (F : (Fin 3 → Fin (p + 1)) → ℕ → UniformNormalData G C)
    (D : BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (R : (Fin 3 → Fin (p + 1)) → ℝ) (lam : ℝ)
    (hε : ∀ c (j : Fin J), (R c * lam)⁻¹ * dyadicScale j.val ∈ Icc 0 G.ε₀)
    (I : Set ℝ) {Θ : Set (Euclidean (n - 1))} (hΘ : IsCompact Θ)
    (hinput : ∀ (j : Fin J) c z θ, θ ∉ Θ → ∀ x,
      D.kernel (j, (c, z)) ((2 : ℝ) ^ j.val • θ) x = 0)
    (hsupport : ∀ (j : Fin J) c z η, η ∉ wideBand n j.val → ∀ x,
      D.kernel (j, (c, z)) η x = 0)
    (e : (Fin 3 → Fin (p + 1)) → Fin J → Euclidean n ≃ᵐ ℝ × Euclidean (n - 1))
    (he : ∀ c j, MeasurePreserving (e c j) (volume.restrict G.D)
      ((volume.restrict I).prod (volume.restrict Θ)))
    (ψ : Point → ℝ) (hψ : ∀ z, 0 ≤ ψ z)
    (v : Euclidean 2) (z₀ : Point) (Z : Euclidean n →L[ℝ] Point)
    (hz : ∀ c j u, u ∈ G.D → z₀ + Z u = carrierSamplingEquiv ((e c j u).1, v))
    (hkernel : ∀ c (j : Fin J),
      ∀ᵐ u ∂(volume.restrict I).prod (volume.restrict Θ), ∀ i : Fin n,
      (fun x ↦ normalizedOscillatoryKernel (normalOperatorScale n (dyadicScale j.val))
        (dyadicScale j.val) ((F c j.val).phase ((R c * lam)⁻¹ * dyadicScale j.val))
        (fun x w ↦ (F c j.val).amplitude ((R c * lam)⁻¹ * dyadicScale j.val) x w i)
        x ((e c j).symm u)) =ᵐ[volume]
      fun x ↦ (Real.sqrt (ψ (carrierSamplingEquiv (u.1, v))) : ℂ) *
        ((Real.sqrt (((2 : ℝ) ^ j.val) ^ (n - 1)) : ℂ) *
          D.kernel (j, (c, carrierSamplingEquiv (u.1, v))) ((2 : ℝ) ^ j.val • u.2) x i))
    (κ : ℝ → ℝ) (B h : ℝ)
    (g : (Fin 3 → Fin (p + 1)) → Lp ℂ ∞ (volume.restrict G.D))
    (hg : ∀ c, g c =ᵐ[volume.restrict G.D] fun u ↦
      (coloredBlockMask p (integerCube (blockCutoff p B h)) (convolvedBoxWindow κ p)
        h c (z₀ + Z u) : ℂ))
    {L : ℕ} (hL : L ≤ J) :
    samplingOutputConjugation n (coloredPrefixNormal F R g lam L) =
      coloredWideSliceNormal D ψ κ B h I L v := by
  classical
  let H := fun c (j : Fin J) (s : ℝ) ↦
    (coloredBlockMask p (integerCube (blockCutoff p B h)) (convolvedBoxWindow κ p)
      h c (carrierSamplingEquiv (s, v)) * ψ (carrierSamplingEquiv (s, v))) •
        atomNormal (wideKernelOperator D j.val (j, (c, carrierSamplingEquiv (s, v))))
  have hsingle (c : Fin 3 → Fin (p + 1)) (j : Fin J) :
      Integrable (H c j) (volume.restrict I) ∧
      samplingOutputConjugation n ((F c j.val).uniformOscillatoryNormalOperator
        (dyadicScale j.val) (g c) ((R c * lam)⁻¹ * dyadicScale j.val)) =
        ∫ s in I, H c j s :=
    samplingNormal_eq_integral_wideKernel (F c j.val) (dyadicScale j.val) (hε c j)
      D j.val (fun s ↦ (j, (c, carrierSamplingEquiv (s, v)))) I hΘ
      (fun s ↦ hinput j c (carrierSamplingEquiv (s, v)))
      (fun s ↦ hsupport j c (carrierSamplingEquiv (s, v))) (e c j) (he c j)
      ψ hψ (fun s ↦ carrierSamplingEquiv (s, v)) z₀ Z (hz c j) (hkernel c j)
      κ p B h c (g c) (hg c)
  unfold coloredPrefixNormal coloredWideSliceNormal
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [← sum_fin_prefix_eq_sum_range _ hL, map_sum]
  simp_rw [(hsingle c _).2]
  rw [← integral_finsetSum _ (fun j _ ↦ (hsingle c j).1)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  simp only [Finset.smul_sum, smul_smul, H]

end JanetCartan.Sampling.ColoredNormalComparison
