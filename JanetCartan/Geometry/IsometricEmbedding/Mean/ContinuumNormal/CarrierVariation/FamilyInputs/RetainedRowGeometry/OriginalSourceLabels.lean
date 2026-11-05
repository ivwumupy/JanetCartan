module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.OriginalLabels
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Comparison
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity.SourceFootpoint

/-!
# Original scalar labels for every contraction of one retained source

The fixed forward C¹ bound controls the divided physical component of the
source footpoint. The carrier component is unchanged. This keeps the original
scalar ball without a source-dependent enlargement of the density class.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier PositiveReference PositiveReference.FlowConstruction
open NormalizedBackground.SourceGeometry WideDensity

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Physical contraction preserves the ENTIRE original output cylinder,
including incidence labels distinct from the ODE cell center. This is a
coordinate identity, not a new choice of masks or comparison domains
(`app:ch_background:eq:bg-Nsigma`, `app:ch_background:eq:bg-Psi`). -/
theorem densityCoordinates_sourceDilation_mem_outputCylinder
    {zCell : Euclidean 3} {Rc τ : ℝ} {p : Euclidean n × CarrierParameter}
    (hp : densityCoordinates T p ∈ outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ)
    {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    densityCoordinates T (σ • p.1, p.2) ∈
      outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ := by
  have heq : densityCoordinates T (σ • p.1, p.2) =
      (σ * (densityCoordinates T p).1,
        (σ • (densityCoordinates T p).2.1, (densityCoordinates T p).2.2)) := by
    simp [densityCoordinates, coordinates_apply, map_smul, smul_eq_mul]
  rw [heq]
  have ht : |(densityCoordinates T p).1| ≤ τ / 2 := abs_le.mpr hp.1
  have ht' : |σ * (densityCoordinates T p).1| ≤ τ / 2 := by
    rw [abs_mul, abs_of_nonneg hσ]
    exact (mul_le_of_le_one_left (abs_nonneg _) hσ1).trans ht
  refine ⟨abs_le.mp ht', ?_⟩
  have hl := hp.2
  simp only [mem_closedBall, Prod.dist_eq, dist_zero_right, max_le_iff] at hl ⊢
  refine ⟨?_, hl.2⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
  exact (mul_le_of_le_one_left (norm_nonneg _) hσ1).trans hl.1

/-- The SAME seed forward C¹ bound controls its divided source ODE footpoint
uniformly for every positive contraction. The time buffer is the explicit
one used by `exists_original_label_region`; the original full-modulation
working ball supplies the label buffer. This proves the positive-source
range needed by `sourceDensityFootpointExtension_zero_mem_original_closedBall`
without assuming an inverse derivative bound or a density extension
(`app:ch_background:eq:bg-Nsigma`, `app:ch_background:prop:bg-normalized`). -/
theorem sourceDensityFootpoint_mem_original_ball_of_forward_cNorm
    {zCell : Euclidean 3} {L Rc B τ Mc : ℝ}
    (hL : 0 < L) (hRc : 0 < Rc) (hτ : 0 < τ) (hMc : 0 < Mc)
    {Ω K : Set (Euclidean n × Euclidean 3)} {F : Euclidean n → Euclidean N}
    {row col : Fin n}
    (c : Chart T Ω K ((0 : Euclidean (n - 1)), zCell) Rc B τ row col F)
    (hforward : cNorm (Icc (-τ) τ ×ˢ closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8))
      1 c.forward ≤ Mc)
    {p : Euclidean n × CarrierParameter}
    (houtput : densityCoordinates T p ∈ outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ)
    (hlabel : (densityCoordinates T p).2 ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64))
    (htime : |(densityCoordinates T p).1| < L / (64 * Mc))
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    densityFootpoint T (sourceTransportFlow c.inverse σ) p ∈
      ball ((0 : Euclidean (n - 1)), zCell) (L / 16) := by
  have hsD : densityCoordinates T (σ • p.1, p.2) ∈ c.D :=
    c.small_subset ((outputCylinder_spec hRc hτ).2
      (densityCoordinates_sourceDilation_mem_outputCylinder T houtput hσ.le hσ1))
  have hd := ContinuumAdjoint.Canonical.RetainedLeading.inverseFootpoint_dist_le_of_forward_cNorm
    zCell hRc hτ c.forward c.inverse c.D c.inverse_range c.initial c.forward_inverse
    c.forward_buffer_smooth hforward hsD
  have htimeσ : (densityCoordinates T (σ • p.1, p.2)).1 =
      σ * (densityCoordinates T p).1 := by
    simp [densityCoordinates, coordinates_apply, map_smul, smul_eq_mul]
  have hlabelσ : (densityCoordinates T (σ • p.1, p.2)).2.1 =
      σ • (densityCoordinates T p).2.1 := by
    simp [densityCoordinates, coordinates_apply, map_smul]
  have hparamσ : (densityFootpoint T c.inverse (σ • p.1, p.2)).2 = parameter p.2 :=
    c.inverse_parameter _ hsD
  have hsp : dist (densityFootpoint T c.inverse (σ • p.1, p.2)).1
      (σ • (densityCoordinates T p).2.1) ≤ Mc * (σ * |(densityCoordinates T p).1|) := by
    have hfst := (le_max_left
      (dist (c.inverse (densityCoordinates T (σ • p.1, p.2))).1
        (densityCoordinates T (σ • p.1, p.2)).2.1)
      (dist (c.inverse (densityCoordinates T (σ • p.1, p.2))).2
        (densityCoordinates T (σ • p.1, p.2)).2.2)).trans
          (by simpa only [Prod.dist_eq] using hd)
    simpa only [densityFootpoint, htimeσ, hlabelσ, abs_mul, abs_of_pos hσ] using hfst
  have hscaled : dist (σ⁻¹ • (densityFootpoint T c.inverse (σ • p.1, p.2)).1)
      (densityCoordinates T p).2.1 ≤ Mc * |(densityCoordinates T p).1| := by
    have hh := mul_le_mul_of_nonneg_left hsp (inv_nonneg.mpr hσ.le)
    have heq : σ⁻¹ * dist (densityFootpoint T c.inverse (σ • p.1, p.2)).1
        (σ • (densityCoordinates T p).2.1) =
        dist (σ⁻¹ • (densityFootpoint T c.inverse (σ • p.1, p.2)).1)
          (densityCoordinates T p).2.1 := by
      have hs := dist_smul₀ σ⁻¹ (densityFootpoint T c.inverse (σ • p.1, p.2)).1
        (σ • (densityCoordinates T p).2.1)
      simpa only [Real.norm_eq_abs, abs_inv, abs_of_pos hσ,
        inv_smul_smul₀ (ne_of_gt hσ)] using hs.symm
    rw [heq] at hh
    convert hh using 1
    field_simp
  have hstep : Mc * |(densityCoordinates T p).1| < L / 64 := by
    have hm := mul_lt_mul_of_pos_left htime hMc
    have heq : Mc * (L / (64 * Mc)) = L / 64 := by field_simp
    rwa [heq] at hm
  have hl := hlabel
  simp only [mem_closedBall, Prod.dist_eq, dist_zero_right, max_le_iff] at hl
  rw [densityFootpoint_sourceTransportFlow, hparamσ]
  simp only [mem_ball, Prod.dist_eq, dist_zero_right, max_lt_iff]
  constructor
  · have htri := norm_le_norm_add_norm_sub'
      (σ⁻¹ • (densityFootpoint T c.inverse (σ • p.1, p.2)).1)
      (densityCoordinates T p).2.1
    rw [← dist_eq_norm] at htri
    linarith [hl.1]
  · exact hl.2.trans_lt (by linarith)

/-- Choose the original scalar time restriction BEFORE incidence masks,
retaining every zero-position carrier point and the full comparison output
cylinder. In addition to the existing current-chart conclusions, the same
seed forward bound now controls every positive source contraction on the
whole chosen cell. The input cylinder is produced by
`exists_original_outputCylinder_region`; all other inputs come from the
original retained working balls and flow estimates. Consumer: the original
source density comparison and the single finite retained cover
(`app:ch_background:prop:bg-normalized`, `app:ch_background:defn:bg-row`). -/
theorem exists_original_source_label_region
    (zCell : Euclidean 3) {L Rc B τ Mc : ℝ}
    (hL : 0 < L) (hRc : 0 < Rc) (hτ : 0 < τ) (hMc : 0 < Mc)
    (hτRc : τ ≤ Rc / 16)
    {Ω K : Set (Euclidean n × Euclidean 3)}
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc) K)
    {E : Set (Euclidean n × CarrierParameter)} (hE : IsOpen E)
    (hlabel : ∀ p ∈ E,
      (densityCoordinates T p).2 ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64))
    (houtput : MapsTo (densityCoordinates T) E
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ)) :
    ∃ E' : Set (Euclidean n × CarrierParameter), IsOpen E' ∧ E' ⊆ E ∧
      (∀ z : CarrierParameter, ((0 : Euclidean n), z) ∈ E' ↔
        ((0 : Euclidean n), z) ∈ E) ∧
      MapsTo (densityCoordinates T) E'
        (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ) ∧
      ∀ (F : Euclidean n → Euclidean N) (row col : Fin n)
        (c : Chart T Ω K ((0 : Euclidean (n - 1)), zCell) Rc B τ row col F),
        cNorm (Icc (-τ) τ ×ˢ closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8))
          1 c.forward ≤ Mc →
        MapsTo (densityCoordinates T) E' c.D ∧
        MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) E' K ∧
        ContDiffOn ℝ ∞ (densityFootpoint T c.inverse) E' ∧
        MapsTo (densityFootpoint T c.inverse) E'
          (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)) ∧
        ∀ σ ∈ Ioc (0 : ℝ) 1,
          MapsTo (densityFootpoint T (sourceTransportFlow c.inverse σ)) E'
            (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)) := by
  let e := L / (64 * Mc)
  have he : 0 < e := div_pos hL (by positivity)
  let Eb := E ∩ (fun p ↦ (densityCoordinates T p).1) ⁻¹' Ioo (-e) e
  have hEb : IsOpen Eb := hE.inter
    (isOpen_Ioo.preimage (densityCoordinates T).continuous.fst)
  have hzero (z : CarrierParameter) : ((0 : Euclidean n), z) ∈ Eb ↔
      ((0 : Euclidean n), z) ∈ E := by
    constructor
    · exact fun h ↦ h.1
    · intro hz
      refine ⟨hz, ?_⟩
      change (adaptedCoordinates T.data.adapted (0 : Euclidean n)).1 ∈ Ioo (-e) e
      simpa only [map_zero, Prod.fst_zero, mem_Ioo, neg_lt_zero] using And.intro he he
  obtain ⟨E', hE', hsub, hzeros, hcharts⟩ := exists_original_label_region (N := N) T zCell
    hL hRc hτ hMc hτRc hbuffer hEb (fun p hp ↦ hlabel p hp.1)
  have hsubE : E' ⊆ E := hsub.trans inter_subset_left
  refine ⟨E', hE', hsubE, fun z ↦ (hzeros z).trans (hzero z),
    houtput.mono_left hsubE, ?_⟩
  intro F row col c hforward
  have hD : MapsTo (densityCoordinates T) Eb c.D :=
    fun p hp ↦ c.small_subset ((outputCylinder_spec hRc hτ).2 (houtput hp.1))
  obtain ⟨hflow, hcoeff, hsmooth, hrange⟩ := hcharts F row col c hD hforward
  refine ⟨hflow, hcoeff, hsmooth, hrange, ?_⟩
  intro σ hσ p hp
  exact sourceDensityFootpoint_mem_original_ball_of_forward_cNorm T hL hRc hτ hMc c hforward
    (houtput (hsubE hp)) (hlabel p (hsubE hp)) (abs_lt.mpr (hsub hp).2) hσ.1 hσ.2

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
