module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SmoothParameters.SupportedResponse
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.WeakDerivatives.IntegralJets
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.CartesianJets.Transfer

/-!
# The original finite-band source in the Sobolev jet completion

For `app:ch_lag:eq:lag-recurrence`, the source must be formed before applying
one fixed response. The scalar components below keep the original Fourier
measure, half weights and smooth band grouping. Compact frequency support gives
integrability of every source jet, and compact physical support identifies its
actual Lebesgue Sobolev realization with the Bochner integral of the same atoms.
The consumer is the fixed-response integral interchange in this directory.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.CanonicalAtomRealization
open RawPrimary RawInputPartition RetardedSobolev.Spaces
open ResponseTransfer.ParameterRealization

/-- Physical derivatives of the unchanged raw Fourier integral, for the source
jets in `app:ch_lag:eq:lag-recurrence`. -/
private theorem iteratedFDeriv_wideIntegral {n J : ℕ} {E G : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    {V : Set (Euclidean (n - 1))} (hV : IsOpen V)
    (hceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {A : E × Euclidean (n - 1) → G}
    (hA : ContDiffOn ℝ ∞ A (univ ×ˢ V))
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (v : WideInput n J) (k : ℕ) (x : E) :
    iteratedFDeriv ℝ k (wideSuperposition A d v) x =
      ∫ η, weightedWideDensity d v η • iteratedFDeriv ℝ k (fun y ↦ A (y, η)) x := by
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Euclidean (n - 1))
      ((2 : ℝ) ^ J))) := isFiniteMeasure_restrict.mpr
    (isCompact_closedBall _ _).measure_lt_top.ne
  have he := iteratedFDeriv_weightedCompactIntegral isOpen_univ hV
    (isCompact_closedBall _ _) hceil (integrable_wideDensity hd hM hb v).integrableOn
    hA k (mem_univ x)
  change iteratedFDeriv ℝ k (fun y ↦ wideSuperposition A d v y) x =
    wideSuperposition (fun z ↦ iteratedFDeriv ℝ k (fun y ↦ A (y, z.2)) z.1) d v x
  simpa only [wideSuperposition_eq_compact] using he

variable {n J d₀ : ℕ} {V : Set (Euclidean (n - 1))}
    (hV : IsOpen V) (hceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {S : Set (ℝ × (Fin d₀ → ℝ))} (hS : IsCompact S)
    (f : Euclidean (n - 1) → supportedTests S)
    (hf : ContDiffOn ℝ ∞
      (fun z : (ℝ × (Fin d₀ → ℝ)) × Euclidean (n - 1) ↦ (f z.2).val.val z.1)
      (univ ×ˢ V))
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)

/-- The supported scalar source obtained by the original finite-band Fourier
integral (`app:ch_lag:eq:lag-recurrence`). Its support and smoothness are proved
from the atomic sources and the original density. -/
def wideSourceTest (v : WideInput n J) : supportedTests S := by
  let g := wideSuperposition (fun z ↦ (f z.2).val.val z.1) d v
  have hg : ContDiff ℝ ∞ g := contDiffOn_univ.mp
    (contDiffOn_wideSuperposition isOpen_univ hV hceil hf hd hM hb v)
  have hs : tsupport g ⊆ S := by
    apply closure_minimal _ hS.isClosed
    intro x hx
    by_contra hn
    apply hx
    apply integral_eq_zero_of_ae
    filter_upwards [] with η
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hn ((f η).property h)), smul_zero]
    rfl
  exact ⟨⟨g, hg, hS.of_isClosed_subset (isClosed_tsupport _) hs⟩, hs⟩

/-- The scalar source realization keeps the literal original Fourier integral
(`app:ch_lag:eq:lag-W0-definition`). -/
@[simp] theorem wideSourceTest_apply (v : WideInput n J) (x : ℝ × (Fin d₀ → ℝ)) :
    (wideSourceTest hV hceil hS f hf hd hM hb v).val.val x =
      ∫ η, weightedWideDensity d v η • (f η).val.val x := rfl

/-- Every actual Cartesian source jet passes through the unchanged raw
integral (`app:ch_lag:eq:lag-recurrence`). This is the source identity needed
by the same-response Hilbert extension, including the original coordinate swap. -/
theorem jet_wideSourceTest (v : WideInput n J) {s : ℕ} (i : JetIndex d₀ s)
    (x : (Fin d₀ → ℝ) × ℝ) :
    jet i (wideSourceTest hV hceil hS f hf hd hM hb v).val.val x =
      ∫ η, weightedWideDensity d v η • jet i (f η).val.val x := by
  let A := fun z : (ℝ × (Fin d₀ → ℝ)) × Euclidean (n - 1) ↦ (f z.2).val.val z.1
  let w : Fin i.1.val → ℝ × (Fin d₀ → ℝ) := fun a ↦ (0, Pi.single (i.2.1 a) 1)
  let At := fun z : (ℝ × (Fin d₀ → ℝ)) × Euclidean (n - 1) ↦
    iteratedFDeriv ℝ i.1.val (fun y ↦ A (y, z.2)) z.1 w
  have hAt : ContDiffOn ℝ ∞ At (univ ×ˢ V) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i.1.val ↦ ℝ × (Fin d₀ → ℝ)) ℂ w).contDiff.comp_contDiffOn
      (contDiffOn_atomPhysicalJet isOpen_univ hV hf i.1.val)
  have htrans : (fun y ↦ iteratedFDeriv ℝ i.1.val
      (wideSuperposition A d v) y w) = wideSuperposition At d v := by
    funext y
    rw [iteratedFDeriv_wideIntegral hV hceil hf hd hM hb]
    exact ContinuousMultilinearMap.integral_apply
      (integrable_wideSuperposition hceil
        (contDiffOn_atomPhysicalJet isOpen_univ hV hf i.1.val).continuousOn
        hd hM hb v (mem_univ y)) w
  rw [FiniteChain.Graph.CartesianJets.jet_eq_mixed_evaluated_iteratedFDeriv
    (wideSourceTest hV hceil hS f hf hd hM hb v).val.property.1]
  change iteratedFDeriv ℝ i.2.2.val
    (fun y ↦ iteratedFDeriv ℝ i.1.val (wideSuperposition A d v) y w) x.swap
      (fun _ ↦ (1, 0)) = _
  rw [htrans, iteratedFDeriv_wideIntegral hV hceil hAt hd hM hb,
    ContinuousMultilinearMap.integral_apply
      (integrable_wideSuperposition hceil
        (contDiffOn_atomPhysicalJet isOpen_univ hV hAt i.2.2.val).continuousOn
        hd hM hb v (mem_univ x.swap))]
  apply integral_congr_ae
  filter_upwards [] with η
  rw [FiniteChain.Graph.CartesianJets.jet_eq_mixed_evaluated_iteratedFDeriv
    (f η).val.property.1]
  rfl

include hceil hd hM hb in
/-- Finite-band density integrability with a norm-continuous source family
(`app:ch_lag:eq:lag-W0-definition`). -/
private theorem integrable_wideDensity_smul_continuous
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {g : Euclidean (n - 1) → G} (hg : ContinuousOn g V) (v : WideInput n J) :
    Integrable (fun η ↦ weightedWideDensity d v η • g η) := by
  exact integrable_wideSuperposition (U := (univ : Set ℝ)) hceil
    (hg.comp continuous_snd.continuousOn (fun _ hz ↦ hz.2)) hd hM hb v (mem_univ 0)

include hceil in
/-- The original density vanishes off its supplied frequency buffer
(`app:ch_lag:eq:lag-W0-definition`). -/
private theorem wideDensity_zero_off_domain (v : WideInput n J)
    {η : Euclidean (n - 1)} (hη : η ∉ V) : weightedWideDensity d v η = 0 := by
  apply wideDensity_eq_zero_of_ceiling_le
  have hn : η ∉ Metric.closedBall 0 ((2 : ℝ) ^ J) := fun h ↦ hη (hceil h)
  exact le_of_lt (by simpa using hn)

include hV hceil hS hf hd hM hb in
/-- The actual source jets are integrable in the original Sobolev completion,
using only the finite-band density and joint source regularity
(`app:ch_lag:eq:lag-recurrence`). -/
theorem integrable_wideSourceSobolev (s : ℕ) (v : WideInput n J) :
    Integrable (fun η ↦ weightedWideDensity d v η • ofTest s volume (f η).val) := by
  apply integrable_wideDensity_smul_continuous hceil hd hM hb ?_ v
  intro η hη
  apply ContinuousAt.continuousWithinAt
  exact (contDiffAt_ofTest_of_commonCompactSupport hV hS (fun a ↦ (f a).val)
    (hf.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
      (fun _ hz ↦ ⟨mem_univ _, hz.1⟩))
    (fun a _ ↦ (f a).property) s 0 hη).continuousAt

/-- The Sobolev realization of the synthesized source is the Bochner integral
of the SAME atomic source realizations. Every coordinate is the original
Lebesgue L² jet (`app:ch_lag:eq:lag-recurrence`). -/
theorem ofTest_wideSourceTest_eq_integral (s : ℕ) (v : WideInput n J) :
    ofTest s volume (wideSourceTest hV hceil hS f hf hd hM hb v).val =
      ∫ η, weightedWideDensity d v η • ofTest s volume (f η).val := by
  let K : Set ((Fin d₀ → ℝ) × ℝ) := Prod.swap ⁻¹' S
  have hK : IsCompact K := (Homeomorph.prodComm _ _).isCompact_preimage.mpr hS
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hsource := integrable_wideSourceSobolev hV hceil hS f hf hd hM hb s v
  apply Subtype.ext
  funext i
  let F := L2Family.compactFamily (K := K) (fun η ↦ jet i (f η).val.val)
  have hj := contDiffOn_jet hV (fun η ↦ (f η).val)
    (hf.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
      (fun _ hz ↦ ⟨mem_univ _, hz.1⟩)) i
  have hF : Integrable (fun η ↦ weightedWideDensity d v η • F η) :=
    integrable_wideDensity_smul_continuous hceil hd hM hb
      (L2Family.compactFamily_continuousOn hj) v
  have hpoint (η : Euclidean (n - 1)) :
      L2Family.compactToL2 hK (weightedWideDensity d v η • F η) =
        weightedWideDensity d v η • jetMap s volume (f η).val i := by
    by_cases hη : η ∈ V
    · change (L2Family.extendZero_memLp hK _).toLp _ =
        weightedWideDensity d v η • (jet_memLp volume i (f η).val).toLp _
      rw [← MemLp.toLp_const_smul]
      apply MemLp.toLp_congr
      filter_upwards [] with x
      by_cases hx : x ∈ K
      · rw [L2Family.extendZero_mem _ hx]
        simp only [ContinuousMap.smul_apply]
        rw [L2Family.compactFamily_apply hj hη]
        rfl
      · rw [L2Family.extendZero_notMem _ hx]
        have hz := jet_eq_zero_off_tsupport i (f η).val.property.1 x
          (fun h ↦ hx ((f η).property h))
        simp [hz]
    · simp [wideDensity_zero_off_domain hceil v hη]
  have hwhole : L2Family.compactToL2 hK
      (∫ η, weightedWideDensity d v η • F η) =
      jetMap s volume (wideSourceTest hV hceil hS f hf hd hM hb v).val i := by
    change (L2Family.extendZero_memLp hK _).toLp _ =
      (jet_memLp volume i (wideSourceTest hV hceil hS f hf hd hM hb v).val).toLp _
    apply MemLp.toLp_congr
    filter_upwards [] with x
    by_cases hx : x ∈ K
    · rw [L2Family.extendZero_mem _ hx, ContinuousMap.integral_apply hF,
        jet_wideSourceTest hV hceil hS f hf hd hM hb]
      apply integral_congr_ae
      filter_upwards [] with η
      by_cases hη : η ∈ V
      · simp only [ContinuousMap.smul_apply]
        rw [L2Family.compactFamily_apply hj hη]
      · simp [wideDensity_zero_off_domain hceil v hη]
    · rw [L2Family.extendZero_notMem _ hx]
      exact (jet_eq_zero_off_tsupport i
        (wideSourceTest hV hceil hS f hf hd hM hb v).val.property.1 x
        (fun h ↦ hx ((wideSourceTest hV hceil hS f hf hd hM hb v).property h))).symm
  let ev : Sobolev s (volume : Measure ((Fin d₀ → ℝ) × ℝ)) →L[ℂ] Lp ℂ 2 volume :=
    (ContinuousLinearMap.proj i).comp (sobolevSubmodule s volume).subtypeL
  change jetMap s volume (wideSourceTest hV hceil hS f hf hd hM hb v).val i =
    ev (∫ η, weightedWideDensity d v η • ofTest s volume (f η).val)
  rw [← hwhole, ← (L2Family.compactToL2 hK).integral_comp_comm hF,
    ← ev.integral_comp_comm hsource]
  exact integral_congr_ae (Filter.Eventually.of_forall hpoint)

end JanetCartan.CanonicalAtomRealization
