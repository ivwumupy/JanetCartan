module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.RetainedAssembly.ExternalWeights
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Supported

/-!
# Original external weights on the selected product cells

The finite normalized selection retains product cells containing the entire
detector support. Choose the external weights there before forming the mean or
source, keeping the supplied measurement radius. The product geometry controls
the whole weight collar, including points outside the detector support.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff
namespace JanetCartan.PositiveBackground
open ContinuumRow CanonicalConic RetainedAssembly.ExternalWeights ActualCarriers
open ContinuumAdjoint.Canonical.PhaseExtension FullPhaseCharts.ActualComparison

/-- Choose the original squared weights on the product cells returned by
`NormalizedSelection.exists_finite_incidence_geometry_rawAdjoints_and_sampling`.
Their open plateaus contain the full original carrier projection, for every
supplied angular width. The SAME measurement radius works on their entire
supports. These choices precede the source, density and inverse
(`app:ch_background:prop:bg-positive`, `app:ch_background:eq:bg-density-four`,
`new:sec:order-of-choices`). This theorem selects weights only at the original
selection point; it does not replace weights of an already constructed mean. -/
theorem exists_selected_product_external_weights
    {n : ℕ} {A : Type*}
    (zRoot : A → Euclidean 3) {am R : A → ℝ} (ham : ∀ a, 0 < am a)
    (V : A → Set CarrierParameter) (hV : ∀ a, IsOpen (V a))
    (hselected : ∀ a, supportedChart (n := n) (zRoot a) (am a) ⊆
      ball (0 : Euclidean n) (R a) ×ˢ V a)
    {r : ℝ} (hr : 0 < r) (hram : ∀ a, 6 * r < am a) :
    ∃ χ : A → CarrierParameter → ℝ,
      (∀ a, ContDiff ℝ ∞ (χ a)) ∧
      (∀ a z, χ a z ∈ Icc (0 : ℝ) 1) ∧
      (∀ a, HasCompactSupport (χ a)) ∧
      (∀ a, tsupport (χ a) ⊆ V a) ∧
      (∀ a, carrierSupport (zRoot a) (r := am a) ⊆ interior {z | χ a z = 1}) ∧
      (∀ a, closedBall (0 : Euclidean n) (6 * r) ×ˢ V a ⊆
        ball (0 : Euclidean n) (R a) ×ˢ V a) ∧
      (∀ a, ContDiff ℝ ∞ (squaredCarrierWeight (χ a))) ∧
      (∀ a z, 0 ≤ squaredCarrierWeight (χ a) z) ∧
      (∀ a, tsupport (squaredCarrierWeight (χ a)) = tsupport (χ a)) ∧
      (∀ a, IsFiniteMeasure (squaredCarrierMeasure (χ a))) ∧
      ∀ (θ : A → Euclidean (n - 1)) (width : A → ℝ) (hwidth : ∀ a, 0 < width a),
        (∀ a z η, angularMask (zRoot a) (θ a) (ham a) (hwidth a) z η ≠ 0 →
          χ a z = 1) ∧
        ∀ (N : ℕ) (d : A → CarrierData n N),
          (∀ a, (d a).angularCutoff = angularMask (zRoot a) (θ a) (ham a) (hwidth a)) →
          ∀ a (f : CarrierVariable n → ℂ) (p : CarrierVariable n),
            squaredCarrierWeight (χ a) p.1 * UncutDensity.initialDensity (d a) 4 f p =
              UncutDensity.initialDensity (d a) 4 f p := by
  classical
  have hKV (a : A) : carrierSupport (zRoot a) (r := am a) ⊆ V a := by
    intro z hz
    exact (@hselected a (0, z) ⟨mem_closedBall_self (by have := ham a; positivity), hz⟩).2
  have hcutoff (a : A) : ∃ χ : CarrierParameter → ℝ,
      ContDiff ℝ ∞ χ ∧ (∀ z, χ z ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ V a ∧
      carrierSupport (zRoot a) (r := am a) ⊆ interior {z | χ z = 1} := by
    have hK := carrierSupport_compact (zRoot a) (r := am a)
    obtain ⟨W, hW, hKW, hWV, hWc⟩ :=
      exists_open_between_and_isCompact_closure hK (hV a) (hKV a)
    obtain ⟨L, _hL, hLc, hKL, hLW⟩ := exists_compact_closed_between hK hW hKW
    obtain ⟨χ, hχ, hχrange, hχsupport, hχone⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW hLc hLW
    have hs : tsupport χ = closure W := by rw [tsupport, hχsupport]
    exact ⟨χ, hχ, fun z ↦ hχrange (mem_range_self z),
      (show IsCompact (tsupport χ) from hs.symm ▸ hWc), hs.symm ▸ hWV,
      hKL.trans (interior_mono (fun z hz ↦ (hχone z).mp hz))⟩
  choose χ hχ hχrange hχcompact hχV hplateau using hcutoff
  refine ⟨χ, hχ, hχrange, hχcompact, hχV, hplateau, ?_,
    fun a ↦ squaredCarrierWeight_contDiff (hχ a),
    fun a z ↦ squaredCarrierWeight_nonneg (χ a) z,
    fun a ↦ squaredCarrierWeight_tsupport (χ a),
    fun a ↦ squaredCarrierMeasure_finite (hχ a) (hχcompact a), ?_⟩
  · intro a p hp
    have hz : (zRoot a 0, spectatorCenter (zRoot a)) ∈
        carrierSupport (zRoot a) (r := am a) :=
      ⟨mem_closedBall_self (half_pos (ham a)).le, mem_closedBall_self (half_pos (ham a)).le⟩
    exact ⟨(@hselected a (p.1, (zRoot a 0, spectatorCenter (zRoot a)))
      ⟨(closedBall_subset_closedBall (by linarith [hram a])) hp.1,
      hz⟩).1, hp.2⟩
  · intro θ width hwidth
    have hp (a : A) (z : CarrierParameter) (η : Euclidean (n - 1))
        (h : angularMask (zRoot a) (θ a) (ham a) (hwidth a) z η ≠ 0) : χ a z = 1 := by
      obtain ⟨hs, hv, _⟩ := angularMask_nonzero (zRoot a) (θ a) (ham a) (hwidth a) h
      exact (show z ∈ {q | χ a q = 1} from
        interior_subset (hplateau a ⟨ball_subset_closedBall hs, ball_subset_closedBall hv⟩))
    refine ⟨hp, ?_⟩
    intro N d hd a f p
    apply UncutDensity.externalWeight_mul_initialDensity
    intro z η h
    rw [hd a] at h
    exact hp a z η h

end JanetCartan.PositiveBackground
