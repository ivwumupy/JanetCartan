module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.Demodulation
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.PhaseExtension

/-!
# Literal kernels for the selected low estimate

Connect the full graph calculus to the carrier-increment kernels in
`app:ch_response:eq:direct-envelope-profile`. The reverse amplitude exchanges
both physical positions and conjugate-transposes the entire matrix. In
particular the weighted coordinate inverse is realized by applying the forward
construction to its exchanged conjugate transpose, retaining `j_S U⁻¹`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.NearCarrierFullLow
open FourierIntegral FourierIntegral.FullLowBounds FourierIntegral.LowBounds.FrequencyCutoff
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The full adjoint amplitude in output-first order. This preserves every
source mask and weight in `app:ch_response:eq:direct-envelope-profile`. -/
def exchangedAdjointAmplitude (A : FullAmplitude n r) : FullAmplitude n r :=
  fun y x δ ↦ (A x y δ).conjTranspose

/-- Exchanging and conjugate-transposing twice recovers the complete weighted
amplitude, as required for the reverse construction in
`app:ch_regular_base:eq:actual-matrix-inverse`. -/
@[simp] theorem exchangedAdjointAmplitude_involutive (A : FullAmplitude n r) :
    exchangedAdjointAmplitude (exchangedAdjointAmplitude A) = A := by
  funext x y δ
  exact Matrix.conjTranspose_conjTranspose _

/-- The generic reverse graph and the near-carrier reverse integral have the
same literal normalization and opposite phase. Only the physical argument
order changes (`app:ch_response:eq:direct-envelope-profile`). -/
theorem reverseGraphOperator_phaseIncrement_eq_envelopeGraph
    (S : E → E → ℝ) (ζ : E) (ρ : ℝ) (A : FullAmplitude n r)
    (f : E → Fin r → ℂ) :
    reverseGraphOperator (phaseIncrement S ζ ρ) A f =
      ReverseDerivative.envelopeGraph S ζ ρ (fun y x δ ↦ A x y δ) f := by
  rw [ReverseDerivative.envelopeGraph_eq_reverseGraph]
  rfl

/-- Literal adjoint kernel, including complex frequency cutoff conjugation,
for `app:ch_response:eq:direct-envelope-profile`. -/
theorem reverseGraphOperator_cut_adjoint_eq_envelopeGraph
    (S : E → E → ℝ) (ζ : E) (ρ : ℝ) (A : FullAmplitude n r)
    (χ : E → ℂ) (f : E → Fin r → ℂ) :
    reverseGraphOperator (phaseIncrement S ζ ρ)
      (frequencyCutFullAmplitude (fun δ ↦ star (χ δ))
        (fun x y δ ↦ (A x y δ).conjTranspose)) f =
      ReverseDerivative.envelopeGraph S ζ ρ
        (frequencyCutFullAmplitude (fun δ ↦ star (χ δ))
          (exchangedAdjointAmplitude A)) f :=
  reverseGraphOperator_phaseIncrement_eq_envelopeGraph S ζ ρ _ f

/-- The selected complete amplitude is smooth in both positions and physical
frequency displacement. Consumer: the low realization of
`app:ch_response:eq:direct-envelope-profile`. -/
theorem contDiff_forwardSelectedAmplitude
    (A : FullAmplitude n r) (ζ : E) (ρ : ℝ) (q : E → ℂ)
    (hA : ContDiff ℝ ∞ (fun p : E × E × E ↦ A p.1 p.2.1 p.2.2))
    (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (fun p : E × E × E ↦
      forwardSelectedAmplitude A ζ ρ q p.1 p.2.1 p.2.2) := by
  have he : forwardSelectedAmplitude A ζ ρ q =
      fun x y δ ↦ q δ • A x y (ρ • ζ + δ) := by
    funext x y δ
    simp [forwardSelectedAmplitude, selectedAmplitude]
  rw [he]
  exact (hq.comp contDiff_snd.snd).smul
    (hA.comp (contDiff_fst.prodMk
      (contDiff_snd.fst.prodMk (contDiff_const.add contDiff_snd.snd))))

/-- The actual selector cuts only the amplitude; all physical masks remain
and the datum is unrestricted (`app:ch_response:eq:direct-envelope-profile`). -/
theorem forwardSelectedAmplitude_support
    (A : FullAmplitude n r) (ζ : E) (ρ : ℝ) (q : E → ℂ)
    {X Y : Set E} (hs : ∀ x y η, x ∉ X ∨ y ∉ Y → A x y η = 0)
    (x y δ : E) (h : x ∉ X ∨ y ∉ Y ∨ δ ∉ tsupport q) :
    forwardSelectedAmplitude A ζ ρ q x y δ = 0 := by
  rcases h with hx | hy | hδ
  · simp [forwardSelectedAmplitude, selectedAmplitude, hs x y _ (Or.inl hx)]
  · simp [forwardSelectedAmplitude, selectedAmplitude, hs x y _ (Or.inr hy)]
  · simp [forwardSelectedAmplitude, selectedAmplitude, image_eq_zero_of_notMem_tsupport hδ]

/-- On compact selected frequency support the unregularized adjoint is also
its literal test integral. This uses the actual full-amplitude adjoint theorem,
not an identification of transport adjoint with weighted coordinate inverse.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem compact_frequency_adjoint_ae
    (S : E → E → ℝ) (ζ : E) (ρ : ℝ)
    (hΦ : ContDiff ℝ ∞ (Function.uncurry (phaseIncrement S ζ ρ)))
    (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : E × E × E ↦ A p.1 p.2.1 p.2.2))
    {X Y F : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    (hs : ∀ x y δ, x ∉ X ∨ y ∉ Y → A x y δ = 0)
    (hf : ∀ x y δ, δ ∉ F → A x y δ = 0)
    (T : H →L[ℂ] H)
    (hT : ∀ u : graphTestSpace n r, T (graphTestToLp u) =ᵐ[volume]
      graphTestOutput (phaseIncrement S ζ ρ) A u)
    (u : graphTestSpace n r) :
    T.adjoint (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
      (ReverseDerivative.envelopeGraph S ζ ρ (exchangedAdjointAmplitude A)
        (fun x ↦ (u.val x).ofLp) y) := by
  obtain ⟨b, hb⟩ := hF.isBounded.subset_closedBall (0 : E)
  obtain ⟨j, hj⟩ := exists_nat_gt b
  have hone (δ : E) (hδ : δ ∈ F) : complexPhysicalCutoff j δ = 1 := by
    have hh : ‖δ‖ ≤ b := by simpa using hb hδ
    simp only [complexPhysicalCutoff, physicalCutoff_eq_one j
      (hh.trans (by dsimp [radius]; linarith)), Complex.ofReal_one]
  have he : frequencyCutFullAmplitude (complexPhysicalCutoff j) A = A := by
    funext x y δ
    by_cases hδ : δ ∈ F
    · simp [frequencyCutFullAmplitude, hone δ hδ]
    · simp [frequencyCutFullAmplitude, hf x y δ hδ]
  have hea : frequencyCutFullAmplitude (fun δ ↦ star (complexPhysicalCutoff j δ))
      (fun x y δ ↦ (A x y δ).conjTranspose) =
        (fun x y δ ↦ (A x y δ).conjTranspose) := by
    funext x y δ
    by_cases hδ : δ ∈ F
    · simp [frequencyCutFullAmplitude, hone δ hδ]
    · simp [frequencyCutFullAmplitude, hf x y δ hδ]
  have hreal := compactFullGraph_adjoint_ae (phaseIncrement S ζ ρ) hΦ A hA hX hY hs
    (complexPhysicalCutoff j) (complexPhysicalCutoff_contDiff j)
    (complexPhysicalCutoff_hasCompactSupport j) T (by
      change ∀ v, T (graphTestToLp v) =ᵐ[volume]
        graphTestOutput (phaseIncrement S ζ ρ)
          (frequencyCutFullAmplitude (complexPhysicalCutoff j) A) v
      rw [he]
      exact hT) u
  change T.adjoint (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
    (ReverseDerivative.envelopeGraph S ζ ρ (fun y x δ ↦ (A x y δ).conjTranspose)
      (fun x ↦ (u.val x).ofLp) y)
  simpa only [hea, reverseGraphOperator_phaseIncrement_eq_envelopeGraph] using hreal

end JanetCartan.ResponseTransfer.NearCarrierFullLow
