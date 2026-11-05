module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.CutoffJets.Range
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.CutoffJets.Scalar
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.CutoffGeometry

/-!
# Uniform cutoff jets for two different original amplitudes

The compact cross normals in `app:ch_regular_base:eq:actual-normal-amplitude`
need separate amplitude sizes. This is the two-amplitude version of the existing
self-normal cutoff estimate, on the same cutoff-independent source ranges.
Its consumer is the uncut cross-normal identification.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.UncutNormal
open NormalComparison LowBounds LowBounds.FrequencyCutoff
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Both original amplitudes retain uniform normalized jets after frequency
truncation. The fixed cutoff cost precedes both amplitudes and all shell and
regularization indices. Consumer: the common PDO budget in the uncut limit of
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem exists_cutCrossAmplitude_primitiveNormalShellInputs {F : ℝ} (hF : 0 ≤ F) :
    ∃ Kcut > 0, ∀ (X D : Set E) (S : E → E → ℝ)
      (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
      (M L δ : ℝ), AveragedGradientChart S X D η J δ →
      (∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D,
        ‖averagedGradient S x y u‖ ≤ F * (1 + ‖u‖)) →
      ∀ (A B : E → E → Mat) (a b : ℝ) (V : ℕ → Set (NormalVariables n)),
      0 ≤ a → 0 ≤ b →
      (∀ l, PrimitiveNormalShellInputs A B η J ((2 : ℝ)^l)
        (primitiveNormalReserve n) M L δ a b
        (normalDyadicShell (bufferedNormalDomain X D S) l) (V l)) →
      ∃ V' : ℕ → Set (NormalVariables n),
        (∀ l, V' l ⊆ V l) ∧
        ∀ j l, PrimitiveNormalShellInputs (cutAmplitude A j) (cutAmplitude B j)
          η J ((2 : ℝ)^l) (primitiveNormalReserve n) M L δ (Kcut * a) (Kcut * b)
          (normalDyadicShell (bufferedNormalDomain X D S) l) (V' l) := by
  let N := primitiveNormalReserve n
  let Q := 2 * (1 + F)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  obtain ⟨C, hC, hscalar⟩ := exists_normalizedCutoff_jet_bound (n := n) N hQ
  refine ⟨(2 : ℝ)^N * C, mul_pos (by positivity) hC, ?_⟩
  intro X D S η J M L δ chart hgrowth A B a b V ha hb hinputs
  let V' := fun l ↦ cutoffJetRange (V l) ((2 : ℝ)^l) Q
  refine ⟨V', fun _ _ h ↦ h.1, ?_⟩
  intro j l
  let ρ : ℝ := (2 : ℝ)^l
  have H := hinputs l
  have hV : IsOpen (V' l) := isOpen_cutoffJetRange H.open_range ρ Q
  have hsub : V' l ⊆ V l := fun _ h ↦ h.1
  have hmap : MapsTo (normalInverseCoordinates (normalizedNormalInverse ρ η))
      (normalDyadicShell (bufferedNormalDomain X D S) l) (V' l) :=
    mapsTo_cutoffJetRange chart hgrowth l H.mapsTo
  have hs : ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦
      complexPhysicalCutoff j (ρ • q.2.2)) (V' l) :=
    ((complexPhysicalCutoff_contDiff j).comp (contDiff_snd.snd.const_smul ρ)).contDiffOn
  have hsjet (z) (hz : z ∈ V' l) (k : ℕ) (hk : k ≤ N) :
      ‖iteratedFDeriv ℝ k (fun q : NormalVariables n ↦
        complexPhysicalCutoff j (ρ • q.2.2)) z‖ ≤ C :=
    hscalar ρ (by dsimp [ρ]; positivity) j z hz.2.le k hk
  have hJ := H.input_smooth.fst.mono hsub
  have hA := H.input_smooth.snd.fst.mono hsub
  have hB := H.input_smooth.snd.snd.mono hsub
  refine ⟨H.open_domain, hV, H.inverse_smooth, hmap, ?_,
    fun z hz ↦ H.gap z hz.1, fun z hz ↦ H.jacobianJets z hz.1, ?_, ?_, H.inverseJets⟩
  · change ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦
      (normalizedNormalJacobian ρ J q.1 q.2.1 q.2.2,
        (normalizedNormalMatrix ρ 0 (cutAmplitude A j) q.1 q.2.2,
          normalizedNormalMatrix ρ 0 (cutAmplitude B j) q.2.1 q.2.2))) (V' l)
    simpa only [normalInputCoefficients, normalizedNormalMatrix, neg_zero, Real.rpow_zero,
      one_smul, cutAmplitude, Pi.smul_apply', ρ] using
        hJ.prodMk ((hs.smul hA).prodMk (hs.smul hB))
  · intro z hz k hk
    have hh := InverseChartJet.norm_iteratedFDeriv_bilinear_on_open_le
      (ContinuousLinearMap.lsmul ℝ ℂ) ContinuousLinearMap.opNorm_lsmul_le
      hV hs hA hC.le hz k (fun i hi ↦ hsjet z hz i (hi.trans hk))
      (fun i hi ↦ H.leftJets z hz.1 i (hi.trans hk))
    simp only [ContinuousLinearMap.lsmul_apply] at hh
    apply (show ‖iteratedFDeriv ℝ k (fun q : NormalVariables n ↦
        normalizedNormalMatrix ρ 0 (cutAmplitude A j) q.1 q.2.2) z‖ ≤
        (2 : ℝ)^k * C * a by
      simpa only [normalInputCoefficients, normalizedNormalMatrix, neg_zero, Real.rpow_zero,
        one_smul, cutAmplitude, ρ] using hh).trans
    gcongr
    norm_num
  · intro z hz k hk
    have hh := InverseChartJet.norm_iteratedFDeriv_bilinear_on_open_le
      (ContinuousLinearMap.lsmul ℝ ℂ) ContinuousLinearMap.opNorm_lsmul_le
      hV hs hB hC.le hz k (fun i hi ↦ hsjet z hz i (hi.trans hk))
      (fun i hi ↦ H.rightJets z hz.1 i (hi.trans hk))
    simp only [ContinuousLinearMap.lsmul_apply] at hh
    apply (show ‖iteratedFDeriv ℝ k (fun q : NormalVariables n ↦
        normalizedNormalMatrix ρ 0 (cutAmplitude B j) q.2.1 q.2.2) z‖ ≤
        (2 : ℝ)^k * C * b by
      simpa only [normalInputCoefficients, normalizedNormalMatrix, neg_zero, Real.rpow_zero,
        one_smul, cutAmplitude, ρ] using hh).trans
    gcongr
    norm_num

end JanetCartan.FourierIntegral.UncutNormal
