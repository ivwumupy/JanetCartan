module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.Identification
public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.UniformSymbol
public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.PhaseTransfer
public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry

/-!
# The actual uncut cross-normal from original local data

Both bounded graphs and their full-amplitude cross PDO are constructed from the
original local phase and amplitude jets. The construction underlying
`WholeImageGeometry.exists_graphL2_of_wholeImage_phase` is applied twice with one
source annulus and one smooth phase extension. The whole-image inverse, its
finite jets, all cutoff budgets, compact identities and limits are proved by
the existing producers. No inverse estimate or operator is an input.

This is the pure cross-normal in `app:ch_regular_base:eq:actual-normal-kernel`
and `app:ch_regular_base:eq:actual-normal-amplitude`, before source multiplication.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.UncutNormal
open NormalComparison LowBounds LowBounds.FrequencyCutoff WholeImageGeometry Pseudodifferential
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

private theorem carrier_closed (A B : E → E → Mat) : IsClosed (jointNormalCarrier A B) :=
  ((isClosed_tsupport (Function.uncurry A)).preimage
    (continuous_fst.prodMk continuous_snd.snd)).inter
    ((isClosed_tsupport (Function.uncurry B)).preimage
      (continuous_snd.fst.prodMk continuous_snd.snd))

private theorem carrier_subset {A B : E → E → Mat} {X D : Set E}
    (hA : tsupport (Function.uncurry A) ⊆ X ×ˢ D)
    (hB : tsupport (Function.uncurry B) ⊆ X ×ˢ D) :
    jointNormalCarrier A B ⊆ X ×ˢ (X ×ˢ D) :=
  fun _ hq ↦ ⟨(hA hq.1).1, (hB hq.2).1, (hA hq.1).2⟩

private theorem amplitude_zero {A : E → E → Mat} {X D : Set E}
    (hA : tsupport (Function.uncurry A) ⊆ X ×ˢ D)
    (x u : E) (h : x ∉ X ∨ u ∉ D) : A x u = 0 := by
  by_contra hne
  have hp := hA (subset_tsupport (Function.uncurry A)
    (show (x, u) ∈ Function.support (Function.uncurry A) from hne))
  exact h.elim (fun hx ↦ hx hp.1) (fun hu ↦ hu hp.2)

/-- Construct both source-independent graphs from original buffered phase data
and identify their pure cross product with the existing matrix two-position PDO
of the literal uncut zero extension. The physical covector is `2 * π * ξ` in
`cycleCrossNormalSymbol`; both positions and both complete masks are retained.

The constants and source-band endpoints precede the fields and amplitude sizes.
The phase gap and injectivity are required only on the chart. The same compact
regularizations converge strongly and distributionally to the identified PDO.
No bounded graph, inverse estimate, normal budget or limiting identity is an input.
Source: `app:ch_regular_base:eq:actual-normal-kernel` and
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem exists_uncut_crossNormal_of_wholeImage_phase (hn : 0 < n) (R B₀ Bφ : ℝ)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ a > 0, ∃ b > a, ∃ C > 0, ∃ Cnormal > 0,
      ∀ (X D : Set E) (O : Set (E × E)) (S : E → E → ℝ) (A B : E → E → Mat)
        (α β : ℝ), 0 ≤ α → 0 ≤ β → IsOpen X → IsOpen D → Convex ℝ X → IsOpen O →
      closure (X ×ˢ D) ⊆ O → ContDiffOn ℝ ∞ (Function.uncurry S) O →
      (∀ x ∈ X, ∀ u ∈ D, ∀ t : ℝ, 0 < t → t • u ∈ D →
        S x (t • u) = t * S x u) →
      (∀ x ∈ X, ∀ u ∈ D,
        ‖fderiv ℝ (fun v ↦ fderiv ℝ (fun z ↦ S z v) x) u‖ ≤ B₀) →
      (∀ x ∈ X, ∀ y ∈ X, InjOn (averagedGradient S x y) D) →
      (∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D, δ ≤ |(averagedJacobian S x y u).det|) →
      (∀ u ∈ D, ε < ‖u‖) →
      (∀ j : ℕ, ∀ z ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
        ∀ k ≤ wholeImagePhaseReserve n, ‖iteratedFDeriv ℝ k
          (Function.uncurry (normalizedPhase ((2 : ℝ)^j) S)) z‖ ≤ Bφ) →
      (∀ x ∈ X, ‖x‖ ≤ R) →
      ContDiffOn ℝ ∞ (Function.uncurry A) (X ×ˢ D) →
      ContDiffOn ℝ ∞ (Function.uncurry B) (X ×ˢ D) →
      (∀ j : ℕ, ∀ z ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
        ∀ k ≤ primitiveNormalReserve n, ‖iteratedFDeriv ℝ k
          (Function.uncurry (normalizedNormalMatrix ((2 : ℝ)^j) 0 A)) z‖ ≤ α) →
      (∀ j : ℕ, ∀ z ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
        ∀ k ≤ primitiveNormalReserve n, ‖iteratedFDeriv ℝ k
          (Function.uncurry (normalizedNormalMatrix ((2 : ℝ)^j) 0 B)) z‖ ≤ β) →
      ∀ (hA : Continuous (Function.uncurry A)) (hB : Continuous (Function.uncurry B))
        (KA KB : Set E) (hKA : IsCompact KA) (hKB : IsCompact KB)
        (hsA : ∀ x u, x ∉ KA → A x u = 0) (hsB : ∀ x u, x ∉ KB → B x u = 0),
      tsupport (Function.uncurry A) ⊆ X ×ˢ D →
      tsupport (Function.uncurry B) ⊆ X ×ˢ D →
      ∀ (PA PB : ℝ) (kA kB : ℕ),
      (∀ x u, ‖A x u‖ ≤ PA * (1 + ‖u‖ ^ kA)) →
      (∀ x u, ‖B x u‖ ≤ PB * (1 + ‖u‖ ^ kB)) →
      ∃ T U : H →L[ℂ] H,
        ‖T‖ ≤ C * α ∧ ‖T.adjoint‖ ≤ C * α ∧
        ‖U‖ ≤ C * β ∧ ‖U.adjoint‖ ≤ C * β ∧
        (∀ u : SchwartzMap E (Fin r → ℂ), T (schwartzVectorToLp u) =ᵐ[volume]
          fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ v ↦ A z v) u x)) ∧
        (∀ u : SchwartzMap E (Fin r → ℂ), U (schwartzVectorToLp u) =ᵐ[volume]
          fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ v ↦ B z v) u x)) ∧
        ∃ hb : GraphNormalAmplitudeBounds
          (cycleCrossNormalSymbol D S A B (wholeImageInverse S D) (averagedJacobian S))
          R (Cnormal * α * β),
        let P := vectorTwoPositionL2Operator hn R
          (cycleCrossNormalSymbol D S A B (wholeImageInverse S D) (averagedJacobian S))
          hb.smooth hb.support (Cnormal * α * β) hb.entry_bound
        T.comp U.adjoint = P ∧
        ∃ (S' : E → E → ℝ) (hS' : ContDiff ℝ ∞ (Function.uncurry S')),
          (∀ q ∈ closure (X ×ˢ D), Function.uncurry S' =ᶠ[𝓝 q] Function.uncurry S) ∧
          let Q := fun m ↦ (compactVectorGraph hS'.continuous
            (cutAmplitude_entry_continuous hA m)
            (cutAmplitude_entry_hasCompactSupport hKA hsA m)).comp
            (compactVectorGraph hS'.continuous (cutAmplitude_entry_continuous hB m)
              (cutAmplitude_entry_hasCompactSupport hKB hsB m)).adjoint
          (∀ f : H, Tendsto (fun m ↦ Q m f) atTop (𝓝 (P f))) ∧
          ∀ f : H, Tendsto (fun m ↦ Lp.toTemperedDistribution (Q m f)) atTop
            (𝓝 (Lp.toTemperedDistribution (P f))) := by
  obtain ⟨F, hF, _, _, a, ha, b, hab, M, _, L, _, hinputs⟩ :=
    exists_wholeImage_primitive_inputs (n := n) (r := r) B₀ Bφ hδ hε
  obtain ⟨C, hC, hlow⟩ := exists_graphL2_of_primitive_inputs (r := r) hn R M L hδ hF.le
  obtain ⟨Cnormal, hCnormal, hnormal⟩ :=
    exists_uniform_cycleCrossNormalSymbol_bounds (n := n) (r := r) M L hδ hF.le
  refine ⟨a, ha, b, hab, C, hC, Cnormal, hCnormal, ?_⟩
  intro X D O S A B α β hα hβ hX hD hcX hO hbuffer hS hhom hmix hinj hgap hcollar
    hphase hR hAs hBs hjA hjB hA hB KA KB hKA hKB hsA hsB hsuppA hsuppB PA PB kA kB
    hpolyA hpolyB
  have hSlocal := hS.mono (subset_trans subset_closure hbuffer)
  obtain ⟨chart, hcompare, hgeometry⟩ :=
    hinputs S X D hX hD hcX hSlocal hhom hmix hinj hgap hcollar hphase
  obtain ⟨S', hS', he'⟩ := exists_smooth_phase_extension S isClosed_closure hO hbuffer hS
  have he : EqOn (Function.uncurry S') (Function.uncurry S) (X ×ˢ D) :=
    fun _ hq ↦ (he' _ (subset_closure hq)).eq_of_nhds
  have hdom := bufferedNormalDomain_phase_congr hX hcX he
  have hchart := chart.congr_phase hX hcX he
  have hgrowth (x) (hx : x ∈ X) (y) (hy : y ∈ X) (u) (hu : u ∈ D) :
      ‖averagedGradient S' x y u‖ ≤ F * (1 + ‖u‖) := by
    rw [averagedGradient_phase_congr hX hcX he hx hy hu]
    exact (hcompare x hx y hy u hu).1.trans
      (mul_le_mul_of_nonneg_left (by linarith) hF.le)
  have hdata (A B : E → E → Mat) (α β : ℝ)
      (hAs : ContDiffOn ℝ ∞ (Function.uncurry A) (X ×ˢ D))
      (hBs : ContDiffOn ℝ ∞ (Function.uncurry B) (X ×ˢ D))
      (hjA : ∀ j : ℕ, ∀ z ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
        ∀ k ≤ primitiveNormalReserve n, ‖iteratedFDeriv ℝ k
          (Function.uncurry (normalizedNormalMatrix ((2 : ℝ)^j) 0 A)) z‖ ≤ α)
      (hjB : ∀ j : ℕ, ∀ z ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
        ∀ k ≤ primitiveNormalReserve n, ‖iteratedFDeriv ℝ k
          (Function.uncurry (normalizedNormalMatrix ((2 : ℝ)^j) 0 B)) z‖ ≤ β)
      (hsuppA : tsupport (Function.uncurry A) ⊆ X ×ˢ D)
      (hsuppB : tsupport (Function.uncurry B) ⊆ X ×ˢ D) :=
    hgeometry A B (jointNormalCarrier A B) α β (carrier_closed A B)
      (carrier_subset hsuppA hsuppB) hAs hBs
      (fun _ _ hl hr ↦ ⟨subset_tsupport (Function.uncurry A) hl,
        subset_tsupport (Function.uncurry B) hr⟩)
      (fun x u hx ↦ amplitude_zero hsuppA x u (Or.inl hx))
      (fun x u hx ↦ amplitude_zero hsuppB x u (Or.inl hx)) hjA hjB
  have hforward (A B : E → E → Mat)
      (hsuppA : tsupport (Function.uncurry A) ⊆ X ×ˢ D)
      (hsuppB : tsupport (Function.uncurry B) ⊆ X ×ˢ D) :
      ContinuousOn (normalForwardCoordinates S') (jointNormalCarrier A B) := by
    apply ((continuousOn_fst.prodMk (continuousOn_snd.fst.prodMk
      (averagedGradient_contDiffOn hX hD hcX hSlocal).continuousOn)).mono
        (carrier_subset hsuppA hsuppB)).congr
    intro q hq
    exact normalForwardCoordinates_phase_congr hX hcX he (carrier_subset hsuppA hsuppB hq)
  have hop (A : E → E → Mat) (hsupp : tsupport (Function.uncurry A) ⊆ X ×ˢ D)
      (v : E → Fin r → ℂ) : graphOperator S' (fun x _ u ↦ A x u) v =
        graphOperator S (fun x _ u ↦ A x u) v := by
    apply graphOperator_phase_congr S S' _ _ v
    intro x _ u hne
    exact he (hsupp (subset_tsupport (Function.uncurry A)
      (show (x, u) ∈ Function.support (Function.uncurry A) from hne)))
  obtain ⟨gA, sA⟩ := hdata A A α α hAs hAs hjA hjA hsuppA hsuppA
  obtain ⟨gB, sB⟩ := hdata B B β β hBs hBs hjB hjB hsuppB hsuppB
  obtain ⟨gAB, sAB⟩ := hdata A B α β hAs hBs hjA hjB hsuppA hsuppB
  obtain ⟨T, hTnorm, hTanorm, _, hT, _, _, _, _, _, _⟩ :=
    hlow X D S' A _ _ _ _ _ α hα hchart
      (gA.congr_phase chart hX hcX he (carrier_subset hsuppA hsuppA)) hR hgrowth
      (fun l ↦ by rw [hdom]; exact sA l)
      hS'.continuous hA KA hKA hsA (amplitude_zero hsuppA) (hforward A A hsuppA hsuppA)
      PA kA hpolyA
  obtain ⟨U, hUnorm, hUanorm, _, hU, _, _, _, _, _, _⟩ :=
    hlow X D S' B _ _ _ _ _ β hβ hchart
      (gB.congr_phase chart hX hcX he (carrier_subset hsuppB hsuppB)) hR hgrowth
      (fun l ↦ by rw [hdom]; exact sB l)
      hS'.continuous hB KB hKB hsB (amplitude_zero hsuppB) (hforward B B hsuppB hsuppB)
      PB kB hpolyB
  have gAB' := gAB.congr_phase chart hX hcX he (carrier_subset hsuppA hsuppB)
  obtain ⟨hb', hcuts⟩ := hnormal X D S' A B _ _ _ _ _ R α β hα hβ hchart gAB' hR hgrowth
    (fun l ↦ by rw [hdom]; exact sAB l)
  have hsymbol := cycleCrossNormalSymbol_phase_congr A B (wholeImageInverse S D)
    (averagedJacobian S) hX hcX he gAB.left_output gAB.right_output
  have hb : GraphNormalAmplitudeBounds
      (cycleCrossNormalSymbol D S A B (wholeImageInverse S D) (averagedJacobian S))
      R (Cnormal * α * β) := hsymbol ▸ hb'
  have hidentity := cross_eq_vectorTwoPositionL2Operator_of_realizes hchart gAB'
    hS'.continuous hA hB hKA hKB hsA hsB (amplitude_zero hsuppA)
    (hforward A B hsuppA hsuppB) hn R _ hb' hcuts T U hT hU
  simp only [hsymbol] at hidentity
  refine ⟨T, U, hTnorm, hTanorm, hUnorm, hUanorm, ?_, ?_, hb, hidentity,
    S', hS', he', ?_, ?_⟩
  · intro u
    simpa only [hop A hsuppA] using hT u
  · intro u
    simpa only [hop B hsuppB] using hU u
  · intro f
    have hlim := compactVectorGraph_cut_cross_tendsto_of_realizes
      hS'.continuous hA hB hKA hKB hsA hsB T U hT hU f
    simpa only [← hidentity, ContinuousLinearMap.comp_apply] using hlim
  · intro f
    have hlim := compactVectorGraph_cut_cross_tendsto_of_realizes
      hS'.continuous hA hB hKA hKB hsA hsB T U hT hU f
    simpa only [← hidentity, ContinuousLinearMap.comp_apply, Function.comp_def,
      Lp.toTemperedDistributionCLM_apply] using
      (Lp.toTemperedDistributionCLM (EuclideanSpace ℂ (Fin r)) (volume : Measure E) 2).continuous.continuousAt.tendsto.comp hlim

end JanetCartan.FourierIntegral.UncutNormal
