module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.PhaseProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.OriginalProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.MixedBounds

/-!
# Literal annular amplitude jets from original primitives

Source: `app:ch_response:lem:energy-carrier-jets`, preserving
`app:ch_response:eq:direct-envelope-profile`. The consumer is
`norm_annularSourceIntegral_le`.

The original two-time phase and symbol, both physical masks, the fixed beta
and selector, and the original supported envelope Sobolev profiles produce
the normalized external jet estimate. Its fixed exponents are
`d_j = ell_j = 0`, `b_j = n + 1 + j`, and `s_j = j`, with `n = d + 1`.
They are independent of the source derivative and later integration orders.
Only envelope parameter orders through `j` are used.

All frequencies are allowed. Original phase and symbol charts are needed
only where beta is nonzero. No supported extension changes the literal
kernel, and the output demodulator is differentiated before normalization.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
open FourierIntegral RegularSector.Characteristic.EvolutionIntegral SymbolBudgets
open OriginalProfiles Complement.ParameterDerivatives Complement.InactiveSource
open JanetCartan.Pseudodifferential
variable {p d r : ℕ}
local notation "P" => Euclidean p
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin r)

set_option backward.isDefEq.respectTransparency false in
/-- Local joint smoothness of the literal elapsed vector amplitude, from
the original symbol and masks on the original chart. Consumer: the mixed
normalized jet estimate in `app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiffOn_originalAnnularExternalAmplitude
    (adjoint : Bool) (b : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ)
    (t lam : ℝ) (ξ : E) {J : Set (TwoTimePoint d)}
    (hb : ContDiffOn ℝ ∞ (jointAmplitude b) J)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    {V : Set P} {X U : Set E}
    (hmap : ∀ q ∈ X ×ˢ U, elapsedPoint t ((if adjoint then q.swap else q), ξ) ∈ J)
    {a : P → E → F} (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (V ×ˢ univ)) :
    ContDiffOn ℝ ∞ (Function.uncurry (annularExternalAmplitude adjoint
      (elapsedAmplitude b χout χsource β t) π lam a ξ)) ((V ×ˢ X) ×ˢ U) := by
  have hm : ContDiffOn ℝ ∞ (fun q : (P × E) × E =>
      originalAnnularMatrix adjoint b χout χsource β π t lam ξ (q.1.2, q.2))
      ((V ×ˢ X) ×ˢ U) := (contDiffOn_originalAnnularMatrix adjoint b χout χsource β π
    t lam ξ hb ho hs hmap).comp (contDiffOn_fst.snd.prodMk contDiffOn_snd)
      (fun _ hq => ⟨hq.1.2, hq.2⟩)
  have he : ContDiffOn ℝ ∞ (fun q : (P × E) × E => a q.1.1 q.2)
      ((V ×ˢ X) ×ˢ U) := ha.comp (contDiffOn_fst.fst.prodMk contDiffOn_snd)
    (fun _ hq => ⟨hq.1.1, mem_univ _⟩)
  simpa only [Function.uncurry_def, Function.comp_def,
    annularExternalAmplitude_eq_originalAnnularMatrix]
    using ((annularMatrixAction r).contDiff.comp_contDiffOn hm).clm_apply he

/-- The actual normalized jets have one source scale factor `K^k`, with
all constants chosen before scales, time, frequency, phases, symbols, masks,
carrier parameters and envelopes. The displayed loss is
`A₀ * (λ + ‖ξ‖)^j * K^(n+1+j)`; equivalently the requested four fixed
exponents are `(0,0,n+1+j,j)`. The two-scale window and fixed `0 < ν < 1`
are retained, though the proof only uses `1 ≤ L ≤ K` and `1 ≤ λ`.

Every analytic premise concerns an ORIGINAL primitive. In particular the
two-time derivatives are evaluated at the actual elapsed coordinates, and
the envelope norms are of its actual parameter derivatives, only through
`j`. There is no elapsed/modified amplitude or normalized-jet premise.
The conclusion includes global source smoothness and the same support for
every source derivative. The beta-zero branch needs no phase regularity.
Source: `app:ch_response:lem:energy-carrier-jets` and
`app:ch_response:eq:direct-envelope-profile`.
Consumer: `norm_annularSourceIntegral_le`. -/
theorem exists_originalAnnularExternalJet_profile
    (P₀ : Set P) {X₀ S : Set E} (hX₀ : IsCompact X₀) (hS : IsCompact S)
    {Δ ν : ℝ} (hΔ : 0 ≤ Δ) (_hν : 0 < ν) (_hν1 : ν < 1)
    (BΨ Bφ O T B : ℕ → ℝ) (C : ℕ → ℕ → ℝ) (Mβ Mπ : ℝ)
    (hBΨ : ∀ m, 0 ≤ BΨ m) (hBφ : ∀ m, 0 ≤ Bφ m)
    (hO : ∀ m, 0 ≤ O m) (hT : ∀ m, 0 ≤ T m) (hB : ∀ m, 0 ≤ B m)
    (hMβ : 0 ≤ Mβ) (hMπ : 0 ≤ Mπ) :
    ∃ D : ℕ → ℕ → ℝ, (∀ j k, 0 ≤ D j k) ∧
      ∀ (j : ℕ) (lam L K t A₀ : ℝ),
      1 ≤ lam → 1 ≤ L → L ≤ K → K ≤ lam ^ (1 - ν) → t ∈ Icc 0 Δ → 0 ≤ A₀ →
      ∀ (ξ : E) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
        (χout χsource β π : E → ℂ) (φ : P → E → ℝ)
        (V : Set P) (U X : Set E) (OΨ Ob : Set (TwoTimePoint d))
        (hV : IsOpen V) (_hU : IsOpen U) (_hX : IsOpen X)
        (_hOΨ : IsOpen OΨ) (_hOb : IsOpen Ob)
        (_hPV : P₀ ⊆ V) (_hSU : S ⊆ U) (_hXX : X₀ ⊆ X)
        (a : P → E → F) (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (V ×ˢ univ))
        (has : ∀ c ∈ V, tsupport (a c) ⊆ S),
      ContDiff ℝ ∞ χout → ContDiff ℝ ∞ χsource →
      ‖β ξ‖ ≤ Mβ → ‖π (lam⁻¹ • ξ)‖ ≤ Mπ →
      (β ξ ≠ 0 → ContDiffOn ℝ ∞ (jointPhase Ψ) OΨ) →
      (β ξ ≠ 0 → ContDiffOn ℝ ∞ (jointAmplitude b) Ob) →
      (β ξ ≠ 0 → ∀ y ∈ U ∪ X, elapsedPoint t ((y, 0), ξ) ∈ OΨ) →
      (β ξ ≠ 0 → ∀ y ∈ U ∪ X, elapsedPoint t ((y, 0), ξ) ∈ Ob) →
      (β ξ ≠ 0 → ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ (U ∪ X))) →
      (β ξ ≠ 0 → ∀ m y, y ∈ S ∪ X₀ →
        ‖iteratedFDeriv ℝ m (jointPhase Ψ) (elapsedPoint t ((y, 0), ξ))‖ ≤
          BΨ m * (1 + ‖ξ‖) * L ^ m) →
      (β ξ ≠ 0 → ∀ m c, c ∈ P₀ → ∀ y ∈ S ∪ X₀,
        ‖iteratedFDeriv ℝ m (Function.uncurry φ) (c, y)‖ ≤ Bφ m * L ^ m) →
      (β ξ ≠ 0 → ∀ m y, y ∈ S ∪ X₀ →
        ‖iteratedFDeriv ℝ m (jointAmplitude b) (elapsedPoint t ((y, 0), ξ))‖ ≤
          B m * L ^ m) →
      (∀ m y, y ∈ S ∪ X₀ → ‖iteratedFDeriv ℝ m χout y‖ ≤ O m) →
      (∀ m y, y ∈ S ∪ X₀ → ‖iteratedFDeriv ℝ m χsource y‖ ≤ T m) →
      (∀ (c : P) (hc : c ∈ V), c ∈ P₀ →
        ∀ l ≤ j, ∀ w : Fin l → P, (∀ i, ‖w i‖ ≤ 1) → ∀ s : ℕ,
        MemVectorFourierSobolev (s : ℝ)
          ((parameterSource_memLp hS hV ha has l w hc).toLp
            (fun y => iteratedFDeriv ℝ l (fun q => a q y) c w))) →
      (∀ (c : P) (hc : c ∈ V), c ∈ P₀ →
        ∀ l ≤ j, ∀ w : Fin l → P, (∀ i, ‖w i‖ ≤ 1) → ∀ s : ℕ,
        vectorFourierSobolevNorm (s : ℝ)
          ((parameterSource_memLp hS hV ha has l w hc).toLp
            (fun y => iteratedFDeriv ℝ l (fun q => a q y) c w)) ≤
              C l s * A₀ * K ^ (s + l)) →
      ∀ (adjoint demodulated : Bool) (v : Fin j → P × E), (∀ i, ‖v i‖ ≤ 1) →
      ∀ p ∈ P₀ ×ˢ X₀,
        ContDiff ℝ ∞ (annularExternalJet adjoint demodulated (elapsedPhase Ψ t)
          (elapsedAmplitude b χout χsource β t) π φ lam a ξ j v p) ∧
        tsupport (annularExternalJet adjoint demodulated (elapsedPhase Ψ t)
          (elapsedAmplitude b χout χsource β t) π φ lam a ξ j v p) ⊆ S ∧
        ∀ k, tsupport (iteratedFDeriv ℝ k (annularExternalJet adjoint demodulated
          (elapsedPhase Ψ t) (elapsedAmplitude b χout χsource β t) π φ lam a ξ j v p)) ⊆ S ∧
        ∀ z, ‖iteratedFDeriv ℝ k (annularExternalJet adjoint demodulated
          (elapsedPhase Ψ t) (elapsedAmplitude b χout χsource β t) π φ lam a ξ j v p) z‖ ≤
            D j k * (A₀ * (lam + ‖ξ‖) ^ j * K ^ (d + 1 + 1 + j)) * K ^ k := by
  obtain ⟨R₀, hR₀⟩ := (hS.union hX₀).exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun x : E => x) (S ∪ X₀))
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hrad : ∀ y ∈ S ∪ X₀, ‖y‖ ≤ R := fun y hy => (hR₀ y hy).trans (le_max_left _ _)
  let H := annularPhaseProfileBudget R Δ BΨ Bφ
  let Q := originalMixedBudget (d + 1) r O T B C Mβ Mπ
  have hH := annularPhaseProfileBudget_nonneg hR hΔ BΨ Bφ hBΨ hBφ
  have hQ := originalMixedBudget_nonneg (d + 1) r C hO hT hB hMβ hMπ
  refine ⟨mixedExternalJetBudget H Q, mixedExternalJetBudget_nonneg hH hQ, ?_⟩
  intro j lam L K t A₀ hlam hL hLK _hscale ht hA ξ Ψ b χout χsource β π φ
    V U X OΨ Ob hV hU hX hOΨ hOb hPV hSU hXX a ha has ho hs hβξ hπξ
    hΨ hb hmapΨ hmapb hφ hΨb hφb hbb hout hsource hmem hprofile adjoint demodulated v hv p hp
  have hpV : p ∈ V ×ˢ X := ⟨hPV hp.1, hXX hp.2⟩
  have hsupport := tsupport_sourceDerivative_annularExternalJet_subset hV hS.isClosed
    adjoint demodulated (elapsedPhase Ψ t) (elapsedAmplitude b χout χsource β t)
    π φ lam a has ξ j v p hpV.1
  have hsupport₀ := tsupport_annularExternalJet_subset hV hS.isClosed
    adjoint demodulated (elapsedPhase Ψ t) (elapsedAmplitude b χout χsource β t)
    π φ lam a has ξ j v p hpV.1
  have hK : 1 ≤ K := hL.trans hLK
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hρ : 1 ≤ lam + ‖ξ‖ := hlam.trans (le_add_of_nonneg_right (norm_nonneg _))
  by_cases hβ : β ξ = 0
  · have he := annularExternalJet_elapsed_eq_zero_of_beta_eq_zero adjoint demodulated
      Ψ b χout χsource β π φ t lam a ξ hβ j v p
    refine ⟨?_, hsupport₀, fun k => ⟨hsupport k, ?_⟩⟩
    · rw [he]; exact contDiff_const
    · intro z
      rw [he]
      have hD := mixedExternalJetBudget_nonneg hH hQ j k
      simpa using mul_nonneg (mul_nonneg hD
        (mul_nonneg (mul_nonneg hA (pow_nonneg (zero_le_one.trans hρ) j))
          (pow_nonneg hK0 _))) (pow_nonneg hK0 k)
  have hmatrixMap : ∀ q ∈ X ×ˢ U,
      elapsedPoint t ((if adjoint then q.swap else q), ξ) ∈ Ob := by
    intro q hq
    cases adjoint
    · simpa only [Bool.false_eq_true, ite_false, elapsedPoint_eq] using
        hmapb hβ q.1 (Or.inr hq.1)
    · simpa only [ite_true, elapsedPoint_eq, Prod.fst_swap] using
        hmapb hβ q.2 (Or.inl hq.2)
  have hu := contDiffOn_originalAnnularExternalAmplitude adjoint b χout χsource β π
    t lam ξ (hb hβ) ho hs hmatrixMap ha
  have hψ := contDiffOn_normalizedAnnularExternalPhase_elapsed adjoint demodulated
    Ψ φ t lam ξ (hΨ hβ) (hmapΨ hβ) (hφ hβ)
  have he : (fun q z => (lam + ‖ξ‖) * normalizedAnnularExternalPhase
      adjoint demodulated (elapsedPhase Ψ t) φ lam ξ q z) =
      annularExternalPhase adjoint demodulated (elapsedPhase Ψ t) φ lam ξ := by
    funext q z
    exact mul_normalizedAnnularExternalPhase adjoint demodulated (elapsedPhase Ψ t) φ hlam ξ q z
  have hus : ∀ q ∈ V ×ˢ X, tsupport (annularExternalAmplitude adjoint
      (elapsedAmplitude b χout χsource β t) π lam a ξ q) ⊆ S :=
    fun q hq => (tsupport_annularExternalAmplitude_subset adjoint
      (elapsedAmplitude b χout χsource β t) π lam a ξ q).trans (has q.1 hq.1)
  refine ⟨?_, hsupport₀, fun k => ⟨hsupport k, fun z => ?_⟩⟩
  · exact contDiff_normalizedExternalJet_of_support_neighborhood (hV.prod hX) hU
      hS.isClosed hSU (contDiffOn_annularExternalPhase adjoint demodulated
        (elapsedPhase Ψ t) φ lam ξ
        (PhaseProfiles.contDiffOn_elapsedPhase_fixedFrequency Ψ (hΨ hβ) t ξ (hmapΨ hβ))
        (hφ hβ)) hu hus j v hpV
  · have hphase (z : E) (hz : z ∈ S) (m : ℕ) (_hm : m ≤ k + j) :
        ‖iteratedFDeriv ℝ m (Function.uncurry (normalizedAnnularExternalPhase
          adjoint demodulated (elapsedPhase Ψ t) φ lam ξ)) (p, z)‖ ≤ H m * K ^ m := by
      apply norm_iteratedFDeriv_normalizedAnnularExternalPhase_elapsed_le hV hU hX hOΨ
        adjoint demodulated Ψ φ hlam hL hLK hR ht ξ (hΨ hβ) (hmapΨ hβ) (hφ hβ)
        BΨ Bφ hBΨ hBφ p z hpV (hSU hz) (hrad _ (Or.inr hp.2)) (hrad _ (Or.inl hz)) m
      · intro y hy
        apply hΨb hβ m y
        rcases (show y = p.2 ∨ y = z by simpa using hy) with rfl | rfl
        · exact Or.inr hp.2
        · exact Or.inl hz
      · intro y hy
        apply hφb hβ m p.1 hp.1 y
        rcases (show y = p.2 ∨ y = z by simpa using hy) with rfl | rfl
        · exact Or.inr hp.2
        · exact Or.inl hz
    have hamplitude (z : E) (hz : z ∈ S) (l : ℕ) (hl : l ≤ j)
        (w : Fin l → P × E) (hw : ∀ i, ‖w i‖ ≤ 1) (q : ℕ) (_hq : q ≤ k) :
        ‖iteratedFDeriv ℝ q (fun y => iteratedFDeriv ℝ l (fun q =>
          annularExternalAmplitude adjoint (elapsedAmplitude b χout χsource β t)
            π lam a ξ q y) p w) z‖ ≤ Q l q * A₀ * K ^ (d + 1 + 1 + l) * K ^ q := by
      apply norm_mixed_originalAnnularAmplitude_le O T B C Mβ Mπ hO hT hB hMβ hMπ
        adjoint b χout χsource β π t lam ξ hOb (hb hβ) ho hs hV hX hU hS
        hmatrixMap ha has hA hL hLK hK hβξ hπξ l w hw hpV.1 hpV.2 (hSU hz)
        (fun i hi => hmem p.1 hpV.1 hp.1 i (hi.trans hl))
        (fun i hi => hprofile p.1 hpV.1 hp.1 i (hi.trans hl)) q
      · intro i _
        apply hout i
        cases adjoint
        · exact Or.inr hp.2
        · exact Or.inl hz
      · intro i _
        apply hsource i
        cases adjoint
        · exact Or.inl hz
        · exact Or.inr hp.2
      · intro i _
        cases adjoint
        · simpa only [Bool.false_eq_true, ite_false, elapsedPoint_eq] using
            hbb hβ i p.2 (Or.inr hp.2)
        · simpa only [ite_true, elapsedPoint_eq] using hbb hβ i z (Or.inl hz)
    have h := norm_normalizedExternalJet_source_le_mixed_of_support (hV.prod hX) hU
      hS.isClosed hSU hψ hu hus H Q hH hQ hK0 hA hρ (d + 1 + 1) j v hv hpV k
      hphase hamplitude z
    rwa [he] at h

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
