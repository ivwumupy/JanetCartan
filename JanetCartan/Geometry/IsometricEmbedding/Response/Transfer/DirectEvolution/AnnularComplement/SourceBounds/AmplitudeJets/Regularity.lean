module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.Products
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Support

/-!
# Source regularity of all four literal normalized annular jets

Original amplitude and envelope smoothness produce joint smoothness of the
literal vector amplitude. Original phase smoothness is needed only near the
source support and the observation point. These deductions supply the
smoothness and fixed-support inputs of `norm_annularSourceIntegral_le`.
Source: `app:ch_response:lem:energy-carrier-jets`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
open FourierIntegral JanetCartan.Localization
open RegularSector.Characteristic.EvolutionIntegral
variable {C : Type} [NormedAddCommGroup C] [NormedSpace ℝ C] {n r : ℕ}
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- Joint smoothness of the actual vector amplitude, including the fixed
selector. Conjugate transpose in the adjoint is a real continuous linear map.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiffOn_annularExternalAmplitude
    {V : Set C} (adjoint : Bool) (A : FullAmplitude n r) (π : E → ℂ)
    (lam : ℝ) (a : C → E → F) (ξ : E)
    (hA : ContDiff ℝ ∞ (fun q : E × E => A q.1 q.2 ξ))
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (V ×ˢ univ)) :
    ContDiffOn ℝ ∞ (Function.uncurry (annularExternalAmplitude adjoint A π lam a ξ))
      ((V ×ˢ univ) ×ˢ univ) := by
  have hf : ContDiffOn ℝ ∞ (fun q : (C × E) × E => a q.1.1 q.2)
      ((V ×ˢ univ) ×ˢ univ) :=
    ha.comp (contDiffOn_fst.fst.prodMk contDiffOn_snd) (fun _ hq => ⟨hq.1.1, mem_univ _⟩)
  cases adjoint with
  | false =>
    have hb : ContDiffOn ℝ ∞ (fun q : (C × E) × E =>
        annularComplementAmplitude π lam A q.1.2 q.2 ξ) ((V ×ˢ univ) ×ˢ univ) :=
      (hA.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffOn.const_smul _
    exact ((annularMatrixAction r).contDiff.comp_contDiffOn hb).clm_apply hf
  | true =>
    have hb : ContDiffOn ℝ ∞ (fun q : (C × E) × E =>
        annularComplementAmplitude π lam A q.2 q.1.2 ξ) ((V ×ˢ univ) ×ˢ univ) :=
      (hA.comp (contDiff_snd.prodMk contDiff_fst.snd)).contDiffOn.const_smul _
    have hstar : ContDiff ℝ ∞ (fun M : Matrix (Fin r) (Fin r) ℂ => M.conjTranspose) :=
      (starL ℝ : Matrix (Fin r) (Fin r) ℂ ≃L[ℝ] Matrix (Fin r) (Fin r) ℂ).contDiff
    exact ((annularMatrixAction r).contDiff.comp_contDiffOn
      (hstar.comp_contDiffOn hb)).clm_apply hf

/-- Primitive phase smoothness for both observations. The output phase is
retained on `X`; the source phase is needed only on `U`. The common domain
`U ∪ X` is an original phase neighborhood, not a global extension.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiffOn_annularExternalPhase
    {V : Set C} {U X : Set E} (adjoint demodulated : Bool)
    (Θ : E → E → ℝ) (φ : C → E → ℝ) (lam : ℝ) (ξ : E)
    (hΘ : ContDiffOn ℝ ∞ (fun y => Θ y ξ) (U ∪ X))
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ (U ∪ X))) :
    ContDiffOn ℝ ∞ (Function.uncurry (annularExternalPhase adjoint demodulated Θ φ lam ξ))
      ((V ×ˢ X) ×ˢ U) := by
  have hsource : ContDiffOn ℝ ∞ (fun q : (C × E) × E => lam * φ q.1.1 q.2)
      ((V ×ˢ X) ×ˢ U) :=
    contDiffOn_const.mul (hφ.comp (contDiffOn_fst.fst.prodMk contDiffOn_snd)
      (fun _ hq => ⟨hq.1.1, Or.inl hq.2⟩))
  have houtput : ContDiffOn ℝ ∞ (fun q : (C × E) × E => lam * φ q.1.1 q.1.2)
      ((V ×ˢ X) ×ˢ U) :=
    contDiffOn_const.mul (hφ.comp contDiffOn_fst
      (fun _ hq => ⟨hq.1.1, Or.inr hq.1.2⟩))
  have hfwd : ContDiffOn ℝ ∞ (fun q : (C × E) × E =>
      forwardCarrierSourcePhase Θ (φ q.1.1) lam q.1.2 ξ q.2) ((V ×ˢ X) ×ˢ U) :=
    ((hΘ.comp contDiffOn_fst.snd (fun _ hq => Or.inr hq.1.2)).sub
      (contDiffOn_snd.inner ℝ contDiffOn_const)).add hsource
  have hadj : ContDiffOn ℝ ∞ (fun q : (C × E) × E =>
      adjointCarrierSourcePhase Θ (φ q.1.1) lam q.1.2 ξ q.2) ((V ×ˢ X) ×ˢ U) :=
    ((contDiffOn_fst.snd.inner ℝ contDiffOn_const).sub
      (hΘ.comp contDiffOn_snd (fun _ hq => Or.inl hq.2))).add hsource
  cases adjoint <;> cases demodulated
  · exact hfwd.sub contDiffOn_const
  · exact hfwd.sub houtput
  · exact hadj.sub contDiffOn_const
  · exact hadj.sub houtput

/-- All four actual normalized external jets are globally source-smooth.
Only original phase, full amplitude, envelope and support inputs are used.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiff_annularExternalJet
    {V : Set C} {U X S : Set E} (hV : IsOpen V) (hU : IsOpen U) (hX : IsOpen X)
    (hS : IsClosed S) (hSU : S ⊆ U)
    (adjoint demodulated : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : C → E → ℝ) (lam : ℝ) (a : C → E → F) (ξ : E)
    (hΘ : ContDiffOn ℝ ∞ (fun y => Θ y ξ) (U ∪ X))
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ (U ∪ X)))
    (hA : ContDiff ℝ ∞ (fun q : E × E => A q.1 q.2 ξ))
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (a c) ⊆ S)
    (j : ℕ) (v : Fin j → C × E) (p : C × E) (hp : p ∈ V ×ˢ X) :
    ContDiff ℝ ∞ (annularExternalJet adjoint demodulated Θ A π φ lam a ξ j v p) := by
  exact contDiff_normalizedExternalJet (hV.prod hX) hU hS hSU
    (contDiffOn_annularExternalPhase adjoint demodulated Θ φ lam ξ hΘ hφ)
    ((contDiffOn_annularExternalAmplitude adjoint A π lam a ξ hA ha).mono
      (prod_mono (prod_mono Subset.rfl (subset_univ X)) Subset.rfl))
    (fun q hq => (tsupport_annularExternalAmplitude_subset adjoint A π lam a ξ q).trans
      (hs q.1 hq.1)) j v hp

/-- The actual elapsed substitution discharges amplitude regularity from the
original two-time symbol and both physical masks. Beta is retained. The phase
hypothesis still concerns the original elapsed phase on its supported chart.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiff_elapsedAnnularExternalJet {d : ℕ}
    {V : Set C} {U X S : Set (Euclidean (d + 1))}
    (hV : IsOpen V) (hU : IsOpen U) (hX : IsOpen X)
    (hS : IsClosed S) (hSU : S ⊆ U)
    (adjoint demodulated : Bool) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
    (χout χsource β π : Euclidean (d + 1) → ℂ)
    (φ : C → Euclidean (d + 1) → ℝ) (t lam : ℝ)
    (a : C → Euclidean (d + 1) → F) (ξ : Euclidean (d + 1))
    (hΘ : ContDiffOn ℝ ∞ (fun y => elapsedPhase Ψ t y ξ) (U ∪ X))
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ (U ∪ X)))
    (hb : ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude b))
    (hout : ContDiff ℝ ∞ χout) (hsource : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (a c) ⊆ S)
    (j : ℕ) (v : Fin j → C × Euclidean (d + 1)) (p : C × Euclidean (d + 1))
    (hp : p ∈ V ×ˢ X) :
    ContDiff ℝ ∞ (annularExternalJet adjoint demodulated (elapsedPhase Ψ t)
      (elapsedAmplitude b χout χsource β t) π φ lam a ξ j v p) := by
  apply contDiff_annularExternalJet hV hU hX hS hSU adjoint demodulated
    (elapsedPhase Ψ t) (elapsedAmplitude b χout χsource β t) π φ lam a ξ hΘ hφ _ ha hs j v p hp
  exact (SymbolBudgets.contDiff_uncurry_elapsedAmplitude b χout χsource β hb hout hsource hβ t).comp
    (contDiff_id.prodMk contDiff_const)

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
