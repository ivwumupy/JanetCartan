module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.PhaseProfiles.External

/-!
# Normalized primitive annular phase profiles from original two-time data

For `app:ch_response:lem:energy-carrier-jets`, the normalization is literally
`annularExternalPhase / (λ + ‖ξ‖)`, with external variable `(c,x)` and source
`z`. Both orientations and both physical/demodulated observations are covered.
The original joint two-time and carrier profiles produce the constants before
any varying scale, elapsed time, frequency, parameter, or phase is chosen.
The scale `L` is retained until the final comparison `L ≤ K` from
`app:ch_response:eq:direct-envelope-profile`.

The open two-time chart is required only at the frequency under consideration.
No boundedness or annular restriction is imposed on that frequency. Thus the
same result applies on all supported shoulders and the unbounded tail; where
beta vanishes the parent uses `annularExternalJet_elapsed_eq_zero_of_beta_eq_zero`.
No extension of the literal phase is made.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
open FourierIntegral RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open PhaseProfiles
variable {C : Type} {d : ℕ}
local notation "E" => Euclidean (d + 1)

/-- Exact normalized primitive input to `norm_normalizedExternalJet_source_le`.
The output carrier remains in the demodulated phase before differentiating.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
def normalizedAnnularExternalPhase (adjoint demodulated : Bool)
    (Θ : E → E → ℝ) (φ : C → E → ℝ) (lam : ℝ) (ξ : E)
    (p : C × E) (z : E) : ℝ :=
  annularExternalPhase adjoint demodulated Θ φ lam ξ p z / (lam + ‖ξ‖)

/-- Literal reconstruction of the full phase, everywhere, including the
output demodulator. No supported extension or phase increment is substituted.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem mul_normalizedAnnularExternalPhase (adjoint demodulated : Bool)
    (Θ : E → E → ℝ) (φ : C → E → ℝ) {lam : ℝ} (hlam : 1 ≤ lam)
    (ξ : E) (p : C × E) (z : E) :
    (lam + ‖ξ‖) * normalizedAnnularExternalPhase adjoint demodulated Θ φ lam ξ p z =
      annularExternalPhase adjoint demodulated Θ φ lam ξ p z := by
  have hρ : lam + ‖ξ‖ ≠ 0 := ne_of_gt (by positivity)
  exact mul_div_cancel₀ _ hρ

variable [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- Smoothness on the original open physical and parameter neighborhoods,
obtained from the original joint two-time phase by the actual elapsed map.
The map assumption is solely chart containment. No elapsed or normalized
phase regularity is assumed (`app:ch_response:lem:energy-carrier-jets`). -/
theorem contDiffOn_normalizedAnnularExternalPhase_elapsed
    {V : Set C} {U X : Set E} {O : Set (TwoTimePoint d)}
    (adjoint demodulated : Bool) (Ψ : TwoTimePhase d) (φ : C → E → ℝ)
    (t lam : ℝ) (ξ : E)
    (hΨ : ContDiffOn ℝ ∞ (jointPhase Ψ) O)
    (hmap : ∀ y ∈ U ∪ X, elapsedPoint t ((y, 0), ξ) ∈ O)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ (U ∪ X))) :
    ContDiffOn ℝ ∞ (Function.uncurry (normalizedAnnularExternalPhase
      adjoint demodulated (elapsedPhase Ψ t) φ lam ξ)) ((V ×ˢ X) ×ˢ U) :=
  (contDiffOn_annularExternalPhase adjoint demodulated (elapsedPhase Ψ t) φ lam ξ
    (contDiffOn_elapsedPhase_fixedFrequency Ψ hΨ t ξ hmap) hφ).div_const _

/-- Explicit constant depending only on the fixed physical radius, slab
length, and ORIGINAL profile constants. Consumer: the primitive phase input
of `norm_normalizedExternalJet_source_le` (`energy-carrier-jets`). -/
def annularPhaseProfileBudget (R Δ : ℝ) (BΨ Bφ : ℕ → ℝ) (m : ℕ) : ℝ :=
  (R + Δ + 1 + BΨ m) + (R + 1) + 2 * Bφ m

/-- Nonnegativity needed by the external-jet polynomial budget. -/
theorem annularPhaseProfileBudget_nonneg {R Δ : ℝ} (hR : 0 ≤ R) (hΔ : 0 ≤ Δ)
    (BΨ Bφ : ℕ → ℝ) (hΨ : ∀ m, 0 ≤ BΨ m) (hφ : ∀ m, 0 ≤ Bφ m) (m : ℕ) :
    0 ≤ annularPhaseProfileBudget R Δ BΨ Bφ m := by
  unfold annularPhaseProfileBudget
  linarith [hΨ m, hφ m]

/-- Original joint two-time jets and original joint carrier jets give the
normalized phase bound at each joint external/source order. The only phase
jets in the premises are those of the original `jointPhase Ψ` and `φ`.
All physical frequencies are allowed. Source: `app:ch_response:lem:energy-carrier-jets`,
preserving `L ≤ K` in `app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_iteratedFDeriv_normalizedAnnularExternalPhase_elapsed_le
    {V : Set C} {U X : Set E} {O : Set (TwoTimePoint d)}
    (hV : IsOpen V) (hU : IsOpen U) (hX : IsOpen X) (hO : IsOpen O)
    (adjoint demodulated : Bool) (Ψ : TwoTimePhase d) (φ : C → E → ℝ)
    {lam L K R Δ t : ℝ} (hlam : 1 ≤ lam) (hL : 1 ≤ L) (hLK : L ≤ K)
    (hR : 0 ≤ R) (ht : t ∈ Icc 0 Δ) (ξ : E)
    (hΨ : ContDiffOn ℝ ∞ (jointPhase Ψ) O)
    (hmap : ∀ y ∈ U ∪ X, elapsedPoint t ((y, 0), ξ) ∈ O)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ (U ∪ X)))
    (BΨ Bφ : ℕ → ℝ) (hBΨ : ∀ m, 0 ≤ BΨ m) (hBφ : ∀ m, 0 ≤ Bφ m)
    (p : C × E) (z : E) (hp : p ∈ V ×ˢ X) (hz : z ∈ U)
    (hxR : ‖p.2‖ ≤ R) (hzR : ‖z‖ ≤ R) (m : ℕ)
    (hΨb : ∀ y ∈ ({p.2, z} : Set E),
      ‖iteratedFDeriv ℝ m (jointPhase Ψ) (elapsedPoint t ((y, 0), ξ))‖ ≤
        BΨ m * (1 + ‖ξ‖) * L ^ m)
    (hφb : ∀ y ∈ ({p.2, z} : Set E),
      ‖iteratedFDeriv ℝ m (Function.uncurry φ) (p.1, y)‖ ≤ Bφ m * L ^ m) :
    ‖iteratedFDeriv ℝ m (Function.uncurry (normalizedAnnularExternalPhase
      adjoint demodulated (elapsedPhase Ψ t) φ lam ξ)) (p, z)‖ ≤
      annularPhaseProfileBudget R Δ BΨ Bφ m * K ^ m := by
  have hΘ := contDiffOn_elapsedPhase_fixedFrequency Ψ hΨ t ξ hmap
  have hBΘ : 0 ≤ R + Δ + 1 + BΨ m := by linarith [hBΨ m, ht.1, ht.2]
  have hΘb : ∀ y ∈ ({p.2, z} : Set E),
      ‖iteratedFDeriv ℝ m (fun y => elapsedPhase Ψ t y ξ) y‖ ≤
        (R + Δ + 1 + BΨ m) * (1 + ‖ξ‖) * L ^ m := by
    intro y hy
    have hy' : y = p.2 ∨ y = z := by simpa using hy
    have hyR : ‖y‖ ≤ R := by rcases hy' with rfl | rfl <;> assumption
    have hyW : y ∈ U ∪ X := by
      rcases hy' with rfl | rfl
      · exact Or.inr hp.2
      · exact Or.inl hz
    exact norm_iteratedFDeriv_elapsedPhase_fixedFrequency_le hO Ψ hΨ hR ht hL ξ y hyR
      (hmap y hyW) m (hΨb y hy)
  have hb := norm_iteratedFDeriv_annularExternalPhase_le hV hU hX adjoint demodulated
    (elapsedPhase Ψ t) φ hlam hL hLK hR hBΘ (hBφ m) ξ hΘ hφ p z hp hz hxR hzR m hΘb hφb
  have hs : ContDiffAt ℝ ∞ (Function.uncurry
      (annularExternalPhase adjoint demodulated (elapsedPhase Ψ t) φ lam ξ)) (p, z) :=
    (contDiffOn_annularExternalPhase adjoint demodulated (elapsedPhase Ψ t)
    φ lam ξ hΘ hφ).contDiffAt (((hV.prod hX).prod hU).mem_nhds ⟨hp, hz⟩)
  have hρ : 0 < lam + ‖ξ‖ := by positivity
  have he : Function.uncurry (normalizedAnnularExternalPhase adjoint demodulated
      (elapsedPhase Ψ t) φ lam ξ) = fun q => (lam + ‖ξ‖)⁻¹ •
        Function.uncurry (annularExternalPhase adjoint demodulated (elapsedPhase Ψ t) φ lam ξ) q := by
    funext q
    simp [Function.uncurry, normalizedAnnularExternalPhase, div_eq_mul_inv, mul_comm]
  rw [he, iteratedFDeriv_const_smul_apply' (hs.of_le (by simp)), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hρ.le)]
  apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hρ.le)).trans_eq
  unfold annularPhaseProfileBudget
  field_simp

/-- Uniform primitive phase profiles on fixed supported parameter/output/source
sets. Constants are chosen BEFORE `λ,L,K,t,ξ,Ψ,φ` and the open charts. The
original joint phase profile is required only on a chart `J` containing the
actual two-time evaluations, and the carrier profile on the original compact
positions. Thus `J` and its open neighborhood may depend on the supported
physical frequency, including the unbounded tail. `β = 0` is handled by the
published literal zero-jet theorem and requires none of these hypotheses.

The scale constraints retain fixed `0 < ν < 1` and `1 ≤ L ≤ K ≤ λ^(1-ν)`;
this phase estimate itself only needs `L ≤ K`. The resulting `H` is the input
to `norm_normalizedExternalJet_source_le`. Source: `energy-carrier-jets` and
`app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_normalizedAnnularExternalPhase_profile
    (P : Set C) {X₀ S : Set E} (hX₀ : IsCompact X₀) (hS : IsCompact S)
    {Δ ν : ℝ} (hΔ : 0 ≤ Δ) (_hν : 0 < ν) (_hν1 : ν < 1)
    (BΨ Bφ : ℕ → ℝ) (hBΨ : ∀ m, 0 ≤ BΨ m) (hBφ : ∀ m, 0 ≤ Bφ m) :
    ∃ H : ℕ → ℝ, (∀ m, 0 ≤ H m) ∧
      ∀ (lam L K t : ℝ), 1 ≤ lam → 1 ≤ L → L ≤ K → K ≤ lam ^ (1 - ν) → t ∈ Icc 0 Δ →
      ∀ (ξ : E) (Ψ : TwoTimePhase d) (φ : C → E → ℝ)
        (V : Set C) (U X : Set E) (J O : Set (TwoTimePoint d)),
      IsOpen V → IsOpen U → IsOpen X → IsOpen O → P ⊆ V → S ⊆ U → X₀ ⊆ X → J ⊆ O →
      ContDiffOn ℝ ∞ (jointPhase Ψ) O →
      (∀ y ∈ U ∪ X, elapsedPoint t ((y, 0), ξ) ∈ O) →
      (∀ y ∈ S ∪ X₀, elapsedPoint t ((y, 0), ξ) ∈ J) →
      ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ (U ∪ X)) →
      (∀ m q, q ∈ J → ‖iteratedFDeriv ℝ m (jointPhase Ψ) q‖ ≤ BΨ m * (1 + ‖ξ‖) * L ^ m) →
      (∀ m c, c ∈ P → ∀ y ∈ S ∪ X₀,
        ‖iteratedFDeriv ℝ m (Function.uncurry φ) (c, y)‖ ≤ Bφ m * L ^ m) →
      ∀ (adjoint demodulated : Bool),
      ContDiffOn ℝ ∞ (Function.uncurry (normalizedAnnularExternalPhase
        adjoint demodulated (elapsedPhase Ψ t) φ lam ξ)) ((V ×ˢ X) ×ˢ U) ∧
      (∀ p z, (lam + ‖ξ‖) * normalizedAnnularExternalPhase
        adjoint demodulated (elapsedPhase Ψ t) φ lam ξ p z =
          annularExternalPhase adjoint demodulated (elapsedPhase Ψ t) φ lam ξ p z) ∧
      ∀ m p, p ∈ P ×ˢ X₀ → ∀ z ∈ S,
        ‖iteratedFDeriv ℝ m (Function.uncurry (normalizedAnnularExternalPhase
          adjoint demodulated (elapsedPhase Ψ t) φ lam ξ)) (p, z)‖ ≤ H m * K ^ m := by
  obtain ⟨R₀, hR₀⟩ := (hS.union hX₀).exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun x : E => x) (S ∪ X₀))
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hrad : ∀ y ∈ S ∪ X₀, ‖y‖ ≤ R := fun y hy => (hR₀ y hy).trans (le_max_left _ _)
  refine ⟨annularPhaseProfileBudget R Δ BΨ Bφ,
    annularPhaseProfileBudget_nonneg hR hΔ BΨ Bφ hBΨ hBφ, ?_⟩
  intro lam L K t hlam hL hLK _hscale ht ξ Ψ φ V U X J O hV hU hX hO hPV hSU hXX
    _hJO hΨ hmap hmapJ hφ hΨb hφb adjoint demodulated
  refine ⟨contDiffOn_normalizedAnnularExternalPhase_elapsed adjoint demodulated Ψ φ
    t lam ξ hΨ hmap hφ, mul_normalizedAnnularExternalPhase adjoint demodulated
      (elapsedPhase Ψ t) φ hlam ξ, ?_⟩
  intro m p hp z hz
  apply norm_iteratedFDeriv_normalizedAnnularExternalPhase_elapsed_le hV hU hX hO
    adjoint demodulated Ψ φ hlam hL hLK hR ht ξ hΨ hmap hφ BΨ Bφ hBΨ hBφ p z
    ⟨hPV hp.1, hXX hp.2⟩ (hSU hz) (hrad _ (Or.inr hp.2)) (hrad _ (Or.inl hz)) m
  · intro y hy
    have hy' : y ∈ S ∪ X₀ := by
      rcases (show y = p.2 ∨ y = z by simpa using hy) with rfl | rfl
      · exact Or.inr hp.2
      · exact Or.inl hz
    exact hΨb m _ (hmapJ y hy')
  · intro y hy
    apply hφb m p.1 hp.1 y
    rcases (show y = p.2 ∨ y = z by simpa using hy) with rfl | rfl
    · exact Or.inr hp.2
    · exact Or.inl hz

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
