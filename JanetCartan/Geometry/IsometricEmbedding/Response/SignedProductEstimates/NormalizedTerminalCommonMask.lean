module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedTerminalCutSource
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.FinalMask

/-!
# A common realized terminal mask for the corrected source

The existing protected-annular-envelope constructor chooses one physical proof
mask and one closed shoulder before any current coefficient field. Its actual
bounded right quantizations are then constructed by the compact graph API.
The corrected normalized source is estimated on that SAME mask using the
original nested source cutoffs. No compactness of the coefficient class and
no independently chosen replacement family are used.

Consumers: the terminal `hBnear` input and the final proof-mask choice in
`finiteChain_observation_rapidDecayAt` (`app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:resolved-angular-tail`). The original no-return and annular
producers must put their actual terminal sets inside the fixed envelope.
Intermediate mask nesting and complete residual leakage remain separate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace JanetCartan.SignedProductEstimates
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open ArbitraryAccuracy.ProtectedMasks ArbitraryAccuracy.EvolutionIntegratedLocalization
open RegularSector.Characteristic.RetardedLocalization LocalSobolev
open FourierIntegral LowBounds FiniteChain.Graph
variable {d : ℕ} {K Bbase : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "RV" => EuclideanSpace ℝ (Fin (d+1))
local notation "H" => Lp V 2 (volume : Measure E)
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Instantiate the common protected-mask constructor and its actual right
quantizations, then apply the normalized-source estimate on the original recut
data. The mask, shoulder and jet bounds precede the selected family. All
Sobolev-order/accuracy constants precede frequencies, the inner cutoff, source
domains and data. Both literal source orientations and real quadratures retain
the original low collar and fixed loss `d+1+s`. The same mask covers EVERY
subset of the retained common terminal envelope
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:resolved-angular-tail`). -/
theorem exists_common_normalizedSource_terminal_localizer
    (hB : IsCompact Bbase) (hK : IsCompact K) (hsym : ∀ η ∈ K, -η ∈ K)
    {a b ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ (mi : LocalizerSymbol (d+1)) (δ lo hiR R : ℝ) (Djet : ℕ → ℝ)
      (M : {ρ : ℝ // 1 ≤ ρ} → H →L[ℂ] H),
      IsBufferedLocalizer mi (protectedAnnularCarrier Bbase a b ε K)
        (physicalProtectedRegion K) ∧
      0 < δ ∧ 0 < lo ∧ lo < hiR ∧ 0 < R ∧
      tsupport mi ⊆ closedBall 0 R ×ˢ PhysicalShells.frequencyAnnulus lo hiR ∧
      (∀ k, 0 ≤ Djet k) ∧ (∀ k p, ‖iteratedFDeriv ℝ k mi p‖ ≤ Djet k) ∧
      (∀ S ⊆ protectedAnnularCarrier Bbase a b ε K,
        cthickening δ S ⊆ interior {p | mi p = 1}) ∧
      (∀ ρ u, M ρ u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ.1 mi (fun y ↦ (u y).ofLp) x)) ∧
      ∀ {Ω : Set E} {x₀ : E} {RQ C₀ : ℝ} {A₀ : Fin (d+1) → MetricTensor (d+1)}
        (f : ActualMaskFamily Ω x₀ RQ A₀ K C₀) (L₀ : ℝ), f.radialThreshold ≤ L₀ →
      ∀ (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (_hoc : HasCompactSupport output)
        (hor : ∀ y, output y ∈ Icc (0 : ℝ) 1)
        (χ₃ : ContDiffBump x₀) (U : Set E), IsOpen U →
        tsupport (χ₃ : E → ℝ) ⊆ U → U ⊆ ball x₀ f.physicalRadius →
        (∀ y ∈ U, output y = 1) →
      ∃ C Cr : ℕ → ℕ → ℝ, (∀ s q, 0 ≤ C s q) ∧ (∀ s q, 0 ≤ Cr s q) ∧
        ∀ (ρ : {ρ : ℝ // 1 ≤ ρ}) (L : ℝ), 1 ≤ L → L ≤ ρ.1 →
        ∀ χ₂ : ContDiffBump x₀, (∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1) →
        ∀ (s q : ℕ) (D : Set E) (hD : MeasurableSet D)
          (W : Set E) (hW : MeasurableSet W) (u : LocalL2 D V) (backward : Bool),
          let w := SmallSupport.zeroExtend hD (SmallSupport.bumpL2 (p := 2) le_rfl χ₂ u)
          let S := pairedSource f hK L₀ output ho.continuous
            (fun y ↦ (Real.norm_of_nonneg (hor y).1).trans_le (hor y).2)
          let P := if backward then S.adjoint else S
          let v := restrictL2 W ((P-1) (M ρ w))
          (v ∈ (restrictionSobolevScale W V hW).level s ∧
            (restrictionSobolevScale W V hW).gradeNorm s v ≤
              C s q * ρ.1^((d+1+s : ℕ) : ℝ) * L^(0 : ℕ) * (L/ρ.1)^q * ‖u‖) ∧
          ∀ c : ℂ, ‖c‖ = 1 →
            let vr := l2RealPart (volume.restrict W) (c • v)
            vr ∈ (restrictionSobolevScale W RV hW).level s ∧
            (restrictionSobolevScale W RV hW).gradeNorm s vr ≤
              Cr s q * ρ.1^((d+1+s : ℕ) : ℝ) * L^(0 : ℕ) * (L/ρ.1)^q * ‖u‖ := by
  obtain ⟨mi, δ, lo, hiR, R, Djet, hm, hδ, hlo, hhiR, hR, hsupp, hDjet, hjets, hplateau⟩ :=
    exists_common_protectedAnnularLocalizer (b := b) hB hK.isClosed ha hε
  have hbounded (ρ : {ρ : ℝ // 1 ≤ ρ}) := exists_bounded_physicalLocalizers (q := d+1)
    (ne_of_gt (zero_lt_one.trans_le ρ.property)) mi hm.smooth.continuous hm.compactSupport
  choose A hleft hright using hbounded
  let M := fun ρ ↦ (A ρ).adjoint
  refine ⟨mi, δ, lo, hiR, R, Djet, M, hm, hδ, hlo, hhiR, hR, hsupp,
    hDjet, hjets, hplateau, hright, ?_⟩
  intro Ω x₀ RQ C₀ A₀ f L₀ hL₀ output ho hoc hor χ₃ U hU hχ₃ hcore houtput
  have hann : ∀ p ∈ tsupport mi, lo ≤ ‖p.2‖ := fun p hp ↦ (hsupp hp).2.1
  have hterminal : ∀ p ∈ tsupport mi, NormedSpace.normalize p.2 ∈ K := by
    intro p hp
    exact interior_subset (hm.support_subset hp).2
  choose C Cr hC hCr hbound using fun s ↦ exists_normalizedSource_recut_terminal_bounds
    f hK hsym L₀ hL₀ output ho hoc hor χ₃ U hU hχ₃ hcore houtput
    mi hm.smooth hm.compactSupport hlo hann hterminal s
  refine ⟨C, Cr, hC, hCr, ?_⟩
  intro ρ L hL hLρ χ₂ hnest s q D hD W hW u backward
  exact hbound s ρ.1 L hL hLρ (M ρ) (hright ρ) χ₂ hnest q D hD W hW u backward

end JanetCartan.SignedProductEstimates