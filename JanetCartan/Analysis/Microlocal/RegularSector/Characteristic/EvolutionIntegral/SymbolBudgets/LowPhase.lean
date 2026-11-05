module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Phase

/-!
# The normalized elapsed phase supplies the whole-image reserve

The whole-image constructor differentiates the phase on the position/covector
pair, whereas the Sobolev profiles retain a dummy source position. Inserting
zero in that position is a contraction, so the same original joint phase
budget supplies the exact `wholeImagePhaseReserve` input, on every dyadic shell.
Source: `app:ch_regular_base:eq:actual-normal-amplitude` and the fixed-time
representation of the retarded kernel.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FourierIntegral FullAmplitudePrimitiveBudget.Local WholeImageGeometry
variable {d : ℕ}

/-- Insert a dummy source position to compare the whole-image and Sobolev
phase conventions. Consumer: the original phase reserve of `PrimitiveRealization.Family`. -/
def phasePairInclusion : (Euclidean (d + 1) × Euclidean (d + 1)) →L[ℝ] Point (d + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p ↦ ((p.1, 0), p.2)
      map_add' := by intro x y; simp
      map_smul' := by intro a x; simp }

/-- Inserting the dummy source position does not enlarge a joint phase jet. -/
theorem norm_phasePairInclusion_le : ‖phasePairInclusion (d := d)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  simp only [one_mul]
  change ‖((p.1, (0 : Euclidean (d + 1))), p.2)‖ ≤ ‖p‖
  simp only [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg p.1)]
  exact le_rfl

/-- Local phase smoothness is inherited from the original joint phase on its
buffered chart. Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem contDiffOn_jointElapsedPhase {U : Set (TwoTimePoint d)}
    (Ψ : TwoTimePhase d) (hΨ : ContDiffOn ℝ ∞ (jointPhase Ψ) U) (r : ℝ) :
    ContDiffOn ℝ ∞ (fun p : Point (d + 1) ↦ elapsedPhase Ψ r p.1.1 p.2)
      (elapsedPoint r ⁻¹' U) := by
  have hE : ContDiff ℝ ∞ (elapsedPoint (d := d) r) :=
    elapsedLinear.contDiff.add contDiff_const
  have ht : ContDiff ℝ ∞ (fun p : Point (d + 1) ↦ (p.1.1 0 - r) * p.2 0) :=
    (((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (d + 1)) 0).contDiff.comp
      (contDiff_fst.comp contDiff_fst)).sub contDiff_const).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (d + 1)) 0).contDiff.comp contDiff_snd)
  have hs := hΨ.comp hE.contDiffOn (fun _ hp ↦ hp)
  have he : (fun p : Point (d + 1) ↦ elapsedPhase Ψ r p.1.1 p.2) =
      (fun p : Point (d + 1) ↦ (p.1.1 0 - r) * p.2 0) + jointPhase Ψ ∘ elapsedPoint r := by
    funext p
    simp only [Pi.add_apply, elapsedPhase, Function.comp_apply, jointPhase, elapsedPoint_eq]
  rw [he]
  exact ht.contDiffOn.add hs

/-- A literal normalized position/covector phase jet is bounded by the
original normalized two-time phase seminorm, at the same order. Neither
homogeneity nor an elapsed phase jet estimate is a premise. -/
theorem norm_iteratedFDeriv_normalizedElapsedPhase_le
    {K : Set (Point (d + 1))} {J U : Set (TwoTimePoint d)}
    (hK : IsCompact K) (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (Ψ : TwoTimePhase d) {R : ℝ} (hR : R ≠ 0)
    (hΨ : ContDiffOn ℝ ∞ (jointPhase (normalizedTwoTimePhase R Ψ)) U)
    {Δ r : ℝ} (hr : r ∈ Icc 0 Δ) (hmap : MapsTo (elapsedPoint r) K J)
    (N k : ℕ) (hk : k ≤ N) (p : Euclidean (d + 1) × Euclidean (d + 1))
    (hp : phasePairInclusion p ∈ K) :
    ‖iteratedFDeriv ℝ k (Function.uncurry (normalizedPhase R (elapsedPhase Ψ r))) p‖ ≤
      phaseTimeConstant K N Δ + cNorm J N (jointPhase (normalizedTwoTimePhase R Ψ)) := by
  let S := normalizedTwoTimePhase R Ψ
  let f : Point (d + 1) → ℝ := fun v ↦ elapsedPhase S r v.1.1 v.2
  let W := elapsedPoint r ⁻¹' U
  have hW : IsOpen W := hU.preimage
    (elapsedLinear.continuous.add continuous_const)
  have hf : ContDiffOn ℝ ∞ f W := contDiffOn_jointElapsedPhase S hΨ r
  have hin : phasePairInclusion p + 0 ∈ W := by
    simpa only [add_zero] using (show phasePairInclusion p ∈ W from hJU (hmap hp))
  have hchain := norm_iteratedFDeriv_preAffine_le phasePairInclusion 0 hW hf hin k
  have hpow : ‖phasePairInclusion (d := d)‖ ^ k ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) norm_phasePairInclusion_le
  have hjet := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
    (fun v hv ↦ (hf.contDiffAt (hW.mem_nhds (hJU (hmap hv)))).of_le (by simp)) hp hk
  have hjet' : ‖iteratedFDeriv ℝ k (fun v ↦ f (phasePairInclusion v)) p‖ ≤ cNorm K N f := by
    simp only [add_zero] at hchain
    exact hchain.trans ((mul_le_mul_of_nonneg_left hpow (norm_nonneg _)).trans (by simpa using hjet))
  rw [normalizedPhase_elapsedPhase hR]
  exact hjet'.trans (cNorm_elapsedPhase_le hK hJ hU hJU S hΨ hr hmap N)

/-- The exact dyadic-shell phase reserve consumed by
`exists_fullGraphFamily_of_wholeImage_phase`. The fixed normalized chart
contains the inserted position/covector pairs of every shell. Original joint
normalized phase jets supply the analytic input, uniformly in elapsed time. -/
theorem wholeImagePhaseReserve_elapsedPhase
    {K : Set (Point (d + 1))} {J U : Set (TwoTimePoint d)}
    (hK : IsCompact K) (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (Ψ : TwoTimePhase d)
    (hΨ : ∀ j : ℕ, ContDiffOn ℝ ∞
      (jointPhase (normalizedTwoTimePhase ((2 : ℝ)^j) Ψ)) U)
    {Bφ Δ : ℝ}
    (hbudget : ∀ j : ℕ, cNorm J (wholeImagePhaseReserve (d + 1))
      (jointPhase (normalizedTwoTimePhase ((2 : ℝ)^j) Ψ)) ≤ Bφ)
    {X D : Set (Euclidean (d + 1))} (a b : ℝ)
    (hchart : ∀ j : ℕ, ∀ p ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
      phasePairInclusion p ∈ K)
    {r : ℝ} (hr : r ∈ Icc 0 Δ) (hmap : MapsTo (elapsedPoint r) K J) :
    ∀ j : ℕ, ∀ p ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
      ∀ k ≤ wholeImagePhaseReserve (d + 1),
      ‖iteratedFDeriv ℝ k (Function.uncurry
        (normalizedPhase ((2 : ℝ)^j) (elapsedPhase Ψ r))) p‖ ≤
        phaseTimeConstant K (wholeImagePhaseReserve (d + 1)) Δ + Bφ := by
  intro j p hp k hk
  exact (norm_iteratedFDeriv_normalizedElapsedPhase_le hK hJ hU hJU Ψ
    (pow_ne_zero _ (by norm_num)) (hΨ j) hr hmap _ k hk p (hchart j p hp)).trans
    (add_le_add le_rfl (hbudget j))

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
