module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.PhaseJets.Geometry
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.ParameterJets.Interchange
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.AffinePullback

/-!
# Restricting the full phase jets

Freezing the spectator and epsilon contracts the joint jets. The ordinary
epsilon derivative costs one more joint derivative, also at epsilon zero.
The consumer is the literal full-input budget of `app:ch_waves:setup:oscillatory`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.Sampling.FullNormalGeometry.PhaseJets
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualPhase
open RawKernel MeanNormalBound.CanonicalGap
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets

private theorem slice_jet_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {I : Set ℝ} {V : Set E} (hI : IsOpen I) (hV : IsOpen V)
    {f : ℝ × E → F} (hf : ContDiffOn ℝ ∞ f (I ×ˢ V))
    {ε : ℝ} (hε : ε ∈ I) {z : E} (hz : z ∈ V) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y ↦ f (ε, y)) z‖ ≤
      ‖iteratedFDeriv ℝ k f (ε, z)‖ := by
  let L := ContinuousLinearMap.inr ℝ ℝ E
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (by intro y; simp [L])
  have hh := norm_iteratedFDeriv_preAffine_le L (ε, 0) (hI.prod hV) hf
    (x := z) (by simpa [L] using And.intro hε hz) k
  have hh' := hh.trans
    (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL))
  simpa [L] using hh'

private theorem deriv_slice_jet_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {I : Set ℝ} {V : Set E} (hI : IsOpen I) (hV : IsOpen V)
    {f : ℝ × E → F} (hf : ContDiffOn ℝ ∞ f (I ×ˢ V))
    {ε : ℝ} (hε : ε ∈ I) {z : E} (hz : z ∈ V) (k : ℕ) :
    ‖deriv (fun t ↦ iteratedFDeriv ℝ k (fun y ↦ f (t, y)) z) ε‖ ≤
      ‖iteratedFDeriv ℝ (k + 1) f (ε, z)‖ := by
  rw [← NormalComparison.iteratedFDeriv_deriv_parameter hI hV hf hε hz k]
  let g : ℝ × E → F := fun q ↦ fderiv ℝ f q (1, 0)
  have hg : ContDiffOn ℝ ∞ g (I ×ˢ V) :=
    (hf.fderiv_of_isOpen (hI.prod hV) (m := ∞) (by simp)).clm_apply contDiffOn_const
  have heq : (fun y ↦ deriv (fun t ↦ f (t, y)) ε) =ᶠ[𝓝 z]
      (fun y ↦ g (ε, y)) := by
    filter_upwards [hV.mem_nhds hz] with y hy
    exact (((hf.contDiffAt ((hI.prod hV).mem_nhds ⟨hε, hy⟩)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt ε
        ((hasDerivAt_id ε).prodMk (hasDerivAt_const ε y))).deriv
  rw [(heq.iteratedFDeriv (𝕜 := ℝ) (n := k)).eq_of_nhds]
  apply (slice_jet_le hI hV hg hε hz k).trans
  have hd := (hf.contDiffAt ((hI.prod hV).mem_nhds
    (show (ε, z) ∈ I ×ˢ V from ⟨hε, hz⟩))).fderiv_right (m := ∞) (by simp)
  have hh := norm_iteratedFDeriv_clm_apply_const (c := ((1 : ℝ), (0 : E))) hd
    (by simp : (k : ℕ∞ω) ≤ ∞)
  simpa only [g, Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one,
    one_mul, norm_iteratedFDeriv_fderiv] using hh

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Freezing only the spectators preserves every epsilon/physical/full-input
jet. Incidence stays a differentiated variable
(`app:ch_waves:setup:oscillatory`). -/
theorem spectator_jet_le (Q : _) {M e ε : ℝ}
    (hs : ContDiffOn ℝ ∞ (literalJoint T Q) (Ioo (-e) e ×ˢ tripleDomain T M))
    (hε : ε ∈ Ioo (-e) e) {v : Euclidean 2}
    {w : Euclidean (m + 1) × Euclidean (m + 1)}
    (hw : w ∈ fullPhaseExtensionDomain T v M) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q : ℝ ×
        (Euclidean (m + 1) × Euclidean (m + 1)) ↦
        normalizedFullPhase T Q v q.1 q.2.1 (canonicalInputCoordinates T q.2.2)) (ε, w)‖ ≤
      ‖iteratedFDeriv ℝ k (literalJoint T Q) (ε, v, w)‖ := by
  let L : (ℝ × (Euclidean (m + 1) × Euclidean (m + 1))) →L[ℝ]
      (ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))) :=
    (ContinuousLinearMap.fst ℝ _ _).prod
      ((0 : (ℝ × (Euclidean (m + 1) × Euclidean (m + 1))) →L[ℝ] Euclidean 2).prod
        (ContinuousLinearMap.snd ℝ _ _))
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro q
    simp [L, Prod.norm_def]
  have hh := norm_iteratedFDeriv_preAffine_le L (0, v, 0)
    (isOpen_Ioo.prod (isOpen_tripleDomain T M)) hs
    (x := (ε, w)) (by simpa [L, tripleDomain] using And.intro hε hw) k
  have hh' := hh.trans
    (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL))
  simpa [L, literalJoint] using hh'

/-- Joint orders `k` and `k+1` bound exactly the two literal phase terms in
`UniformNormalData.input_jets`, using the open extension at both endpoints
(`app:ch_waves:setup:oscillatory`, `app:ch_seed:eq:seed-phase-tame`). -/
theorem inputJets_le_joint (Q : _) {M e ε : ℝ}
    (hs : ContDiffOn ℝ ∞ (literalJoint T Q) (Ioo (-e) e ×ˢ tripleDomain T M))
    (hε : ε ∈ Ioo (-e) e) {v : Euclidean 2}
    {w : Euclidean (m + 1) × Euclidean (m + 1)}
    (hw : w ∈ fullPhaseExtensionDomain T v M) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (Function.uncurry (fun x u ↦
        normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u))) w‖ +
      ‖deriv (fun t ↦ iteratedFDeriv ℝ k (Function.uncurry (fun x u ↦
        normalizedFullPhase T Q v t x (canonicalInputCoordinates T u))) w) ε‖ ≤
      ‖iteratedFDeriv ℝ k (literalJoint T Q) (ε, v, w)‖ +
        ‖iteratedFDeriv ℝ (k + 1) (literalJoint T Q) (ε, v, w)‖ := by
  have hf : ContDiffOn ℝ ∞ (fun q : ℝ ×
      (Euclidean (m + 1) × Euclidean (m + 1)) ↦
      normalizedFullPhase T Q v q.1 q.2.1 (canonicalInputCoordinates T q.2.2))
      (Ioo (-e) e ×ˢ fullPhaseExtensionDomain T v M) :=
    hs.comp (f := fun q : ℝ × (Euclidean (m + 1) × Euclidean (m + 1)) ↦
      (q.1, v, q.2)) (by fun_prop) (fun q hq ↦ hq)
  exact add_le_add
    ((slice_jet_le isOpen_Ioo (isOpen_fullPhaseExtensionDomain T v M) hf hε hw k).trans
      (spectator_jet_le T Q hs hε hw k))
    ((deriv_slice_jet_le isOpen_Ioo (isOpen_fullPhaseExtensionDomain T v M) hf hε hw k).trans
      (spectator_jet_le T Q hs hε hw (k + 1)))

end JanetCartan.Sampling.FullNormalGeometry.PhaseJets
