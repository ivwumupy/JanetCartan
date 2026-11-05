module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets.Rescaling
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets.Homogeneity
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.FrequencyBounds.ConicJets

/-!
# Frozen linear dilations for normalized inverse jets

These estimates transfer common-ball inverse jets to the supported conic shell.
The dilation is held fixed during differentiation, including the two positions
and spectator. Consumer: `exists_normalJetRescaling_normalizedPull_bound`.
Sources: `app:ch_background:eq:bg-Psi`, `bg-full-complex-amplitude`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
open ContinuumRow DerivativeKernels ModifiedNormalSymbol
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open CanonicalConic ContinuumNormalReduction.TransportSymbol

variable {n : ℕ}

/-- Output frequency dilation retaining both positions and the spectator,
used at the fixed supported shell (`app:ch_background:eq:bg-Psi`). -/
def jointOutputCovectorDilation (t : ℝ) (ht : t ≠ 0) :
    JointVariables n ≃L[ℝ] JointVariables n :=
  (frequencyDilationEquiv t ht).prodCongr (ContinuousLinearEquiv.refl ℝ (Euclidean 2))

/-- The input dilation has a dimension-independent operator bound, including
its unscaled coordinates (`app:ch_background:eq:bg-Psi`). -/
theorem inputCovectorDilation_norm_le {t : ℝ} (ht : 0 < t) :
    ‖(inputCovectorDilation (n := n) t ht.ne').toContinuousLinearMap‖ ≤ 1 + t := by
  refine (inputCovectorDilation (n := n) t ht.ne').toContinuousLinearMap.opNorm_le_bound
    (by positivity) ?_
  intro p
  have hp : ‖p‖ ≤ (1 + t) * ‖p‖ := by nlinarith [norm_nonneg p]
  have hη := mul_le_mul_of_nonneg_left
    ((norm_snd_le p.2).trans (norm_snd_le p)) ht.le
  have hη' : t * ‖p.2.2‖ ≤ (1 + t) * ‖p‖ := by nlinarith [norm_nonneg p]
  change ‖scaleInput t p‖ ≤ _
  simp only [scaleInput, Prod.norm_def, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  exact max_le ((norm_fst_le p).trans hp)
    (max_le (((norm_fst_le p.2).trans (norm_snd_le p)).trans hp)
      hη')

/-- The joint output dilation bounds full joint jets, not just covector
jets (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem jointOutputCovectorDilation_norm_le {t : ℝ} (ht : 0 < t) :
    ‖(jointOutputCovectorDilation (n := n) t ht.ne').toContinuousLinearMap‖ ≤ 1 + t := by
  refine (jointOutputCovectorDilation (n := n) t ht.ne').toContinuousLinearMap.opNorm_le_bound
    (by positivity) ?_
  intro p
  have hp : ‖p‖ ≤ (1 + t) * ‖p‖ := by nlinarith [norm_nonneg p]
  have hη := mul_le_mul_of_nonneg_left
    (((norm_snd_le p.1.2).trans (norm_snd_le p.1)).trans (norm_fst_le p)) ht.le
  have hη' : t * ‖p.1.2.2‖ ≤ (1 + t) * ‖p‖ := by nlinarith [norm_nonneg p]
  change ‖((p.1.1, p.1.2.1, t • p.1.2.2), p.2)‖ ≤ _
  simp only [Prod.norm_def, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  exact max_le (max_le (((norm_fst_le p.1).trans (norm_fst_le p)).trans hp)
    (max_le ((((norm_fst_le p.1.2).trans (norm_snd_le p.1)).trans
      (norm_fst_le p)).trans hp) hη'))
    ((norm_snd_le p).trans hp)

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r aOuter aPhase : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r)
    {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ aOuter)
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ aOuter,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)

include hηb hr hInv htrans in
/-- Freeze the positive shell dilation before differentiating the SAME
normalized inverse (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalJetRescaling_normalizedPull_eq_shell
    {p : JointVariables n} (hp : p ∈ symbolDomain T Q z₀ ηb r aOuter)
    {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    (normalJetRescaling T Q z₀ ηb r aOuter aPhase).normalizedPull R p =
      (jointInputCoordinates T).symm
        (scaleInput (R * t)⁻¹ (inverseCoordinates (symbolInverse T Q z₀ ηb r aOuter)
          (jointOutputCovectorDilation t ht.ne' p))) := by
  rw [normalJetRescaling_normalizedPull T Q z₀ ηb r aOuter aPhase hR]
  change (jointInputCoordinates T).symm (scaleInput R⁻¹
      (inverseCoordinates (symbolInverse T Q z₀ ηb r aOuter) p)) =
    (jointInputCoordinates T).symm (scaleInput (R * t)⁻¹
      (inverseCoordinates (symbolInverse T Q z₀ ηb r aOuter) (scaleFrequency t p.1, p.2)))
  simp only [inverseCoordinates]
  rw [symbolInverse_smul T Q hηb hr hInv htrans hp ht]
  simp only [scaleInput, scaleFrequency, mul_inv_rev, smul_smul]
  congr 3
  field_simp

include hηb hr hInv htrans in
/-- Full joint inverse jets transfer through the frozen shell dilation.
The unnormalized derivative is evaluated at the scaled output; this lemma
assumes no derivative bound (`app:ch_background:eq:bg-Psi`). -/
theorem norm_iteratedFDeriv_normalizedPull_le_shell
    (hV : IsOpen V) (hLV : L ⊆ V)
    {p : JointVariables n} (hp : p ∈ symbolDomain T Q z₀ ηb r aOuter)
    {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (j : ℕ) :
    ‖iteratedFDeriv ℝ j
      ((normalJetRescaling T Q z₀ ηb r aOuter aPhase).normalizedPull R) p‖ ≤
      (‖(jointInputCoordinates T).symm.toContinuousLinearMap‖ * (1 + (R * t)⁻¹)) *
        (‖iteratedFDeriv ℝ j (inverseCoordinates (symbolInverse T Q z₀ ηb r aOuter))
          (jointOutputCovectorDilation t ht.ne' p)‖ * (1 + t) ^ j) := by
  let D := jointOutputCovectorDilation (n := n) t ht.ne'
  let H := (jointInputCoordinates T).symm.toContinuousLinearMap.comp
    (inputCovectorDilation (n := n) (R * t)⁻¹ (inv_pos.mpr (mul_pos hR ht)).ne').toContinuousLinearMap
  let f := inverseCoordinates (symbolInverse T Q z₀ ηb r aOuter)
  have hΩ := symbolDomain_open T Q hηb hr hInv htrans hV hLV
  have hf := inverseCoordinates_contDiffOn (symbolInverse_smooth T Q hηb hr hInv htrans hLV)
  have hDp : D p ∈ symbolDomain T Q z₀ ηb r aOuter :=
    (symbolDomain_smul_iff T Q ht p).mpr hp
  have he : (normalJetRescaling T Q z₀ ηb r aOuter aPhase).normalizedPull R =ᶠ[𝓝 p]
      H ∘ (f ∘ D) := (hΩ.eventually_mem hp).mono fun q hq ↦
    normalJetRescaling_normalizedPull_eq_shell T Q hηb hr hInv htrans hq hR ht
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  have hcomp : ContDiffAt ℝ ∞ (f ∘ D) p :=
    (hf.contDiffAt (hΩ.mem_nhds hDp)).comp p D.contDiff.contDiffAt
  have hright := NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le
    D.toContinuousLinearMap hΩ hf hDp j
  have hH : ‖H‖ ≤ ‖(jointInputCoordinates T).symm.toContinuousLinearMap‖ * (1 + (R * t)⁻¹) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (inputCovectorDilation_norm_le (inv_pos.mpr (mul_pos hR ht)))
        (norm_nonneg _))
  exact (H.norm_iteratedFDeriv_comp_left hcomp (by simp)).trans
    (mul_le_mul hH (hright.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (jointOutputCovectorDilation_norm_le ht) j)
      (norm_nonneg _))) (norm_nonneg _) (by positivity))

end JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
