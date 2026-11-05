module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.CoefficientBounds.Principal
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Reconstruction.Field

/-!
# The literal null-transport potential as a finite jet formula

The consumer is the potential estimate in `app:ch_waves:eq:joint-tame`.
The formula retains the full symmetrized covariant derivative, including the
induced Christoffel coefficients. Its inputs use joint physical/carrier
Fréchet derivatives and the original Euclidean/Frobenius norms.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NullTransport.CoefficientBounds
open ProjectedStressFrame GeometricProfile

variable {n N : ℕ}

/-- Value input, joint nullvector derivative and immersion second jet for
`app:ch_waves:thm:leading`. -/
abbrev PotentialJet (n N : ℕ) := Input n ×
  (((Euclidean n × Euclidean 3) →L[ℝ] Euclidean n) × StressJet n N)

/-- The literal normalized potential, with every connection term retained
(`app:ch_waves:thm:leading`). -/
def potentialFormula (ν : Euclidean n) (r c : Fin n) (p : PotentialJet n N) : ℝ :=
  (∑ i, left r p.1 i * ∑ a, ∑ b, p.1.1 i a b *
    (((p.2.1 (EuclideanSpace.single a 1, 0)) b +
      (p.2.1 (EuclideanSpace.single b 1, 0)) a) / 2 -
      ∑ j, secondJetChristoffel p.2.2 a b j * right c p.1 j)) /
    denominator ν r c p.1

/-- The actual metric gap makes the matrix inverse in the connection smooth
(`app:ch_waves:eq:joint-tame`). -/
theorem firstJetMetric_isUnit_of_gap {J : StressJet n N} {κ : ℝ} (hκ : 0 < κ)
    (hgap : ∀ v, κ * ‖v‖ ^ 2 ≤ ‖J.1 v‖ ^ 2) : IsUnit (firstJetMetric J.1) := by
  apply firstJetMetric_isUnit_of_injective
  apply (injective_iff_map_eq_zero J.1).mpr
  intro v hv
  have h := hgap v
  rw [hv, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
  have hz : ‖v‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖v‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

/-- Smoothness of the fixed potential formula on the two primitive gap loci
(`app:ch_waves:eq:joint-tame`). -/
theorem smoothAt_potentialFormula (ν : Euclidean n) (r c : Fin n)
    {p : PotentialJet n N} (hmet : IsUnit (firstJetMetric p.2.2.1))
    (hden : denominator ν r c p.1 ≠ 0) :
    ContDiffAt ℝ ∞ (potentialFormula ν r c) p := by
  have hl (i : Fin n) : ContDiffAt ℝ ∞ (fun q : PotentialJet n N ↦ left r q.1 i) p :=
    (contDiffAt_pi.mp (smooth_left r).contDiffAt i).comp p contDiffAt_fst
  have hq (i a b : Fin n) :
      ContDiffAt ℝ ∞ (fun q : PotentialJet n N ↦ q.1.1 i a b) p :=
    (Matrix.entryLinearMap ℝ ℝ a b).toContinuousLinearMap.contDiff.contDiffAt.comp p
      (contDiffAt_pi.mp contDiffAt_fst.fst i)
  have hd (a b : Fin n) : ContDiffAt ℝ ∞ (fun q : PotentialJet n N ↦
      (q.2.1 (EuclideanSpace.single a 1, 0)) b) p :=
    (EuclideanSpace.proj (𝕜 := ℝ) b).contDiff.contDiffAt.comp p
      (contDiffAt_snd.fst.clm_apply contDiffAt_const)
  have hk (j : Fin n) : ContDiffAt ℝ ∞ (fun q : PotentialJet n N ↦ right c q.1 j) p :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt.comp p
      ((smooth_right c).contDiffAt.comp p contDiffAt_fst)
  have hchr (a b j : Fin n) : ContDiffAt ℝ ∞
      (fun q : PotentialJet n N ↦ secondJetChristoffel q.2.2 a b j) p := by
    exact ContDiffAt.comp (f := fun q : PotentialJet n N ↦ q.2.2)
      (g := fun J : StressJet n N ↦ secondJetChristoffel J a b j) p
      (contDiffAt_secondJetChristoffel (J := p.2.2) hmet a b j) contDiffAt_snd.snd
  apply ContDiffAt.div _ ((smooth_denominator ν r c).contDiffAt.comp p contDiffAt_fst) hden
  exact ContDiffAt.sum fun i _ ↦ (hl i).mul (ContDiffAt.sum fun a _ ↦
    ContDiffAt.sum fun b _ ↦ (hq i a b).mul
      (((hd a b).add (hd b a) |>.div_const 2).sub (ContDiffAt.sum fun j _ ↦
        (hchr a b j).mul (hk j))))

/-- Local identification of the second-jet connection; global smoothness
is unnecessary on the working patch (`app:ch_waves:thm:leading`). -/
theorem secondJetChristoffel_eq_at {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hF : ContDiffAt ℝ ∞ F x) (i j k : Fin n) :
    secondJetChristoffel (stressJet F x) i j k = christoffel F x i j k := by
  rw [christoffel_eq_hessian_contraction (hF.of_le (by simp : (2 : ℕ∞ω) ≤ ∞))]
  unfold secondJetChristoffel stressJet partialDeriv
  have hd := hF.fderiv_right (show ∞ + 1 ≤ ∞ by simp)
  rw [fderiv_clm_apply (hd.differentiableAt (by simp)) (differentiableAt_const _)]
  simp
  rfl

/-- The physical scalar derivative is the corresponding evaluation of the
joint derivative (`app:ch_waves:eq:joint-tame`). -/
theorem physical_partial_eq_joint {k : Euclidean n × Euclidean 3 → Euclidean n}
    {w : Euclidean n × Euclidean 3} (hk : DifferentiableAt ℝ k w) (a b : Fin n) :
    partialDeriv (fun x ↦ k (x, w.2) b) w.1 a =
      (fderiv ℝ k w (EuclideanSpace.single a 1, 0)) b := by
  have he : HasFDerivAt (fun x : Euclidean n ↦ (x, w.2))
      ((ContinuousLinearMap.id ℝ (Euclidean n)).prod 0) w.1 :=
    (hasFDerivAt_id w.1).prodMk (hasFDerivAt_const w.2 w.1)
  have hd := (EuclideanSpace.proj (𝕜 := ℝ) b).hasFDerivAt.comp w.1
    (hk.hasFDerivAt.comp w.1 he)
  change HasFDerivAt (fun x ↦ k (x, w.2) b) _ w.1 at hd
  rw [partialDeriv, hd.fderiv]
  rfl

open ActualCarriers FrozenMenu CurrentFullPhase

/-- Identification with the literal potential of the same carrier and chart,
including every Christoffel term (`app:ch_waves:thm:leading`). -/
theorem potentialFormula_actual {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    (Q : _) {F : Euclidean n → Euclidean N} (hF : ContDiffOn ℝ ∞ F U)
    (r c : Fin n) {w : Euclidean n × Euclidean 3} (hw : w ∈ inputDomain T) :
    potentialFormula T.data.adapted.normal r c
      (actualInput T Q w, fderiv ℝ (carrierNullvector T Q c) w, stressJet F w.1) =
      carrierTransportPotential T Q F r c w := by
  have hk : DifferentiableAt ℝ (carrierNullvector T Q c) w :=
    ((smooth_right c).comp_contDiffOn (smooth_actualInput T hP Q)).contDiffAt
      ((isOpen_inputDomain T).mem_nhds hw) |>.differentiableAt (by simp)
  have hp := physical_partial_eq_joint hk
  simp only [potentialFormula, carrierTransportPotential, reducedOperator, tensorPairing,
    symmCovariantDeriv, dotProduct, hp,
    ← secondJetChristoffel_eq_at (hF.contDiffAt (hU.mem_nhds hw.1.1))]
  rfl

end JanetCartan.NullTransport.CoefficientBounds
