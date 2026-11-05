module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.Defect
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.NormalizedSymbolBounds.Basic
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SymbolStability
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Carriers
public import JanetCartan.Analysis.ContDiff.Norm.Composition

/-!
# Uniform annular bounds for the actual Hamilton field

The covector Lipschitz estimate used by the protected graph transport is
derived from the literal normalized determinant.  The coefficient range and
all of its low jets are fixed before the coefficient field; no Lipschitz
property of a coefficient-function class is assumed (`app:ch_regular:thm:no-return`).
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open ActualCarriers ActualCarriers.NormalizedSymbol
open ActualCarriers.NormalizedSymbolBounds HamiltonPhase
open JanetCartan.FiniteChain.Graph.PhysicalShells
open JanetCartan.CompositionBounds

variable {n : ℕ}

private theorem cNorm_lifted_coeff_le
    {R : ℝ} {s : Set (Euclidean n × Euclidean n)}
    (hS : IsCompact s) (hs : ∀ z ∈ s, z.1 ∈ closedBall (0 : Euclidean n) R)
    {Q : Euclidean n → Fin n → MetricTensor n} (hQ : ContDiff ℝ ∞ Q) (r : ℕ) :
    cNorm s r
        (fun z : Euclidean n × Euclidean n ↦ (Q z.1, z.2)) ≤
      (r + 1 : ℝ) *
        (cNorm (closedBall (0 : Euclidean n) R) r Q +
          cNorm s r
            (Prod.snd : Euclidean n × Euclidean n → Euclidean n)) := by
  let L := ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n)
  have hb := cNorm_le_sum (s := s) (r := r)
    (f := fun z : Euclidean n × Euclidean n ↦ (Q z.1, z.2))
    (B := fun _ ↦ cNorm (closedBall (0 : Euclidean n) R) r Q +
      cNorm s r (Prod.snd : Euclidean n × Euclidean n → Euclidean n))
    (fun _ _ ↦ add_nonneg (cNorm_nonneg ..) (cNorm_nonneg ..)) ?_
  · simpa [mul_add] using hb
  intro j hj z hz
  have hQfst : ContDiff ℝ ∞ (fun z : Euclidean n × Euclidean n ↦ Q z.1) :=
    hQ.comp contDiff_fst
  rw [iteratedFDeriv_prodMk hQfst.contDiffAt
    contDiff_snd.contDiffAt (by simp : (j : ℕ∞ω) ≤ ∞),
    ContinuousMultilinearMap.opNorm_prod]
  have hfst : ‖iteratedFDeriv ℝ j (fun z : Euclidean n × Euclidean n ↦ Q z.1) z‖ ≤
      cNorm (closedBall (0 : Euclidean n) R) r Q := by
    change ‖iteratedFDeriv ℝ j (Q ∘ L) z‖ ≤ _
    rw [L.iteratedFDeriv_comp_right hQ z (by simp)]
    apply ((iteratedFDeriv ℝ j Q (L z)).norm_compContinuousLinearMap_le (fun _ ↦ L)).trans
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc
      _ ≤ ‖iteratedFDeriv ℝ j Q (L z)‖ * 1 :=
        mul_le_mul_of_nonneg_left (by
          simpa using (pow_le_pow_left₀ (norm_nonneg L)
            (ContinuousLinearMap.norm_fst_le ℝ (Euclidean n) (Euclidean n)) j))
          (norm_nonneg _)
      _ ≤ _ := by
        rw [mul_one]
        exact norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _)
          (hQ.of_le (by simp)) (hs z hz) hj
  have hsnd := norm_iteratedFDeriv_le_cNorm hS
    (show ContDiff ℝ r (Prod.snd : Euclidean n × Euclidean n → Euclidean n) from
      contDiff_snd.of_le (by simp : (r : ℕ∞ω) ≤ ∞)) hz hj
  exact max_le (hfst.trans (le_add_of_nonneg_right (cNorm_nonneg ..)))
    (hsnd.trans (le_add_of_nonneg_left (cNorm_nonneg ..)))

/-- Uniform covector Lipschitz control for the actual normalized Hamilton field.
The constant is chosen from `n`, the physical radius, the coefficient budget,
and the fixed annulus before the coefficient field (`app:ch_regular:thm:no-return`). -/
theorem exists_uniform_normalizedHomogeneousSymbol_vectorField_covector_lipschitz
    (R : ℝ) (_hR : 0 < R) (M : ℝ) (hM : 0 ≤ M)
    {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) :
    ∃ V ≥ 0, ∀ (Q : Euclidean n → Fin n → MetricTensor n)
      (hQ : ContDiff ℝ ∞ Q), cNorm (closedBall 0 R) 3 Q ≤ M →
      ∀ x ∈ closedBall 0 R, ∀ v ∈ frequencyAnnulus a b,
        ∀ w ∈ frequencyAnnulus a b,
          ‖(normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn).vectorField (x, v) -
              (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn).vectorField (x, w)‖ ≤
            V * ‖v - w‖ := by
  let A : Set (Euclidean n) := frequencyAnnulus (a / 2) b
  let S : Set (Euclidean n × Euclidean n) := closedBall 0 R ×ˢ A
  let T : Set (Fin n → MetricTensor n) := closedBall 0 M
  have ha2 : 0 < a / 2 := by linarith
  have hA : IsCompact A := by
    dsimp [A]
    exact isCompact_frequencyAnnulus _ _
  have hS : IsCompact S := (isCompact_closedBall (0 : Euclidean n) R).prod hA
  have hT : IsCompact T := isCompact_closedBall _ _
  have hA0 : ∀ ξ ∈ A, ξ ≠ 0 := by
    intro ξ hξ hzero
    have hξa : a / 2 ≤ ‖ξ‖ := hξ.1
    rw [hzero, norm_zero] at hξa
    linarith
  obtain ⟨Cjet, hCjet, hjet⟩ :=
    exists_bound_coefficient_jets (T := T) (A := A) hT hA hA0 3
  let g0 : ((Fin n → MetricTensor n) × Euclidean n) → ℝ :=
    fun p ↦ determinant p.1 p.2 * ‖p.2‖ ^ (1 - (n : ℤ))
  have hQval {Q : Euclidean n → Fin n → MetricTensor n}
      (hQ : ContDiff ℝ ∞ Q) (hQnorm : cNorm (closedBall 0 R) 3 Q ≤ M)
      {x : Euclidean n} (hx : x ∈ closedBall 0 R) :
      Q x ∈ closedBall (0 : Fin n → MetricTensor n) M := by
    have hb := norm_iteratedFDeriv_le_cNorm (isCompact_closedBall (0 : Euclidean n) R)
      (hQ.of_le (by simp : (3 : ℕ∞ω) ≤ ∞)) hx (j := 0) (by omega)
    rw [norm_iteratedFDeriv_zero] at hb
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hb.trans hQnorm
  have hF : ∀ (Q : Euclidean n → Fin n → MetricTensor n), ContDiff ℝ ∞ Q →
      ContDiff ℝ ∞ (fun z : Euclidean n × Euclidean n ↦ (Q z.1, z.2)) := by
    intro Q hQ
    exact (hQ.comp contDiff_fst).prodMk contDiff_snd
  have hinner {Q : Euclidean n → Fin n → MetricTensor n} (hQ : ContDiff ℝ ∞ Q)
      (hQnorm : cNorm (closedBall 0 R) 3 Q ≤ M) :
      cNorm S 3 (fun z : Euclidean n × Euclidean n ↦ (Q z.1, z.2)) ≤
        (4 : ℝ) * (cNorm (closedBall (0 : Euclidean n) R) 3 Q +
          cNorm S 3 (Prod.snd : Euclidean n × Euclidean n → Euclidean n)) := by
    exact (cNorm_lifted_coeff_le hS (fun z hz ↦ hz.1) hQ 3).trans_eq (by norm_num)
  have hsymbol {Q : Euclidean n → Fin n → MetricTensor n} (hQ : ContDiff ℝ ∞ Q)
      (hQnorm : cNorm (closedBall 0 R) 3 Q ≤ M) :
      cNorm S 3 (normalizedSymbol Q) ≤
        compositionMultiplicity 3 * Cjet *
          (1 + cNorm S 3 (fun z : Euclidean n × Euclidean n ↦ (Q z.1, z.2))) ^ 3 := by
    have hcomp := cNorm_comp_le_polynomial (s := S) (r := 3)
      (f := fun z : Euclidean n × Euclidean n ↦ (Q z.1, z.2)) (g := g0)
      (fun z hz ↦ (hF Q hQ).contDiffAt.of_le (by simp : (3 : ℕ∞ω) ≤ ∞))
      (fun z hz ↦ (contDiffAt_determinant_norm_zpow
        (hA0 z.2 hz.2)).of_le (by simp))
      (fun j hj ↦ bddAbove_derivative_image hS
        ((hF Q hQ).of_le (by simp : (3 : ℕ∞ω) ≤ ∞)) hj)
      (by positivity)
      (fun j hj z hz ↦ hjet j hj (Q z.1) (hQval hQ hQnorm hz.1) z.2 hz.2)
    change cNorm S 3
      (fun z : Euclidean n × Euclidean n ↦
        determinant (Q z.1) z.2 * ‖z.2‖ ^ (1 - (n : ℤ))) ≤ _
    simpa [g0, Function.comp_def] using hcomp
  let Snd := cNorm S 3 (Prod.snd : Euclidean n × Euclidean n → Euclidean n)
  let Ainner : ℝ := 1 + 4 * (M + Snd)
  let B : ℝ := compositionMultiplicity 3 * Cjet * Ainner ^ 3
  let V : ℝ := max B (4 * B / a)
  have hSnd : 0 ≤ Snd := cNorm_nonneg _ _ _
  have hAinner : 0 ≤ Ainner := by
    dsimp [Ainner]
    positivity
  have hAinner1 : 1 ≤ Ainner := by
    dsimp [Ainner]
    linarith [hM, hSnd]
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (by
      dsimp [compositionMultiplicity]
      exact Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)) hCjet.le)
      (pow_nonneg hAinner 3)
  have hmult : 0 ≤ compositionMultiplicity 3 := by
    dsimp [compositionMultiplicity]
    exact Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)
  have hV : 0 ≤ V := by
    dsimp [V]
    exact hB.trans (le_max_left _ _)
  have hBsymbol {Q : Euclidean n → Fin n → MetricTensor n}
      (hQ : ContDiff ℝ ∞ Q) (hQnorm : cNorm (closedBall 0 R) 3 Q ≤ M) :
      cNorm S 3 (normalizedSymbol Q) ≤ B := by
    have hi := hinner hQ hQnorm
    have hs := hsymbol hQ hQnorm
    calc
      _ ≤ compositionMultiplicity 3 * Cjet * Ainner ^ 3 := by
        apply hs.trans
        have hbase : 1 + cNorm S 3
            (fun z : Euclidean n × Euclidean n ↦ (Q z.1, z.2)) ≤ Ainner := by
          dsimp [Ainner]
          linarith [hi, hQnorm]
        have hpow : (1 + cNorm S 3
            (fun z : Euclidean n × Euclidean n ↦ (Q z.1, z.2))) ^ 3 ≤ Ainner ^ 3 :=
          pow_le_pow_left₀ (by
            linarith [cNorm_nonneg S 3
              (fun z : Euclidean n × Euclidean n ↦ (Q z.1, z.2))]) hbase 3
        exact mul_le_mul_of_nonneg_left hpow
          (mul_nonneg hmult hCjet.le)
      _ = B := rfl
  refine ⟨V, hV, ?_⟩
  intro Q hQ hQnorm x hx v hv w hw
  let H := normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn
  let H0 : HomogeneousSymbol (Euclidean n) := {
    domain := normalizedSymbolDomain (Set.univ : Set (Euclidean n))
    isOpen_domain := isOpen_normalizedSymbolDomain isOpen_univ
    h := fun _ ↦ 0
    hx := fun _ ↦ 0
    hp := fun _ ↦ 0
    hpDerivative := fun _ ↦ 0
    hasFDerivAt_h := by
      intro z hz
      simpa [hamiltonDifferential] using (hasFDerivAt_const (0 : ℝ) z)
    hasFDerivAt_hp := by
      intro z hz
      simpa using (hasFDerivAt_const (0 : Euclidean n) z)
    homogeneous := by
      intro z hz
      exact Filter.Eventually.of_forall (fun r ↦ by simp)
  }
  have hD : IsOpen (normalizedSymbolDomain (Set.univ : Set (Euclidean n))) :=
    isOpen_normalizedSymbolDomain isOpen_univ
  have hDsub : S ⊆ normalizedSymbolDomain (Set.univ : Set (Euclidean n)) := by
    intro z hz
    exact ⟨mem_univ _, hA0 z.2 hz.2⟩
  have hH3 : ContDiffOn ℝ 3 H.h H.domain := by
    change ContDiffOn ℝ 3 (normalizedSymbol Q) (normalizedSymbolDomain (Set.univ : Set (Euclidean n)))
    exact (contDiffOn_normalizedSymbol (n := n) isOpen_univ hQ.contDiffOn).of_le
      (by simp : (3 : ℕ∞ω) ≤ ∞)
  have hH03 : ContDiffOn ℝ 3 H0.h H0.domain := by
    simpa [H0] using
      (contDiffOn_const : ContDiffOn ℝ 3 (fun _ : Euclidean n × Euclidean n ↦ (0 : ℝ)) _)
  have hHdom : normalizedSymbolDomain (Set.univ : Set (Euclidean n)) ⊆ H.domain := by
    intro z hz
    exact hz
  have hdiffsub : (fun z : Euclidean n × Euclidean n ↦ H.h z - H0.h z) =
      normalizedSymbol Q := by
    funext z
    change normalizedSymbol Q z - 0 = normalizedSymbol Q z
    simp
  have hzeroField : H0.vectorField =
      (fun _ : Euclidean n × Euclidean n ↦ (0 : Euclidean n × Euclidean n)) := by
    funext z
    simp [H0, HomogeneousSymbol.vectorField]
  have hfd {z : Euclidean n × Euclidean n} (hz : z ∈ S) :
      ‖fderiv ℝ H.vectorField z‖ ≤ B := by
    have hb := norm_fderiv_vectorField_sub_le_cNorm_three H H0 hD hHdom hHdom
      hH3 hH03 hS hDsub hz
    have hsB := hBsymbol hQ hQnorm
    have hb' : ‖fderiv ℝ H.vectorField z - fderiv ℝ H0.vectorField z‖ ≤
        cNorm S 3 (normalizedSymbol Q) := by
      simpa [hdiffsub] using hb
    have hz0 : fderiv ℝ H0.vectorField z = 0 := by
      rw [hzeroField]
      simp
    calc
      ‖fderiv ℝ H.vectorField z‖ =
          ‖fderiv ℝ H.vectorField z - 0‖ := by rw [sub_zero]
      _ = ‖fderiv ℝ H.vectorField z - fderiv ℝ H0.vectorField z‖ := by rw [hz0]
      _ ≤ B := hb'.trans hsB
  have hval {z : Euclidean n × Euclidean n} (hz : z ∈ S) :
      ‖H.vectorField z‖ ≤ B := by
    have hb := norm_vectorField_sub_le_cNorm_three H H0 hD hHdom hHdom
      hH3 hH03 hS hDsub hz
    have hsB := hBsymbol hQ hQnorm
    have hb' : ‖H.vectorField z - H0.vectorField z‖ ≤
        cNorm S 3 (normalizedSymbol Q) := by
      simpa [hdiffsub] using hb
    calc
      ‖H.vectorField z‖ = ‖H.vectorField z - 0‖ := by rw [sub_zero]
      _ = ‖H.vectorField z - H0.vectorField z‖ := by rw [hzeroField]
      _ ≤ B := hb'.trans hsB
  have hvA : v ∈ A := ⟨by linarith [hv.1, ha], hv.2⟩
  have hwA : w ∈ A := ⟨by linarith [hw.1, ha], hw.2⟩
  have hvS : (x, v) ∈ S := ⟨hx, hvA⟩
  have hwS : (x, w) ∈ S := ⟨hx, hwA⟩
  by_cases hfar : a / 2 ≤ ‖v - w‖
  · have htriangle := norm_sub_le (H.vectorField (x, v)) (H.vectorField (x, w))
    have hsum : ‖H.vectorField (x, v)‖ + ‖H.vectorField (x, w)‖ ≤ B + B :=
      add_le_add (hval hvS) (hval hwS)
    have hfactor : 0 ≤ 4 * B / a := by positivity
    have hscale : 2 * B ≤ (4 * B / a) * ‖v - w‖ := by
      have heq : (2 : ℝ) * B = (4 * B / a) * (a / 2) := by
        field_simp
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hfar hfactor
    calc
      ‖H.vectorField (x, v) - H.vectorField (x, w)‖ ≤
          ‖H.vectorField (x, v)‖ + ‖H.vectorField (x, w)‖ := htriangle
      _ ≤ 2 * B := by linarith
      _ ≤ (4 * B / a) * ‖v - w‖ := hscale
      _ ≤ V * ‖v - w‖ := by
        apply mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  · have hclose : ‖v - w‖ < a / 2 := lt_of_not_ge hfar
    let ξ : ℝ → Euclidean n := fun t ↦ (1 - t) • v + t • w
    let F : ℝ → Euclidean n × Euclidean n := fun t ↦ H.vectorField (x, ξ t)
    have hξmem : ∀ t ∈ Icc (0 : ℝ) 1, ξ t ∈ A := by
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have hupper : ‖ξ t‖ ≤ b := by
        calc
          ‖ξ t‖ ≤ ‖(1 - t) • v‖ + ‖t • w‖ := by
            exact norm_add_le _ _
          _ = (1 - t) * ‖v‖ + t * ‖w‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg ht0, abs_of_nonneg (by linarith)]
          _ ≤ b := by
            have h1 : (1 - t) * ‖v‖ ≤ (1 - t) * b :=
              mul_le_mul_of_nonneg_left hv.2 (by linarith)
            have h2 : t * ‖w‖ ≤ t * b :=
              mul_le_mul_of_nonneg_left hw.2 ht0
            calc
              _ ≤ (1 - t) * b + t * b := add_le_add h1 h2
              _ = b := by ring
      have hsub : v - ξ t = t • (v - w) := by
        dsimp [ξ]
        module
      have hnormsub : ‖v - ξ t‖ ≤ ‖v - w‖ := by
        rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
        simpa [mul_comm] using (mul_le_of_le_one_right (norm_nonneg (v - w)) ht1)
      have hlower : a / 2 ≤ ‖ξ t‖ := by
        have htri := norm_sub_norm_le v (ξ t)
        have hva : a ≤ ‖v‖ := hv.1
        linarith
      exact ⟨hlower, hupper⟩
    have hξdom : ∀ t ∈ Icc (0 : ℝ) 1, (x, ξ t) ∈ H.domain := by
      intro t ht
      exact hDsub ⟨hx, hξmem t ht⟩
    have hpath : ∀ t : ℝ, HasDerivAt (fun s ↦ (x, ξ s)) (0, w - v) t := by
      intro t
      have hξder : HasDerivAt ξ (w - v) t := by
        dsimp [ξ]
        have hleft : HasDerivAt (fun s : ℝ ↦ (1 - s) • v) (-v) t := by
          convert (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const v) using 1 <;> simp
        have hright : HasDerivAt (fun s : ℝ ↦ s • w) w t := by
          convert (hasDerivAt_id t).smul_const w using 1 <;> simp
        convert hleft.add hright using 1;
          simp [sub_eq_add_neg, add_comm]
      exact (hasDerivAt_const t x).prodMk hξder
    have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt F
        (fderiv ℝ H.vectorField (x, ξ t) (0, w - v)) t := by
      intro t ht
      have hd : DifferentiableAt ℝ H.vectorField (x, ξ t) := by
        exact ((H.contDiffOn_vectorField_of_subset H.isOpen_domain Subset.rfl (n := 2)
          (by convert hH3 using 1; norm_num)).contDiffAt
          (H.isOpen_domain.mem_nhds (hξdom t ht))).differentiableAt
          (by simp)
      dsimp [F]
      exact hd.hasFDerivAt.comp_hasDerivAt t (hpath t)
    have hderivbound : ∀ t ∈ Icc (0 : ℝ) 1,
        ‖fderiv ℝ H.vectorField (x, ξ t) (0, w - v)‖ ≤ B * ‖v - w‖ := by
      intro t ht
      have hfd' := hfd (⟨hx, hξmem t ht⟩ : (x, ξ t) ∈ S)
      calc
        ‖fderiv ℝ H.vectorField (x, ξ t) (0, w - v)‖ ≤
            ‖fderiv ℝ H.vectorField (x, ξ t)‖ * ‖(0, w - v)‖ :=
          (fderiv ℝ H.vectorField (x, ξ t)).le_opNorm _
        _ ≤ B * ‖v - w‖ := by
          simp [Prod.norm_def, norm_sub_rev]
          exact mul_le_mul_of_nonneg_right hfd' (norm_nonneg _)
    have hseg := norm_image_sub_le_of_norm_deriv_le_segment'
      (a := (0 : ℝ)) (b := 1) (f := F)
      (fun t ht ↦ (hderiv t ht).hasDerivWithinAt)
      (fun t ht ↦ hderivbound t (Ico_subset_Icc_self ht))
      1 (right_mem_Icc.2 zero_le_one)
    have hclosebound : ‖H.vectorField (x, v) - H.vectorField (x, w)‖ ≤
        B * ‖v - w‖ := by
      simpa [F, ξ, norm_sub_rev] using hseg
    exact hclosebound.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
