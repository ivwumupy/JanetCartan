module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.CoefficientBudgets.Segment

/-! # Primitive budgets for the parameter coefficient integrand

Composition and bilinear product estimates for the coefficient in
`app:ch_response:thm:response-literal-transfer`, consumed by the unit-interval
integration in `CoefficientBudgets`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ResponseTransfer

set_option maxSynthPendingDepth 4

/-- The fixed bilinear contraction of the carrier derivative with the Hessian
in `app:ch_response:thm:response-literal-transfer`. -/
def parameterCoefficientContraction (n p : ℕ) :
    (Euclidean p →L[ℝ] Euclidean n) →L[ℝ]
      (Euclidean n →L[ℝ] Euclidean n →L[ℝ] ℝ) →L[ℝ]
        (Euclidean n →L[ℝ] Euclidean p →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ (Euclidean n) (Euclidean n →L[ℝ] ℝ)
    (Euclidean p →L[ℝ] ℝ)).comp
    (ContinuousLinearMap.compL ℝ (Euclidean p) (Euclidean n) ℝ).flip

/-- An explicit finite budget for the joint order `k` coefficient jet in
`app:ch_response:eq:direct-envelope-profile`. `A` bounds Hessian jets through
`k`; `M` bounds carrier jets through `k+1`. No frequency occurs. -/
def parameterCoefficientJetBudget (n p k : ℕ) (A M : ℝ) : ℝ :=
  ‖parameterCoefficientContraction n p‖ *
    ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * M *
      ((k - i).factorial * A * (1 + M) ^ (k - i))

/-- The actual segment integrand defining the parameter coefficient
(`app:ch_response:thm:response-literal-transfer`). -/
def parameterCoefficientIntegrand {n p : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean p → Euclidean n)
    (t : ℝ) (q : ParameterCoefficientSpace n p) :
    Euclidean n →L[ℝ] Euclidean p →L[ℝ] ℝ :=
  parameterCoefficientContraction n p (fderiv ℝ ζ q.2.2)
    (fderiv ℝ (fderiv ℝ (S q.1)) (ζ q.2.2 + t • q.2.1))

section
variable {n p : ℕ} {S : Euclidean n → Euclidean n → ℝ}
  {ζ : Euclidean p → Euclidean n} {X D V : Set (Euclidean n)}
  {C : Set (Euclidean p)}
  (hX : IsOpen X) (hD : IsOpen D) (hV : IsOpen V) (hC : IsOpen C)
  (hcD : Convex ℝ D) (hζD : ∀ c ∈ C, ζ c ∈ D)
  (hbuffer : ∀ c ∈ C, ∀ ε ∈ V, ζ c + ε ∈ D)
  (hH : ContDiffOn ℝ ∞
    (fun z : Euclidean n × Euclidean n ↦ fderiv ℝ (fderiv ℝ (S z.1)) z.2) (X ×ˢ D))
  (hζ : ContDiffOn ℝ ∞ ζ C)

include hX hD hC hcD hζD hbuffer hH hζ in
/-- Joint smoothness of the literal integrand follows from primitive chart
smoothness, without evaluating the phase at zero
(`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterCoefficientIntegrand_contDiffAt
    {z : ℝ × ParameterCoefficientSpace n p}
    (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ (X ×ˢ V ×ˢ C)) :
    ContDiffAt ℝ ∞ (fun w : ℝ × ParameterCoefficientSpace n p ↦
      parameterCoefficientIntegrand S ζ w.1 w.2) z := by
  have hc := hζ.contDiffAt (hC.mem_nhds hz.2.2.2)
  have hd := (hζ.fderiv_of_isOpen (m := ∞) hC (by simp)).contDiffAt
    (hC.mem_nhds hz.2.2.2)
  have hh := hH.contDiffAt (x := (z.2.1, ζ z.2.2.2 + z.1 • z.2.2.1)) ((hX.prod hD).mem_nhds
    ⟨hz.2.1, hcD.add_smul_mem (hζD _ hz.2.2.2)
      (hbuffer _ hz.2.2.2 _ hz.2.2.1) hz.1⟩)
  exact ((parameterCoefficientContraction n p).contDiff.contDiffAt.comp z
    (hd.comp z contDiffAt_snd.snd.snd)).clm_apply
    (hh.comp z (contDiffAt_snd.fst.prodMk
      ((hc.comp z contDiffAt_snd.snd.snd).add
        (contDiffAt_fst.smul contDiffAt_snd.snd.fst))))

include hX hD hV hC hcD hζD hbuffer hH hζ in
/-- Faà di Bruno bounds the pulled-back primitive Hessian using only its first
`k` jets and the carrier's first `k` jets
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_parameterCoefficient_hessian_jet_le {N k : ℕ} {A M : ℝ}
    (hM : 0 ≤ M)
    (hA : ∀ j ≤ N, ∀ z ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j
        (fun z : Euclidean n × Euclidean n ↦ fderiv ℝ (fderiv ℝ (S z.1)) z.2) z‖ ≤ A)
    (hb : ∀ j ≤ N + 1, ∀ c ∈ C, ‖iteratedFDeriv ℝ j ζ c‖ ≤ M)
    (hk : k ≤ N) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {q : ParameterCoefficientSpace n p} (hq : q ∈ X ×ˢ V ×ˢ C) :
    ‖iteratedFDeriv ℝ k (fun w : ParameterCoefficientSpace n p ↦
      fderiv ℝ (fderiv ℝ (S w.1)) (ζ w.2.2 + t • w.2.1)) q‖ ≤
        k.factorial * A * (1 + M) ^ k := by
  let U := X ×ˢ V ×ˢ C
  have hU : IsOpen U := hX.prod (hV.prod hC)
  let f := fun w : ParameterCoefficientSpace n p ↦ (w.1, ζ w.2.2 + t • w.2.1)
  have hf : ContDiffOn ℝ ∞ f U := by
    intro w hw
    exact (contDiffAt_fst.prodMk
      (((hζ.contDiffAt (hC.mem_nhds hw.2.2)).comp w contDiffAt_snd.snd).add
        (contDiffAt_snd.fst.const_smul t))).contDiffWithinAt
  have hmap : MapsTo f U (X ×ˢ D) := fun w hw ↦
    ⟨hw.1, hcD.add_smul_mem (hζD _ hw.2.2) (hbuffer _ hw.2.2 _ hw.2.1) ht⟩
  have he := norm_iteratedFDerivWithin_comp_le hH hf (n := k) (by simp)
    (hX.prod hD).uniqueDiffOn hU.uniqueDiffOn hmap hq
    (C := A) (D := 1 + M)
    (fun j hj ↦ by
      rw [iteratedFDerivWithin_of_isOpen _ (hX.prod hD) (hmap hq)]
      exact hA j (hj.trans hk) _ (hmap hq))
    (fun j hj hjk ↦ by
      rw [iteratedFDerivWithin_of_isOpen _ hU hq]
      exact norm_parameterCoefficient_segment_jet_le hC hζ hq.2.2 hj hM
        (hb j (by omega) _ hq.2.2) ht)
  rwa [iteratedFDerivWithin_of_isOpen _ hU hq] at he

include hX hD hV hC hcD hζD hbuffer hH hζ in
/-- Leibniz and composition estimates give a finite bound for the actual
integrand, with one additional primitive carrier jet
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_parameterCoefficientIntegrand_jet_le {N k : ℕ} {A M : ℝ}
    (hM : 0 ≤ M)
    (hA : ∀ j ≤ N, ∀ z ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j
        (fun z : Euclidean n × Euclidean n ↦ fderiv ℝ (fderiv ℝ (S z.1)) z.2) z‖ ≤ A)
    (hb : ∀ j ≤ N + 1, ∀ c ∈ C, ‖iteratedFDeriv ℝ j ζ c‖ ≤ M)
    (hk : k ≤ N) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {q : ParameterCoefficientSpace n p} (hq : q ∈ X ×ˢ V ×ˢ C) :
    ‖iteratedFDeriv ℝ k (parameterCoefficientIntegrand S ζ t) q‖ ≤
      parameterCoefficientJetBudget n p k A M := by
  let U := X ×ˢ V ×ˢ C
  have hU : IsOpen U := hX.prod (hV.prod hC)
  have hdζ : ContDiffOn ℝ ∞ (fderiv ℝ ζ) C := hζ.fderiv_of_isOpen hC (by simp)
  have hd : ContDiffOn ℝ ∞
      (fun w : ParameterCoefficientSpace n p ↦ fderiv ℝ ζ w.2.2) U := by
    intro w hw
    exact ((hdζ.contDiffAt (hC.mem_nhds hw.2.2)).comp w
      contDiffAt_snd.snd).contDiffWithinAt
  have hh : ContDiffOn ℝ ∞ (fun w : ParameterCoefficientSpace n p ↦
      fderiv ℝ (fderiv ℝ (S w.1)) (ζ w.2.2 + t • w.2.1)) U := by
    intro w hw
    exact ((hH.contDiffAt ((hX.prod hD).mem_nhds
      ⟨hw.1, hcD.add_smul_mem (hζD _ hw.2.2) (hbuffer _ hw.2.2 _ hw.2.1) ht⟩)).comp w
      (contDiffAt_fst.prodMk
        (((hζ.contDiffAt (hC.mem_nhds hw.2.2)).comp w contDiffAt_snd.snd).add
          (contDiffAt_snd.fst.const_smul t)))).contDiffWithinAt
  have he := (parameterCoefficientContraction n p).norm_iteratedFDerivWithin_le_of_bilinear
    hd hh hU.uniqueDiffOn hq (n := k) (by simp)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hU hq] at he
  apply he.trans
  unfold parameterCoefficientJetBudget
  gcongr with i hi
  · exact (norm_parameterCoefficient_pullback_le hC hdζ hq.2.2 i).trans (by
      rw [norm_iteratedFDeriv_fderiv]
      exact hb (i + 1) (by simp only [Finset.mem_range] at hi; omega) _ hq.2.2)
  · exact norm_parameterCoefficient_hessian_jet_le hX hD hV hC hcD hζD hbuffer hH hζ
      hM hA hb (by omega) ht hq
end
end JanetCartan.ResponseTransfer
