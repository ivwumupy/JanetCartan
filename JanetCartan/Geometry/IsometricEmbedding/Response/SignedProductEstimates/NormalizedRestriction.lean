module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedQuadratures

/-!
# Restriction norms for the original corrected-source quadratures

The existing Fourier-to-weak-jet comparison and fixed real fiber map retain
the original source, measure and quadratures. Constants precede all domains,
sources and frequencies. Consumer: the restricted signed angular contribution
in `app:ch_pairs:prop:pairs-lag-sum` and `resolved-angular-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace JanetCartan.SignedProductEstimates
open LocalSobolev Pseudodifferential RegularSector.Characteristic.RetardedLocalization
open ArbitraryAccuracy.ResidualLocalization
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "RV" => EuclideanSpace ℝ (Fin (d+1))
local notation "H" => Lp V 2 (volume : Measure E)

/-- Both real quadratures have the same restriction bound from the actual
complex Fourier norm. The original rotation and real part form one fixed
fiber map, independent of source frequency and accuracy
(`app:ch_pairs:eq:pairs-lag-one-error`, source contribution). -/
theorem exists_source_quadrature_restriction_comparison (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H), MemVectorFourierSobolev (s : ℝ) u →
      ∀ (W : Set E) (c : ℂ), ‖c‖ = 1 →
        MemRestrictionSobolev W s (l2RealPart (volume.restrict W) (c • restrictL2 W u)) ∧
        restrictionSobolevNorm W s (l2RealPart (volume.restrict W) (c • restrictL2 W u)) ≤
          C * vectorFourierSobolevNorm (s : ℝ) u := by
  obtain ⟨C, hC, hbound⟩ := vector_restrictionSobolev_nat_bounds (d+1) (d+1) s
  refine ⟨2*C, by positivity, ?_⟩
  intro u hu W c hc
  obtain ⟨hm, hn⟩ := hbound u hu W (restrictL2 W u) (restrictL2_coeFn W u).symm
  let L : V →L[ℝ] RV := euclideanRealPart.comp ((c • ContinuousLinearMap.id ℂ V).restrictScalars ℝ)
  have hL : ‖L‖ ≤ 1 := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    have hid : ‖(c • ContinuousLinearMap.id ℂ V).restrictScalars ℝ‖ ≤ 1 := by
      rw [ContinuousLinearMap.norm_restrictScalars, norm_smul, hc, one_mul]
      exact ContinuousLinearMap.norm_id_le
    exact (mul_le_mul euclideanRealPart_norm_le hid (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
  have he : L.compLp (restrictL2 W u) = l2RealPart (volume.restrict W) (c • restrictL2 W u) := by
    apply Lp.ext
    filter_upwards [L.coeFn_compLp (restrictL2 W u),
      euclideanRealPart.coeFn_compLpL (c • restrictL2 W u), Lp.coeFn_smul c (restrictL2 W u)]
      with y hl hr hs
    change (l2RealPart (volume.restrict W) (c • restrictL2 W u)) y = _ at hr
    rw [hl, hr, hs, Pi.smul_apply]
    rfl
  obtain ⟨hrm, hrn⟩ := compLp_restrictionSobolev_bound L hm
  rw [he] at hrm hrn
  refine ⟨hrm, ?_⟩
  calc
    _ ≤ 2 * restrictionSobolevNorm W s (restrictL2 W u) := hrn.trans
      (mul_le_mul_of_nonneg_right (by linarith : ‖L‖+1 ≤ 2) restrictionSobolevNorm_nonneg)
    _ ≤ 2 * (C * vectorFourierSobolevNorm (s : ℝ) u) := mul_le_mul_of_nonneg_left hn (by norm_num)
    _ = _ := by ring
end JanetCartan.SignedProductEstimates
