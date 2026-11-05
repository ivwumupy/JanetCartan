module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.FrequencySobolev
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.Multiplication
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Scale

/-! # Fixed physical multiplication for the terminal estimate

The existing scalar integer multiplier theorem, with compact derivative bounds,
controls the original output mask in `app:ch_regular:eq:resolved-angular-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open FourierIntegral LowBounds Pseudodifferential IsometricEmbedding.Reconstruction
open ResponseTransfer.Complement
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The original fixed smooth compact physical multiplier is bounded on the
actual vector Fourier Sobolev level. No membership or multiplier estimate is
assumed (`app:ch_regular:eq:resolved-angular-tail`). -/
theorem exists_sourceCutMultiplier_fourierSobolev_bound
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχb : ∀ x, ‖χ x‖ ≤ 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H, MemVectorFourierSobolev (m : ℝ) u →
      MemVectorFourierSobolev (m : ℝ) (sourceCutMultiplier χ hχ.continuous hχb u) ∧
      vectorFourierSobolevNorm (m : ℝ) (sourceCutMultiplier χ hχ.continuous hχb u) ≤
        C * vectorFourierSobolevNorm (m : ℝ) u := by
  let c : E → ℂ := fun x ↦ (χ x : ℂ)
  have hc : ContDiff ℝ ∞ c := Complex.ofRealCLM.contDiff.comp hχ
  have hcs : HasCompactSupport c := hχs.comp_left Complex.ofReal_zero
  obtain ⟨B, hB, hb⟩ := hcs.exists_bound_iteratedFDeriv hc m
  let C := localizedMultiplierConstant n m * ((m + 1 : ℕ) : ℝ) * B
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (localizedMultiplierConstant_pos n m).le (by positivity)) hB
  refine ⟨C, hC, ?_⟩
  intro u hu
  let Q := finiteL2CoordinateIsometry (I := Fin r) (volume : Measure E)
  have he (i : Fin r) : Q (sourceCutMultiplier χ hχ.continuous hχb u) i =
      localizedScalarProduct c hc hcs (Q u i) := by
    apply Lp.ext
    filter_upwards [finiteL2Coordinates_apply_ae volume
      (sourceCutMultiplier χ hχ.continuous hχb u) i,
      sourceCutMultiplier_coeFn χ hχ.continuous hχb u,
      localizedScalarProduct_ae c hc hcs (Q u i),
      finiteL2Coordinates_apply_ae volume u i] with x hx ht hp hu'
    change (Q u i) x = u x i at hu'
    exact hx.trans (by rw [ht, hp, hu']; rfl)
  have hcoord (i : Fin r) :
      MemFourierSobolev (m : ℝ) (Q (sourceCutMultiplier χ hχ.continuous hχb u) i) ∧
      fourierSobolevNorm (m : ℝ) (Q (sourceCutMultiplier χ hχ.continuous hχb u) i) ≤
        C * fourierSobolevNorm (m : ℝ) (Q u i) := by
    rw [he]
    obtain ⟨hm, hn⟩ := localizedScalarProduct_frechet_bound m c hc hcs
      (fun _ ↦ B) (fun _ ↦ hB) hb (Q u i) (hu i)
    refine ⟨hm, hn.trans ?_⟩
    have hs : mixedAmplitudeSobolevSum m (fun _ ↦ B) (Q u i) ≤
        ((m + 1 : ℕ) : ℝ) * B * fourierSobolevNorm (m : ℝ) (Q u i) := by
      calc
        _ ≤ ∑ _k ∈ Finset.range (m + 1), B * fourierSobolevNorm (m : ℝ) (Q u i) := by
          apply Finset.sum_le_sum
          intro k hk
          apply mul_le_mul_of_nonneg_left (fourierSobolevNorm_mono (hu i) ?_) hB
          exact_mod_cast (show k ≤ m by have := Finset.mem_range.mp hk; omega)
        _ = _ := by simp [mul_assoc]
    exact (mul_le_mul_of_nonneg_left hs (localizedMultiplierConstant_pos n m).le).trans_eq
      (by dsimp [C]; ring)
  exact ⟨fun i ↦ (hcoord i).1,
    vectorFourierSobolevNorm_le_of_coordinate_bounds hC _ _ (fun i ↦ (hcoord i).2)⟩

namespace TerminalBounds

/-- Addition on the existing vector Sobolev level, for the two terminal tails
in `app:ch_regular:eq:resolved-angular-tail`. -/
theorem add_bound {s : ℝ} {u v : H}
    (hu : MemVectorFourierSobolev s u) (hv : MemVectorFourierSobolev s v) :
    MemVectorFourierSobolev s (u + v) ∧
      vectorFourierSobolevNorm s (u + v) ≤
        vectorFourierSobolevNorm s u + vectorFourierSobolevNorm s v := by
  let a : vectorFourierSobolevLevel s := ⟨u, hu⟩
  let b : vectorFourierSobolevLevel s := ⟨v, hv⟩
  refine ⟨(a + b).property, ?_⟩
  have h := norm_add_le (vectorWeightedFourier s a) (vectorWeightedFourier s b)
  rw [← map_add, norm_vectorWeightedFourier, norm_vectorWeightedFourier,
    norm_vectorWeightedFourier] at h
  exact h

/-- Negation preserves the same vector Sobolev norm; used for the full
identity subtraction in `app:ch_regular:eq:chain-tail`. -/
theorem neg_bound {s : ℝ} {u : H} (hu : MemVectorFourierSobolev s u) :
    MemVectorFourierSobolev s (-u) ∧
      vectorFourierSobolevNorm s (-u) = vectorFourierSobolevNorm s u := by
  let a : vectorFourierSobolevLevel s := ⟨u, hu⟩
  refine ⟨(-a).property, ?_⟩
  have h := norm_neg (vectorWeightedFourier s a)
  rw [← map_neg, norm_vectorWeightedFourier, norm_vectorWeightedFourier] at h
  exact h

end TerminalBounds
end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
