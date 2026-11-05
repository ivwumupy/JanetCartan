module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.FiniteIdentity

/-!
# Regularity of the actual differentiated correction amplitude

The retarded regularization producer needs continuity of P W₁, jointly in
both times and spatial variables. Here it follows from the same smooth
coefficients and W₁ used in the finite identity, including B₀. Consumer:
`completeResidual_operators_of_graph_regularizations`.
Source: `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.CharacteristicTransport.CompleteResidual
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ
local notation "T" => (ℝ × ℝ) × (Euclidean d × Euclidean d)

private theorem contDiff_complex_matrix
    (A : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x ↦ A x i j)) :
    ContDiff ℝ ∞ (fun x ↦ (A x).map Complex.ofReal) := by
  classical
  have he : (fun x ↦ (A x).map Complex.ofReal) = fun x ↦
      ∑ i, ∑ j, (A x i j : ℂ) • (Matrix.single i j 1 : Mat) := by
    funext x
    ext i j
    simp [Matrix.single, Matrix.sum_apply, ite_and]
  rw [he]
  exact ContDiff.sum fun i _ ↦ ContDiff.sum fun j _ ↦
    (Complex.ofRealCLM.contDiff.comp (hA i j)).smul contDiff_const

/-- The differentiated two-time correction is jointly smooth. This proves
the continuity input of the retarded strong-limit producer from the original
coefficient and amplitude regularity, without adding a new analytic premise
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem contDiff_twoTimePhysicalApply_of_real_coefficients
    (A : E → Fin (d + 1) → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (W : TwoTimeAmplitude d q)
    (hW : ContDiff ℝ ∞ (fun p : T ↦ W p.1.1 p.1.2 p.2.1 p.2.2)) :
    ContDiff ℝ ∞ (fun p : T ↦ twoTimePhysicalApply
      (fun x a ↦ (A x a).map Complex.ofReal) (fun x ↦ (B x).map Complex.ofReal)
      W p.1.1 p.1.2 p.2.1 p.2.2) := by
  let F : T → E → Mat := fun p x ↦ W (x 0) p.1.2 (spatialPart x) p.2.2
  let g : T → E := fun p ↦ timeSpacePoint p.1.1 p.2.1
  have hg : ContDiff ℝ ∞ g :=
    contDiff_timeSpacePoint.comp (contDiff_fst.fst.prodMk contDiff_snd.fst)
  have hsp : ContDiff ℝ ∞ (spatialPart : E → Euclidean d) := by
    apply (contDiff_piLp 2).mpr
    intro i
    change ContDiff ℝ ∞ (fun x : E ↦ x i.succ)
    exact (EuclideanSpace.proj (𝕜 := ℝ) i.succ).contDiff
  have hF : ContDiff ℝ ∞ (Function.uncurry F) :=
    hW.comp ((((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff.comp
      contDiff_snd).prodMk contDiff_fst.fst.snd).prodMk
      ((hsp.comp contDiff_snd).prodMk contDiff_fst.snd.snd))
  have hd (a : Fin (d + 1)) : ContDiff ℝ ∞
      (fun p ↦ partialDeriv (F p) (g p) a) :=
    (hF.fderiv hg (by simp)).clm_apply contDiff_const
  change ContDiff ℝ ∞ (fun p : T ↦
    (∑ a, (A (g p) a).map Complex.ofReal * partialDeriv (F p) (g p) a) +
      (B (g p)).map Complex.ofReal * F p (g p))
  exact (ContDiff.sum fun a _ ↦
    ((contDiff_complex_matrix (fun x ↦ A x a) (hA a)).comp hg).mul (hd a)).add
      (((contDiff_complex_matrix B hB).comp hg).mul (hF.comp (contDiff_id.prodMk hg)))

/-- Physical differentiation preserves the original lower source-time buffer:
source time is frozen in every derivative. Consumer: the P W₁ retarded
producer in `completeResidual_operators_of_graph_regularizations`.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem twoTimePhysicalApply_eq_zero_of_lower_buffer
    (A : E → Fin (d + 1) → Mat) (B : E → Mat) (W : TwoTimeAmplitude d q)
    (a : ℝ) (hzero : ∀ t s y η, s ≤ a → W t s y η = 0)
    (t s : ℝ) (y η : Euclidean d) (hs : s ≤ a) :
    twoTimePhysicalApply A B W t s y η = 0 := by
  have hz : (fun x : E ↦ W (x 0) s (spatialPart x) η) = fun _ ↦ 0 :=
    funext fun x ↦ hzero (x 0) s (spatialPart x) η hs
  simp only [twoTimePhysicalApply, physicalSymbolApply]
  simp only [hz, partialDeriv]
  simp [hzero _ _ _ _ hs]

end JanetCartan.CharacteristicTransport.CompleteResidual
