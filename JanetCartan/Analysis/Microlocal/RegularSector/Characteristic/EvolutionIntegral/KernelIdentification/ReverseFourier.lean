module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.ReverseTriangle

/-!
# The compact retarded adjoint in its literal order

Frequency multiplication by `conj (θ β)` stays outside the reversed time
triangle. The source mask is outermost and the conjugate output mask acts on
the datum before the adjoint evolution. Thus the formula retains precisely
`Mχsource* Bβ* E_b* Mχout*`, including physical Fourier normalization.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open FourierIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ

/-- The reverse spatial/time Fourier integrand before applying the conjugate
spacetime multiplier. It contains the original conjugate-transposed matrix
and output mask. Source: `app:ch_regular_base:lem:retarded-kernel`. -/
def reverseTimeFourierKernel (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout : E → ℂ) (u : E → V) (ξ : E) (t s : ℝ) (y : Euclidean d) : V :=
  star (Complex.exp (Complex.I * ((s * ξ 0 + Ψ t s y (spatialPart ξ) : ℝ) : ℂ))) •
    (b t s y (spatialPart ξ)).conjTranspose.mulVec
      (star (χout (timeSpacePoint t y)) • u (timeSpacePoint t y))

/-- The reversed retarded triangle followed by the adjoint Fourier multiplier
and then the source mask. This is the actual compact spectral kernel, with
`Bβ*` to the left of `E_b*`, in `app:ch_regular_base:lem:retarded-kernel`. -/
def cutReverseRetardedFourier (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β θ : E → ℂ) (u : E → V) (a c : ℝ) (z : E) : V :=
  star (χsource z) • (((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ •
    ∫ ξ, (star (θ ξ * β ξ) * Complex.exp (Complex.I * (inner ℝ z ξ : ℂ))) •
      ∫ s in Icc a c, ∫ t in s..c, ∫ y, reverseTimeFourierKernel Ψ b χout u ξ t s y)

/-- Split the conjugate graph oscillation without commuting any multiplier.
Consumer: the reversed kernels in `app:ch_regular_base:lem:retarded-kernel`. -/
theorem graphOscillation_star_split (S : E → E → ℝ) (x z ξ : E) :
    star (graphOscillation S x z ξ) =
      Complex.exp (Complex.I * (inner ℝ z ξ : ℂ)) *
        star (Complex.exp (Complex.I * (S x ξ : ℂ))) := by
  change (starRingEnd ℂ) (Complex.exp _) = _ * (starRingEnd ℂ) (Complex.exp _)
  rw [← Complex.exp_conj, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- Compact-frequency Fubini on the fixed elapsed slab. Consumer: the
literal reversed retarded triangle in `app:ch_regular_base:lem:retarded-kernel`. -/
theorem integral_compact_frequency_slab_swap (G : ℝ → E → V)
    (hG : Continuous (Function.uncurry G)) {K : Set E} (hK : IsCompact K)
    (hs : ∀ r ξ, ξ ∉ K → G r ξ = 0) (Δ : ℝ) :
    (∫ r in Icc 0 Δ, ∫ ξ, G r ξ) = ∫ ξ, ∫ r in Icc 0 Δ, G r ξ := by
  have he (r : ℝ) : (∫ ξ, G r ξ) = ∫ ξ in K, G r ξ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hs r)).symm
  have he' : (∫ ξ, ∫ r in Icc 0 Δ, G r ξ) = ∫ ξ in K, ∫ r in Icc 0 Δ, G r ξ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun ξ hξ ↦ by simp [hs _ ξ hξ])).symm
  simp_rw [he]
  rw [he']
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  exact hG.continuousOn.integrableOn_compact (isCompact_Icc.prod hK)

/-- Joint continuity of the literal reverse integrand from the primitive
phase, amplitude, output mask and datum. Consumer: Fubini in
`integral_cut_reverse_elapsedGraph_eq_reverseRetardedFourier`, from
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem continuous_reverseTimeFourierKernel
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout : E → ℂ) (u : E → V)
    (hΨ : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hb : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      b p.1.1 p.1.2 p.2.1 p.2.2))
    (ho : Continuous χout) (hu : Continuous u) :
    Continuous (fun p : ((ℝ × ℝ) × Euclidean d) × E ↦
      reverseTimeFourierKernel Ψ b χout u p.2 p.1.1.1 p.1.1.2 p.1.2) := by
  have hp : Continuous (fun p : ((ℝ × ℝ) × Euclidean d) × E ↦
      (p.1.1, (p.1.2, spatialPart p.2))) :=
    continuous_fst.fst.prodMk (continuous_fst.snd.prodMk (continuous_spatialPart.comp continuous_snd))
  have hx : Continuous (fun p : ((ℝ × ℝ) × Euclidean d) × E ↦
      timeSpacePoint p.1.1.1 p.1.2) := continuous_timeSpacePoint.comp
    (continuous_fst.fst.fst.prodMk continuous_fst.snd)
  have hphase := (show Continuous (fun p : ((ℝ × ℝ) × Euclidean d) × E ↦ p.1.1.2 * p.2 0)
    by fun_prop).add (hΨ.comp hp)
  exact (continuous_const.mul (Complex.continuous_ofReal.comp hphase)).cexp.star.smul
    ((hb.comp hp).matrix_conjTranspose.matrix_mulVec ((ho.comp hx).star.smul (hu.comp hx)))

/-- The actual compact adjoint elapsed integral is the reversed retarded
triangle with every mask and the Fourier multiplier in literal order.
All Fubini integrability follows from continuity and compact masks/cutoffs;
the lower buffer and endpoints use `integral_fixed_slab_eq_retarded` through
`integral_elapsed_space_eq_reverse_triangle`. No test-action hypothesis or
Sobolev estimate is used. Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem integral_cut_reverse_elapsedGraph_eq_reverseRetardedFourier
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β θ : E → ℂ)
    (hΨ : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hb : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      b p.1.1 p.1.2 p.2.1 p.2.2))
    (ho : Continuous χout) (hβ : Continuous β) (hθ : Continuous θ)
    (hocs : HasCompactSupport χout) (hθcs : HasCompactSupport θ)
    (a c Δ : ℝ) (hcΔ : c - a ≤ Δ)
    (hout : ∀ x, χout x ≠ 0 → x 0 ∈ Icc a c)
    (hzero : ∀ t s y η, s ≤ a → b t s y η = 0)
    (u : E → V) (hu : Continuous u) (z : E) :
    (∫ r in Icc 0 Δ, reverseGraphOperator (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude (fun ξ ↦ star (θ ξ))
        (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose)) u z) =
      cutReverseRetardedFourier Ψ b χout χsource β θ u a c z := by
  let F := reverseTimeFourierKernel Ψ b χout u
  let k : E → ℂ := fun ξ ↦ star (θ ξ * β ξ) * Complex.exp (Complex.I * (inner ℝ z ξ : ℂ))
  have hF := continuous_reverseTimeFourierKernel Ψ b χout u hΨ hb ho hu
  have hfx : Continuous (fun p : (ℝ × E) × E ↦ F p.1.2 (p.2 0) (p.2 0 - p.1.1)
      (spatialPart p.2)) := hF.comp
    (((show Continuous (fun p : (ℝ × E) × E ↦ p.2 0) by fun_prop).prodMk
      (by fun_prop)).prodMk (continuous_spatialPart.comp continuous_snd) |>.prodMk continuous_fst.snd)
  have hfxzero (r : ℝ) (ξ x : E) (hx : x ∉ tsupport χout) :
      F ξ (x 0) (x 0 - r) (spatialPart x) = 0 := by
    have he : timeSpacePoint (x 0) (spatialPart x) = x := timeSpaceMeasurableEquiv.symm_apply_apply x
    simp [F, reverseTimeFourierKernel, he, image_eq_zero_of_notMem_tsupport hx]
  have he (r : ℝ) (ξ : E) : (∫ x, F ξ (x 0) (x 0 - r) (spatialPart x)) =
      ∫ x in tsupport χout, F ξ (x 0) (x 0 - r) (spatialPart x) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hfxzero r ξ)).symm
  have hI : Continuous (fun p : ℝ × E ↦ ∫ x, F p.2 (x 0) (x 0 - p.1) (spatialPart x)) := by
    simp_rw [he]
    exact continuous_parametric_integral_of_continuous hfx hocs
  have hk : Continuous k := (hθ.mul hβ).star.mul
    ((continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id))).cexp)
  have hG : Continuous (fun p : ℝ × E ↦ k p.2 • ∫ x, F p.2 (x 0) (x 0 - p.1) (spatialPart x)) :=
    (hk.comp continuous_snd).smul hI
  have hkzero (ξ : E) (hξ : ξ ∉ tsupport θ) : k ξ = 0 := by
    simp [k, image_eq_zero_of_notMem_tsupport hξ]
  have hmask (r : ℝ) : reverseGraphOperator (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude (fun ξ ↦ star (θ ξ))
        (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose)) u z =
      star (χsource z) • (((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ •
        ∫ ξ, k ξ • ∫ x, F ξ (x 0) (x 0 - r) (spatialPart x)) := by
    rw [cut_reverse_elapsedGraph_masks]
    congr 2
    apply integral_congr_ae
    filter_upwards [] with ξ
    simp only [k, mul_smul, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [graphOscillation_star_split]
    have he : timeSpacePoint (x 0) (spatialPart x) = x := timeSpaceMeasurableEquiv.symm_apply_apply x
    simp only [mul_smul, F, reverseTimeFourierKernel, elapsedPhase, he]
  simp_rw [hmask]
  rw [integral_smul, integral_smul]
  rw [integral_compact_frequency_slab_swap _ hG hθcs (fun r ξ hξ ↦ by simp [hkzero ξ hξ]) Δ]
  unfold cutReverseRetardedFourier
  congr 2
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [integral_smul]
  apply congrArg (k ξ • ·)
  apply integral_elapsed_space_eq_reverse_triangle (F ξ)
    (hF.comp (continuous_id.prodMk continuous_const))
    (hocs.image continuous_spatialPart) a c Δ hcΔ
  · intro t s y h
    have hx : χout (timeSpacePoint t y) = 0 := by
      by_contra hn
      rcases h with ht | hy
      · exact ht (by simpa only [timeSpacePoint_time] using hout _ hn)
      · exact hy ⟨timeSpacePoint t y, subset_tsupport χout hn, spatialPart_timeSpacePoint t y⟩
    simp [F, reverseTimeFourierKernel, hx]
  · intro t s y hs
    simp [F, reverseTimeFourierKernel, hzero _ _ _ _ hs]

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
