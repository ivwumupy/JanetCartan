module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.PhysicalBounds.GradedAtoms
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.PhysicalBounds.Quotient

/-!
# The literal demodulated atom and its primitive physical bound

This connects the exact quotient to the graded exponential/product estimate
for `app:ch_waves:eq:raw-physical-bound`. Its consumer is the physical bound
for `rawPrimaryDemodulatedIntegral` on arbitrary integrable Fourier data.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.RawPrimary

variable {X P F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The density-free integrand of `rawPrimaryDemodulatedIntegral`, with the
literal nonzero phase quotient (`app:ch_waves:eq:individual-representation`). -/
def rawPrimaryDemodulatedAtom (S : X → P → ℝ) (A : X → P → F) (ζ : P) (τ : ℝ)
    (p : X × P) : F :=
  Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ p.1 p.2 : ℂ)) •
    A p.1 (ζ + τ • p.2)

/-- The quotient is smooth on every buffered domain where its two phase
arguments remain in the original chart (`app:ch_waves:eq:phase-quotient`). -/
theorem contDiffOn_rawPrimaryPhaseDifference {U : Set X} {V Ω : Set P}
    {S : X → P → ℝ} (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    {ζ : P} {τ : ℝ} (hζ : ζ ∈ V) (hshift : ∀ η ∈ Ω, ζ + τ • η ∈ V) :
    ContDiffOn ℝ ∞ (fun p : X × P ↦ rawPrimaryPhaseDifference S ζ τ p.1 p.2)
      (U ×ˢ Ω) := by
  have hl : ContDiffOn ℝ ∞ (fun p : X × P ↦ S p.1 (ζ + τ • p.2)) (U ×ˢ Ω) :=
    hS.comp (contDiffOn_fst.prodMk
      (contDiffOn_const.add (contDiffOn_const.smul contDiffOn_snd)))
      (fun p hp ↦ ⟨hp.1, hshift p.2 hp.2⟩)
  have hr : ContDiffOn ℝ ∞ (fun p : X × P ↦ S p.1 ζ) (U ×ˢ Ω) :=
    hS.comp (contDiffOn_fst.prodMk contDiffOn_const) (fun _ hp ↦ ⟨hp.1, hζ⟩)
  simpa only [rawPrimaryPhaseDifference, div_eq_mul_inv] using
    (hl.sub hr).mul (contDiffOn_const (c := τ⁻¹))

/-- The actual demodulated atom is jointly smooth. Only phase/amplitude
smoothness and shifted-domain containment enter this result
(`app:ch_waves:eq:individual-representation`). -/
theorem contDiffOn_rawPrimaryDemodulatedAtom {U : Set X} {V Ω : Set P}
    {S : X → P → ℝ} {A : X → P → F}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V))
    {ζ : P} {τ : ℝ} (hζ : ζ ∈ V) (hshift : ∀ η ∈ Ω, ζ + τ • η ∈ V) :
    ContDiffOn ℝ ∞ (rawPrimaryDemodulatedAtom S A ζ τ) (U ×ˢ Ω) := by
  have hφ := contDiffOn_rawPrimaryPhaseDifference hS hζ hshift
  exact (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hφ)).cexp.smul
    (hA.comp (contDiffOn_fst.prodMk
      (contDiffOn_const.add (contDiffOn_const.smul contDiffOn_snd)))
      (fun p hp ↦ ⟨hp.1, hshift p.2 hp.2⟩))

end JanetCartan.RawPrimary

namespace JanetCartan.RawPrimary

variable {X P F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Every physical jet of the literal atom satisfies the required scale
bound, derived entirely from primitive amplitude and covector-phase jets.
The producer of those primitive grades remains the actual WKB/common-history
construction (`app:ch_waves:eq:raw-physical-bound`). -/
theorem norm_iteratedFDeriv_rawPrimaryDemodulatedAtom_le
    {U : Set X} {V : Set P} (hU : IsOpen U) (hV : IsOpen V)
    {S : X → P → ℝ} {A : X → P → F}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V))
    {ζ η : P} {τ : ℝ} (hτ : τ ≠ 0) (hζ : ζ ∈ V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, ζ + (t * τ) • η ∈ V)
    {x : X} (hx : x ∈ U) {m : ℕ} {a s : ℕ → ℝ} {c K L : ℝ}
    (hc : 0 ≤ c) (hK : 0 ≤ K) (hL : 0 ≤ L) (hη : ‖η‖ ≤ c * K)
    (ha : ∀ j ≤ m, 0 ≤ a j) (hs : ∀ j, 1 ≤ j → j ≤ m → 0 ≤ s j)
    (hAj : ∀ j ≤ m, ∀ ξ ∈ V, ‖iteratedFDeriv ℝ j (fun y ↦ A y ξ) x‖ ≤ a j * L ^ j)
    (hSj : ∀ j, 1 ≤ j → j ≤ m → ∀ ξ ∈ V,
      ‖iteratedFDeriv ℝ j (fun y ↦ fderiv ℝ (S y) ξ) x‖ ≤ s j * L ^ (j - 1)) :
    ‖iteratedFDeriv ℝ m (fun y ↦ rawPrimaryDemodulatedAtom S A ζ τ (y, η)) x‖ ≤
      atomJetConstant a (fun j ↦ c * s j) m * (K + L) ^ m := by
  have hshift : ζ + τ • η ∈ V := by simpa using hseg 1 (by simp)
  have hφ : ContDiffOn ℝ m (fun y ↦ rawPrimaryPhaseDifference S ζ τ y η) U :=
    ((contDiffOn_rawPrimaryPhaseDifference hS hζ
      (Ω := {η}) (fun z hz ↦ by simpa only [mem_singleton_iff.mp hz] using hshift)).comp
      (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy ↦ ⟨hy, rfl⟩)).of_le (by simp)
  have hAx : ContDiffOn ℝ m (fun y ↦ A y (ζ + τ • η)) U :=
    (hA.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy ↦ ⟨hy, hshift⟩)).of_le (by simp)
  exact norm_iteratedFDeriv_oscillatoryAtom_le hU hφ hAx hK hL ha
    (fun j hj hj' ↦ mul_nonneg hc (hs j hj hj')) hx
    (fun j hj ↦ hAj j hj _ hshift)
    (fun j hj hj' ↦ norm_iteratedFDeriv_rawPrimaryPhaseDifference_le_grade
      hU hV hS hτ hseg hx j (hs j hj hj') hL hη (hSj j hj hj'))

end JanetCartan.RawPrimary
