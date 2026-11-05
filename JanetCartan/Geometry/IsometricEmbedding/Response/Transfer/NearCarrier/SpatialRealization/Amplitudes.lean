module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.SpatialRealization.CompactKernels

/-!
# Smooth compact spatial transfer amplitudes

Closure of the original full amplitudes under the forward and reverse spatial
trades in `app:ch_response:eq:direct-envelope-profile`. The inverse coefficient
is differentiated inside the reverse remainder, so the original Jacobian,
weight, masks, selector and both amplitude positions are retained.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.SpatialRealization
open FourierIntegral
variable {n r : ℕ} {X Y F : Set (Euclidean n)} {A : FullAmplitude n r}

/-- Forward datum coefficients preserve the full carriers and smoothness in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem admissible_forwardDatumAmplitude (hA : ForwardAmplitudeAdmissible X Y F A)
    {B : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ} (i j : Fin n)
    (hB : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ B p.1 p.2 i j)) :
    ForwardAmplitudeAdmissible X Y F (forwardDatumAmplitude B A i j) := by
  refine ⟨(Complex.ofRealCLM.contDiff.comp
    (hB.comp (contDiff_fst.prodMk contDiff_snd.snd))).smul hA.smooth, ?_⟩
  intro x y δ h
  simp [forwardDatumAmplitude, hA.support x y δ h]

/-- The exact forward remainder is smooth and retains all three carriers.
Its source derivative does not differentiate `B(x,δ)`.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem admissible_forwardRemainderAmplitude (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsClosed X) (hY : IsClosed Y)
    {B : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ} (i : Fin n)
    (hB : ∀ j, ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ B p.1 p.2 i j)) :
    ForwardAmplitudeAdmissible X Y F (forwardRemainderAmplitude B A i) := by
  have hx := hA.outputPartial hX i
  have hy (j) := admissible_forwardDatumAmplitude (hA.sourcePartial hY j) i j (hB j)
  refine ⟨hx.smooth.add (ContDiff.sum (fun j _ ↦ (hy j).smooth)), ?_⟩
  intro x y δ h
  change _ + ∑ j, forwardDatumAmplitude B
    (fun x y δ ↦ partialDeriv (fun z ↦ A x z δ) y j) i j x y δ = 0
  rw [hx.support x y δ h]
  simp only [(hy _).support x y δ h, Finset.sum_const_zero, add_zero]

/-- Reverse datum coefficients depend on the source position. The physical
support and every weight stay in the amplitude
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem admissible_reverseDatumAmplitude (hA : ForwardAmplitudeAdmissible X Y F A)
    {C : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ} (i j : Fin n)
    (hC : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ C p.1 p.2 i j)) :
    ForwardAmplitudeAdmissible X Y F (ReverseDerivative.datumAmplitude C A i j) := by
  refine ⟨(Complex.ofRealCLM.contDiff.comp (hC.comp contDiff_snd)).smul hA.smooth, ?_⟩
  intro y x δ h
  simp [ReverseDerivative.datumAmplitude, hA.support y x δ h]

/-- The full reverse remainder `∂y A + Σ ∂x(C A)` preserves smoothness and
carriers. In particular, this proof includes derivatives of `C`.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem admissible_reverseRemainderAmplitude (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsClosed X) (hY : IsClosed Y)
    {C : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ} (i : Fin n)
    (hC : ∀ j, ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ C p.1 p.2 i j)) :
    ForwardAmplitudeAdmissible X Y F (ReverseDerivative.remainderAmplitude C A i) := by
  have hx := hA.outputPartial hX i
  have hy (j) := (admissible_reverseDatumAmplitude hA i j (hC j)).sourcePartial hY j
  refine ⟨hx.smooth.add (ContDiff.sum (fun j _ ↦ (hy j).smooth)), ?_⟩
  intro y x δ h
  change _ + ∑ j, partialDeriv (fun z ↦ ReverseDerivative.datumAmplitude C A i j y z δ) x j = 0
  rw [hx.support y x δ h]
  simp only [(hy _).support y x δ h, Finset.sum_const_zero, add_zero]

/-- Source sections of the full amplitude have compact support. This is the
boundary-term input of the reverse trade in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem compactSupport_amplitude_source (hA : ForwardAmplitudeAdmissible X Y F A)
    (hY : IsCompact Y) (x δ : Euclidean n) : HasCompactSupport (fun y ↦ A x y δ) := by
  apply hY.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hY.isClosed
  intro y hy
  by_contra hn
  exact hy (hA.support x y δ (Or.inr (Or.inl hn)))

/-- Joint smoothness of the forward envelope oscillation from the primitive
phase increment, for `app:ch_response:eq:direct-envelope-profile`. -/
theorem smooth_graphOscillation {Φ : Euclidean n → Euclidean n → ℝ}
    (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ)) :
    ContDiff ℝ ∞ (fun p : Euclidean n × (Euclidean n × Euclidean n) ↦
      graphOscillation Φ p.1 p.2.1 p.2.2) :=
  (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    ((hΦ.comp (contDiff_fst.prodMk contDiff_snd.snd)).sub
      (contDiff_snd.fst.inner ℝ contDiff_snd.snd)))).cexp

/-- Joint smoothness of the reverse envelope oscillation from the same
primitive phase increment (`app:ch_response:eq:direct-envelope-profile`). -/
theorem smooth_reverseOscillation {S : Euclidean n → Euclidean n → ℝ}
    {ζ : Euclidean n} {ρ : ℝ}
    (hΦ : ContDiff ℝ ∞ (Function.uncurry (phaseIncrement S ζ ρ))) :
    ContDiff ℝ ∞ (fun p : Euclidean n × (Euclidean n × Euclidean n) ↦
      ReverseDerivative.oscillation S ζ ρ p.1 p.2.1 p.2.2) :=
  (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    ((contDiff_fst.inner ℝ contDiff_snd.snd).sub (hΦ.comp contDiff_snd)))).cexp

end JanetCartan.ResponseTransfer.SpatialRealization
