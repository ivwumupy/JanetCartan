module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.GradedBounds
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.SmoothJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.StrainBounds

/-!
# Ambient reconstruction from smooth root Sobolev profiles

Assembly of `app:ch_response:eq:response-graded-displacement` and
`app:ch_response:eq:response-graded-derivative`. Classical envelope jets are
constructed from root membership, so neither derivative representatives nor
ambient estimates are premises. All spaces use Euclidean Lebesgue measure.
The same literal completed variation also satisfies the strain theorem imported
from `StrainBounds`, once its reduced physical equations and residual bound hold.

The actual producers remain `jc-response-transfer` (smooth reduced/source
profiles and residuals), `jc-current-coefficient-scale` (finite coefficient
budgets), and `jc-compatible-phase-geometry` (phase and geometric hypotheses).
Consumers `jc-response-transfer` and `jc-corrected-atoms` must instantiate those
inputs. This module does not construct a reduced inverse.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
open JanetCartan.IsometricEmbedding.Reconstruction

namespace JanetCartan.IsometricEmbedding.Reconstruction
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- Coordinatewise classical jets for the root Hilbert profile consumed by
`completedVariationComplex_graded_envelopes`, proving the extra representative
premises of the graded helpers from root membership alone
(`app:ch_response:eq:response-reconstruction-grading`). -/
theorem exists_smoothMatrixL2Jets {J : Type*} [Fintype J]
    (f : J → E → ℂ) (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (M : ℕ) (u : PiLp 2 (fun _ : J ↦ L2))
    (hrep : ∀ j, u j =ᵐ[volume] f j) (hu : MemMatrixFourierSobolev (M : ℝ) u) :
    ∃ v : J → List (Fin d) → L2,
      reconstructionJetInput v (fun _ ↦ []) = u ∧
      (∀ j w, w.length ≤ M → v j w =ᵐ[volume] euclideanCoordinateDerivList w (f j)) ∧
      (∀ j w, w.length < M → ∀ i,
        HasEuclideanL2CoordinateDerivative i (v j w) (v j (i :: w))) := by
  classical
  have hj (j : J) := exists_smoothL2Jets (hf j) (hrep j) (hu j)
  choose v hvroot hvrep _ hvderiv _ using hj
  refine ⟨v, ?_, hvrep, fun j w hw i ↦ hvderiv j i w hw⟩
  apply PiLp.ext
  intro j
  exact hvroot j

end JanetCartan.IsometricEmbedding.Reconstruction

namespace JanetCartan.ResponseTransfer
variable {n N : ℕ}
local notation "E" => Euclidean n
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- The displacement and demodulated PHYSICAL derivative of the same completed
variation satisfy `app:ch_response:eq:response-graded-displacement` and
`app:ch_response:eq:response-graded-derivative` from smooth root profiles alone.
The observation cutoff is outside the physical derivative. The finite budgets
are `k + 1` for coefficients and phase gradients and `k + 2` for the two root
profiles; every classical L² jet and its derivative bound is constructed.
Constants depend only on dimensions and `k, P, C, B`, independently of
`A, L, K, ρ`. The tensor profile includes all entries with the Frobenius norm.
The original analytic producer inputs remain explicit. -/
theorem completedVariationComplex_graded_envelopes
    (k : ℕ) (hk : 0 < k) {s : ℝ} (hs : 0 ≤ s) (hsk : s ≤ k)
    (F : E → Euclidean N) {Ω : Set E} (hΩ : IsOpen Ω)
    (φ χ ψ : E → ℝ) (g : E → EuclideanSpace ℂ (Fin n))
    (a : E → Matrix (Fin n) (Fin n) ℂ)
    (hφ : Differentiable ℝ φ) (hg : ContDiff ℝ ∞ g)
    (ha : ∀ j l, ContDiff ℝ ∞ (fun x ↦ a x j l))
    (hψ : ContDiff ℝ ∞ (fun x ↦ (ψ x : ℂ)))
    (hψs : HasCompactSupport (fun x ↦ (ψ x : ℂ)))
    (hsupp : tsupport (fun x ↦ (ψ x : ℂ)) ⊆ Ω)
    (hχ : ContDiffOn ℝ ∞ (fun x ↦ (χ x : ℂ)) Ω)
    (hphase : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ ((partialDeriv φ x i : ℝ) : ℂ)) Ω)
    (hV : ∀ l j, ContDiffOn ℝ ∞ (reconstructionValueEntry F l j) Ω)
    (hD : ∀ l ij, ContDiffOn ℝ ∞ (reconstructionDerivativeEntry F l ij) Ω)
    (hS : ∀ l ij, ContDiffOn ℝ ∞ (reconstructionSourceEntry F l ij) Ω)
    (P C B : ℕ → ℝ) (hP : ∀ r, 0 ≤ P r) (hC : ∀ r, 0 ≤ C r)
    (hB : ∀ r, 0 ≤ B r) {A L K ρ : ℝ}
    (hA : 0 ≤ A) (hL : 1 ≤ L) (hLK : L ≤ K) (hKρ : K ≤ ρ)
    (hψB : ∀ r, r ≤ k → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun y ↦ (ψ y : ℂ)) x‖ ≤ P r * L ^ r)
    (hχB : ∀ r, r ≤ k + 1 → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun y ↦ (χ y : ℂ)) x‖ ≤ C r * L ^ r)
    (hphaseB : ∀ i r, r ≤ k + 1 → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun y ↦ ((partialDeriv φ y i : ℝ) : ℂ)) x‖ ≤ C r * L ^ r)
    (hVB : ∀ l j r, r ≤ k + 1 → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (reconstructionValueEntry F l j) x‖ ≤ C r * L ^ r)
    (hDB : ∀ l ij r, r ≤ k + 1 → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (reconstructionDerivativeEntry F l ij) x‖ ≤ C r * L ^ r)
    (hSB : ∀ l ij r, r ≤ k + 1 → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (reconstructionSourceEntry F l ij) x‖ ≤ C r * L ^ r)
    (ug : PiLp 2 (fun _ : Fin n ↦ L2))
    (ua : PiLp 2 (fun _ : Fin n × Fin n ↦ L2))
    (hgrep : ∀ j, ug j =ᵐ[volume] fun x ↦ g x j)
    (harep : ∀ ij, ua ij =ᵐ[volume] fun x ↦ a x ij.1 ij.2)
    (hgmem : MemMatrixFourierSobolev ((k + 2 : ℕ) : ℝ) ug)
    (hamem : MemMatrixFourierSobolev ((k + 2 : ℕ) : ℝ) ua)
    (hgB : ∀ p, p ≤ k + 2 → matrixFourierSobolevNorm (p : ℝ) ug ≤ B p * A * K ^ p)
    (haB : ∀ p, p ≤ k + 2 → matrixFourierSobolevNorm (p : ℝ) ua ≤ B p * A * K ^ p) :
    ∃ U : PiLp 2 (fun _ : Fin N ↦ L2),
      ∃ D : PiLp 2 (fun _ : Fin n × Fin N ↦ L2),
        (∀ l, U l =ᵐ[volume] fun x ↦
          (waveCarrier (-ρ) φ x • ((ψ x : ℂ) •
            completedVariationComplex F (modulatedWave ρ φ g)
              (fun y ↦ waveCarrier ρ φ y • ((χ y : ℂ) • a y)) x)) l) ∧
        MemMatrixFourierSobolev s U ∧ matrixFourierSobolevNorm s U ≤
          reconstructionDisplacementConstant n N k P C B * A * ρ * K ^ s ∧
        (∀ l, D l =ᵐ[volume] fun x ↦
          (waveCarrier (-ρ) φ x • ((ψ x : ℂ) •
            fderiv ℝ (completedVariationComplex F (modulatedWave ρ φ g)
              (fun y ↦ waveCarrier ρ φ y • ((χ y : ℂ) • a y))) x
              (EuclideanSpace.single l.1 1))) l.2) ∧
        MemMatrixFourierSobolev s D ∧ matrixFourierSobolevNorm s D ≤
          ((n : ℝ) * N * reconstructionPhysicalTermConstant n N k
            (reconstructionDisplacementWord (n := n)) P C (reconstructionDisplacementBudget C)
            (fun _ ↦ B)) * A * ρ ^ 2 * K ^ s := by
  obtain ⟨vg, hvgroot, hvgRep, hvgDeriv⟩ := exists_smoothMatrixL2Jets
    (fun j x ↦ g x j) ((contDiff_piLp 2).mp hg) (k + 2) ug hgrep hgmem
  obtain ⟨va, hvaroot, hvaRep, hvaDeriv⟩ := exists_smoothMatrixL2Jets
    (fun ij x ↦ a x ij.1 ij.2) (fun ij ↦ ha ij.1 ij.2) (k + 2) ua harep hamem
  have hgm : MemMatrixFourierSobolev ((k + 2 : ℕ) : ℝ)
      (reconstructionJetInput vg (fun _ ↦ [])) := by rwa [hvgroot]
  have ham : MemMatrixFourierSobolev ((k + 2 : ℕ) : ℝ)
      (reconstructionJetInput va (fun _ ↦ [])) := by rwa [hvaroot]
  have hgb : ∀ p, p ≤ k + 2 → matrixFourierSobolevNorm (p : ℝ)
      (reconstructionJetInput vg (fun _ ↦ [])) ≤ B p * A * K ^ p := by rwa [hvgroot]
  have hab : ∀ p, p ≤ k + 2 → matrixFourierSobolevNorm (p : ℝ)
      (reconstructionJetInput va (fun _ ↦ [])) ≤ B p * A * K ^ p := by rwa [hvaroot]
  obtain ⟨U, hUrep, hUm, hUb⟩ := completedVariationComplex_displacement_graded k hk hs hsk
    F hΩ φ χ ψ g a hφ (hg.differentiable (by simp)) hψ hψs hsupp hχ hphase hV hD hS
    P C B hP hC hB hA hL hLK hKρ hψB
    (fun r hr ↦ hχB r (by omega)) (fun i r hr ↦ hphaseB i r (by omega))
    (fun l j r hr ↦ hVB l j r (by omega)) (fun l ij r hr ↦ hDB l ij r (by omega))
    (fun l ij r hr ↦ hSB l ij r (by omega)) vg va
    (fun j w hw ↦ hvgDeriv j w (by omega)) (fun j w hw ↦ hvaDeriv j w (by omega))
    (fun j ↦ (hgm j).mono (by push_cast; linarith))
    (fun j ↦ (ham j).mono (by push_cast; linarith))
    (fun p hp ↦ hgb p (by omega)) (fun p hp ↦ hab p (by omega))
    (fun j w hw ↦ hvgRep j w (by omega)) (fun j w hw ↦ hvaRep j w (by omega))
  obtain ⟨D, hDrep, hDm, hDb⟩ := completedVariationComplex_physicalDerivative_graded
    k hk hs hsk F hΩ φ χ ψ g a hφ hg ha hψ hψs hsupp hχ hphase hV hD hS
    P C B hP hC hB hA hL hLK hKρ hψB hχB hphaseB hVB hDB hSB
    vg va hvgDeriv hvaDeriv hgm ham hgb hab hvgRep hvaRep
  exact ⟨U, D, hUrep, hUm, hUb, hDrep, hDm, hDb⟩

/-- A single strain representative satisfies every requested accuracy in
`app:ch_response:eq:response-graded-strain`. The reduced residual belongs to
the fixed completed variation, independently of the requested accuracy. For
output accuracy `q`, the proof uses the producer estimate at `q + k`, paying
the polynomial cost of the actual inverse-Gram/frame coefficients. The
geometric hypotheses, two reduced physical equations, coefficient budget and
arbitrary-accuracy reduced residual profile are the only conditional inputs;
no full-strain identity or estimate is assumed. -/
theorem completedVariationComplex_strain_all_precisions {m : ℕ}
    (k : ℕ) {s : ℝ} (hsk : s ≤ k)
    {F : E → Euclidean N} {u : E → EuclideanSpace ℂ (Fin n)}
    {h : E → Matrix (Fin n) (Fin n) ℂ} {Ω : Set E} (hΩ : IsOpen Ω)
    (hF : ContDiffOn ℝ ∞ F Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (himm : IsImmersionOn F Ω) (hrank : HasFullNormalRankOn F Ω)
    (hhSmooth : ContDiffOn ℝ ∞ h Ω) (hh : ∀ x ∈ Ω, (h x).IsSymm)
    (ψ : E → ℝ) (hψ : Function.support ψ ⊆ Ω)
    (Q : E → Fin m → MetricTensor n)
    (hQ : ∀ x ∈ Ω, LinearIndependent ℝ (Q x))
    (hspan : ∀ x ∈ Ω,
      (Submodule.span ℝ (Set.range (Q x)) : Set (MetricTensor n)) = stressSpace F x)
    (z : E → Fin m → ℂ) (T : (E → Fin m → ℂ) →ₗ[ℂ] (E → Fin m → ℂ))
    (hphysicalRe : ∀ x ∈ Ω, ∀ j, tensorPairing (Q x j)
      (symmCovariantDeriv F (fun y ↦ WithLp.toLp 2 (fun l ↦ (u y l).re)) x) =
      (1 / 2 : ℝ) * tensorPairing (Q x j) (fun i l ↦ (h x i l).re) +
        (T z x j - z x j).re)
    (hphysicalIm : ∀ x ∈ Ω, ∀ j, tensorPairing (Q x j)
      (symmCovariantDeriv F (fun y ↦ WithLp.toLp 2 (fun l ↦ (u y l).im)) x) =
      (1 / 2 : ℝ) * tensorPairing (Q x j) (fun i l ↦ (h x i l).im) +
        (T z x j - z x j).im)
    (hc : ∀ ij j, ContDiff ℝ ∞ (stressResidualCoefficient ψ Q ij j))
    (hcs : ∀ ij j, HasCompactSupport (stressResidualCoefficient ψ Q ij j))
    (C : ℕ → ℝ) (hC : ∀ l, 0 ≤ C l) (B : ℕ → ℝ) {ρ L A : ℝ}
    (hL : 1 ≤ L) (hLρ : L ≤ ρ)
    (hbudget : ∀ ij j l, l ≤ k → ∀ x,
      ‖iteratedFDeriv ℝ l (stressResidualCoefficient ψ Q ij j) x‖ ≤ C l * L ^ l)
    (r : PiLp 2 (fun _ : Fin m ↦ L2))
    (hrrep : ∀ j, r j =ᵐ[volume] fun x ↦ T z x j - z x j)
    (hr : MemMatrixFourierSobolev (k : ℝ) r)
    (hrb : ∀ t : ℕ, matrixFourierSobolevNorm (k : ℝ) r ≤ B t * A * ρ ^ (-(t : ℝ))) :
    ∃ R : PiLp 2 (fun _ : Fin n × Fin n ↦ L2),
      (∀ ij, R ij =ᵐ[volume] fun x ↦
        ((ψ x : ℂ) • (WKB.complexLinearizedMetric F (completedVariationComplex F u h) x -
          h x)) ij.1 ij.2) ∧
      MemMatrixFourierSobolev s R ∧ ∀ q : ℕ, matrixFourierSobolevNorm s R ≤
        ((n : ℝ) * n * m * localizedMultiplierConstant n k *
          ∑ l ∈ Finset.range (k + 1), C (k - l)) * B (q + k) * A * ρ ^ (-(q : ℝ)) := by
  have hprecision (q : ℕ) := completedVariationComplex_strain_graded_precision k hsk
    hΩ hF hu himm hrank hhSmooth hh ψ hψ Q hQ hspan z T hphysicalRe hphysicalIm
    hc hcs C hC hL hLρ hbudget r hrrep hr
    (q := (q : ℝ)) (B := B (q + k)) (by simpa only [Nat.cast_add] using hrb (q + k))
  obtain ⟨R, hRrep, hRm, _⟩ := hprecision 0
  refine ⟨R, hRrep, hRm, fun q ↦ ?_⟩
  obtain ⟨Rq, hRqrep, _, hRqb⟩ := hprecision q
  have heq : Rq = R := by
    apply PiLp.ext
    intro ij
    exact Lp.ext ((hRqrep ij).trans (hRrep ij).symm)
  simpa only [heq] using hRqb

end JanetCartan.ResponseTransfer
