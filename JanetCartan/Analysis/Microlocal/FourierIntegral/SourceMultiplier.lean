module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplier.Segment
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplier.InputCutoff

/-!
# Exact right multiplication by a physical source cutoff

Checked deductions for `app:ch_regular_base:eq:fixed-source-multiplication`:

* `sourceFourierTransform` is the normalized physical Schwartz transform, with
  proved inversion and all absolute polynomial moments.
* `sourceSymbol` and `sourceRemainder` are the literal shift integral and its
  difference from the principal term. Polynomial growth proves convergence.
* `sourceSymbol_eq_principal_add_integral` proves the exact segment FTC formula,
  including both the amplitude derivative and the phase-gradient difference.
* `graphOperator_sourceSymbol_frequencyCutoff` proves the source-first operator
  identity for literal compact frequency regularizations, using proved Fubini
  interchanges and actual Schwartz inversion.
* `graphOperator_tendsto_frequencyCutoff` and
  `graphOperator_sourceSymbol_tendsto_frequencyCutoff` remove those regularizations
  on Schwartz input data using polynomial majorants and Schwartz moments.
* `graphOperator_sourceSymbol_inputCutoff` gives `(T_A m) Π_in = T_b Π_in` on
  Schwartz data. The input cutoff is an actual vector Fourier multiplier in
  physical covectors, with the frequency scaling explicitly proved.

Conditional scope: the supplied phase and amplitude already contain their
angular and low-frequency extensions. Their continuity and polynomial amplitude
growth are explicit operator hypotheses; the FTC identity uses `C¹` regularity.
The fixed smooth input multiplier has temperate growth. Smooth compact source
masks are supplied by `HasCompactSupport.toSchwartzMap`. The phase/geometry
producers and parent consumers must supply these extensions, bounds, and the
cutoff plateau on the stipulated support. No plateau assumption is necessary
for this exact identity. All integrals use Euclidean Lebesgue measure.

The quantitative order-minus-one remainder bounds and extensions of these
operators to Sobolev or distribution spaces are separate constructions.
-/
