module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
import all RiemannMasullo.Ch10_TraceSpectral.Sec1
import all RiemannMasullo.AppB_AnalyticNT.Sec4b

/-! # Trace formula: the Main Theorem

Masullo, §12.5, pp. 519–520. Zeros of the completed Hecke L-functions are listed
through a norm section, as in Theorem B.4.4.7: a quasi-character c = χ|·|^s with
χ trivial on the section has abscissa σ(c) = Re s.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "M(" φ ", " c ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 (φ : BruhatCompactSupport C𝔽).val c
local notation "twist(" χ ", " s ")" => ideleClassNormTwist (F := F) χ s
local notation "ord(" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "interiorZeros(" τ ", " α ")" =>
  {z : {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
    0 < ord(z.1.val, z.2) ∧ |z.2.re - 1 / 2| < α}
local notation "zeroTerm(" φ ", " z ")" =>
  ((ord((z).val.1.val, (z).val.2) : ℤ) : ℂ) * M(φ, twist((z).val.1.val, (z).val.2 - 1 / 2))
local notation "classVolume" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "archTest" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest" => ((v : V) → BruhatCompactSupport (v.adicCompletion F)ˣ)
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "finiteVolume(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal
local notation "finiteTerm(" v ", " b ")" =>
  ((Real.log ((v : V).asIdeal.absNorm : ℝ) / finiteVolume(v) : ℝ) : ℂ) *
    finiteConnesWeilPrincipalValue v 1 b

local notation "exteriorZeros(" τ ", " α ")" =>
  {z : {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
    0 < ord(z.1.val, z.2) ∧ α ≤ |z.2.re - 1 / 2|}

local notation "traceIdentity(" τ ", " φ ", " α ")" =>
  (∃ (a : archTest) (b : finiteTest),
      (∀ (w : InfinitePlace F) (u : w.Completionˣ), (a w).val u = (φ).val (archClass(w) u)) ∧
      (∀ (v : V) (u : (v.adicCompletion F)ˣ), (b v).val u = (φ).val (finiteClass(v) u)) ∧
      Summable (fun v : V ↦ finiteTerm(v, b v)) ∧
      HasSum (fun z : interiorZeros(τ, α) ↦ zeroTerm(φ, z))
        (M(φ, twist(1, 1 / 2)) + M(φ, twist(1, -1 / 2)) -
          classVolume * ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
            ∑' v : V, finiteTerm(v, b v))))

-- Page 519 introduces tests with φ(1) = 0 and states the theorem for φ(C_F¹) = 0.
-- TODO(paper-gap): Page 520 leaves χ free. Theorem 11.3.2.1 also requires
-- support above norm one. In (11.3.1.4), the signed differences sum to the
-- S-local restriction minus the original kernel. A quotient lift and comparison
-- of the separate shell integrals are missing (ERRATA I292).
-- TODO(paper-gap): Theorem 12.4.1.1 divides by the S-local norm-one volume.
-- Section 12.3 lacks the comparison of this local limit with the global Haar
-- diagonal and the two polar Mellin terms (ERRATA M25).

/-- Paper: Theorem 12.5.1.1, pp. 519–520. For a test vanishing on the norm-one
classes, the zero terms omitted by a positive-width open strip sum to zero.
Gap: The global to S-local comparison on p. 520 must account for every omitted
zero, including zeros on the edges. The all-zero identity of Theorem B.4.4.7
alone gives no such cancellation. -/
theorem traceFormula_exteriorZeros (τ : ℝ≥0ˣ →ₜ* C𝔽) (_hτ : RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (_hφ : ∀ g : C₁, φ.val g = 0) {α : ℝ} (_hα : 0 < α) :
    HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) 0 := by sorry

private theorem traceFormula_of_exteriorZeros_mul_congr {a b c d : ℂ} (h1 : a = b)
    (h2 : c = d) : a * c = b * d := by
  rw [h1, h2]

private theorem traceFormula_of_exteriorZeros_vol :
    (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ) ≠ 0 := by
  have hvol := normOneIdeleClassTamagawaMeasure_volume (F := F)
  have hc0 : normOneIdeleClassTamagawaMeasure F univ ≠ 0 := by
    rw [hvol, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have := NumberField.Units.regulator_pos F
    have := NumberField.classNumber_pos F
    have := NumberField.Units.torsionOrder_pos F
    have : (0 : ℝ) < Real.sqrt (Int.natAbs (NumberField.discr F) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero F))
    positivity
  have hct : normOneIdeleClassTamagawaMeasure F univ ≠ ⊤ := by
    rw [hvol]; exact ENNReal.ofReal_ne_top
  exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨hc0, hct⟩)

private theorem traceFormula_of_exteriorZeros_cpow (p a x s : ℂ) (hx : x ≠ 0) :
    p * (a * x ^ s) * x ^ (-1 / 2 : ℂ) = p * (a * x ^ (s - 1 / 2)) := by
  rw [sub_eq_add_neg, Complex.cpow_add _ _ hx]
  ring_nf

private theorem traceFormula_of_exteriorZeros_split {X : Type*} (G : X → ℂ) (Z E I : Set X)
    {T T' : ℂ}
    (hEZ : E ⊆ Z) (hI : ∀ p, p ∈ I ↔ p ∈ Z ∧ p ∉ E) (hT : T = T')
    (hZ : HasSum (fun z : Z ↦ G z) T) (hE : HasSum (fun z : E ↦ G z) 0) :
    HasSum (fun z : I ↦ G z) T' := by
  replace hZ := (hasSum_subtype_iff_indicator (f := G) (s := Z)).mp hZ
  replace hE := (hasSum_subtype_iff_indicator (f := G) (s := E)).mp hE
  refine (hasSum_subtype_iff_indicator (f := G) (s := I)).mpr ?_
  have h : I.indicator G = Z.indicator G - E.indicator G := by
    funext p
    by_cases hp : p ∈ E
    · simp [Set.indicator_of_mem hp, Set.indicator_of_mem (hEZ hp),
        Set.indicator_of_notMem (fun h ↦ ((hI p).mp h).2 hp)]
    · by_cases hz : p ∈ Z
      · simp [Set.indicator_of_mem ((hI p).mpr ⟨hz, hp⟩), Set.indicator_of_mem hz,
          Set.indicator_of_notMem hp]
      · simp [Set.indicator_of_notMem hz, Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (fun h ↦ hz ((hI p).mp h).1)]
  rw [h, ← hT, ← sub_zero T]
  exact hZ.sub hE

private theorem traceFormula_of_exteriorZeros_hasSum_congr {ι : Type*} {f g : ι → ℂ} {a : ℂ}
    (h : HasSum f a) (hfg : ∀ i, f i = g i) : HasSum g a :=
  (funext hfg) ▸ h

private theorem traceFormula_of_exteriorZeros_val {v x p A Fs P1 P2 M1 M2 A' F' : ℂ}
    (hv : v ≠ 0) (hx : x = p - A - Fs) (hp : p = (P1 + P2) / v) (hA : A = A') (hF : Fs = F')
    (h1 : M1 = P2) (h2 : M2 = P1) :
    v * x = M1 + M2 - v * (A' + F') := by
  subst hx hp hA hF h1 h2
  field_simp
  ring

private theorem traceFormula_of_exteriorZeros_one (p a x : ℂ) (ha : a = 1) :
    p * (a * x) = p * x := by
  rw [ha, one_mul]

private theorem traceFormula_of_exteriorZeros_mul_div (v m I : ℂ) (hv : v ≠ 0) :
    v * (m / v * I) = m * I := by
  field_simp

/-- Paper: Theorem B.4.4.7, p. 623, applied to Theorem 12.5.1.1, pp. 519–520.
Evaluating the full explicit formula at a test and removing a zero subseries of
sum zero gives the strip identity. -/
theorem traceFormula_of_exteriorZeros (τ : ℝ≥0ˣ →ₜ* C𝔽) (_hτ : RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (α : ℝ)
    (_hTail : HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) 0) :
    traceIdentity(τ, φ, α) := by
  have h := idelicExplicitFormula τ _hτ
  obtain ⟨spectral, poles, arch, finite, hspec, hpoles, harch, hfin, _, hsupp, hsum, hHas⟩ := h
  choose a ha haPV using fun w ↦ harch w φ
  choose b hb hbPV using fun v ↦ hfin v φ
  let E : StrongDual ℂ (BruhatCompactSupport C𝔽) →+ ℂ :=
    { toFun := fun L ↦ L φ, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  have hEc : Continuous E := continuous_eval_const φ
  have hT := hsum.hasSum.map E hEc
  have hS := hHas.map E hEc
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · refine (summable_of_ne_finset_zero (s := (hsupp φ).toFinset) fun v hv ↦ ?_).congr
      fun v ↦ hbPV v
    by_contra hne
    exact hv ((hsupp φ).mem_toFinset.mpr hne)
  have hvol : (classVolume : ℂ) ≠ 0 := traceFormula_of_exteriorZeros_vol
  have hM (c : QuasiCharacter C𝔽) : M(φ, c) = ∫ g, φ.val g * c g ∂μ𝔽 := by
    unfold modulatedFourierMellin
    rw [Set.indicator_of_mem (by simp [relativeVerticalStrip])]
  let X := {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ
  let G : X → ℂ := fun p ↦
    ((ord(p.1.val, p.2) : ℤ) : ℂ) * M(φ, twist(p.1.val, p.2 - 1 / 2))
  let Z : Set X :=
    {p | 0 < MeromorphicOn.divisor (explicitFormulaCompletedHeckeL p.1.val) univ p.2}
  let Ext : Set X := {p | 0 < ord(p.1.val, p.2) ∧ α ≤ |p.2.re - 1 / 2|}
  let Int : Set X := {p | 0 < ord(p.1.val, p.2) ∧ |p.2.re - 1 / 2| < α}
  have hfun (z : Z) : (classVolume : ℂ) * E (spectral z) = G z.val := by
    change (classVolume : ℂ) * spectral z φ = _
    rw [hspec z φ]
    refine (traceFormula_of_exteriorZeros_mul_div _ _ _ hvol).trans
      (traceFormula_of_exteriorZeros_mul_congr rfl ((integral_congr_ae
        (Filter.Eventually.of_forall fun g ↦ ?_)).trans (hM _).symm))
    have hn : ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    change φ.val g * (_ * ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ z.val.2) *
        ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ (-1 / 2 : ℂ) =
      φ.val g * (_ * ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ (z.val.2 - 1 / 2))
    exact traceFormula_of_exteriorZeros_cpow _ _ _ _ hn
  have hZ : HasSum (fun z : Z ↦ G z.val) ((classVolume : ℂ) *
      E (poles - (∑ w, arch w) - (∑' v, finite v))) :=
    traceFormula_of_exteriorZeros_hasSum_congr (hS.mul_left (classVolume : ℂ)) hfun
  refine traceFormula_of_exteriorZeros_split G Z Ext Int (fun p hp ↦ hp.1)
    (fun p ↦ ⟨fun h ↦ ⟨h.1, fun h' ↦ (not_le.mpr h.2) h'.2⟩,
      fun h ↦ ⟨h.1, lt_of_not_ge fun h' ↦ h.2 ⟨h.1, h'⟩⟩⟩) ?_ hZ _hTail
  have hone (r : ℂ) : M(φ, twist(1, r)) = ∫ g, φ.val g *
      ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ r ∂μ𝔽 := by
    refine (hM _).trans (integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_))
    change φ.val g * (_ * ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ r) =
      φ.val g * ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ r
    exact traceFormula_of_exteriorZeros_one _ _ _ rfl
  have hx : E (poles - (∑ w, arch w) - (∑' v, finite v)) =
      E poles - E (∑ w, arch w) - E (∑' v, finite v) :=
    (map_sub E _ _).trans (congrArg (· - E _) (map_sub E _ _))
  refine traceFormula_of_exteriorZeros_val hvol hx (hpoles φ) ?_ ?_ (hone _) (hone _)
  · exact (map_sum E arch Finset.univ).trans (Finset.sum_congr rfl fun w _ ↦ haPV w)
  · exact hT.tsum_eq.symm.trans (tsum_congr fun v ↦ hbPV v)

/-- Paper: Theorem 12.5.1.1, pp. 519–520. For compactly supported Bruhat tests
vanishing on the norm-one classes, the pole terms minus the interior zero sum
equal the global norm-one volume times the sum of the local principal values.
Deviation: The half-width is positive as in §1.8.4, p. 53. The global volume
and the normalized complex denominator ‖1 − u‖² follow Theorem B.4.4.7 and
(12.4.1.26). The all-width conclusion uses `traceFormula_exteriorZeros`. -/
theorem traceFormula (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0) {α : ℝ} (hα : 0 < α) :
    traceIdentity(τ, φ, α) :=
  traceFormula_of_exteriorZeros τ hτ φ α (traceFormula_exteriorZeros τ hτ φ hφ hα)

section SmoothenedDiagonal

local notation "hs₁(" hs ")" => (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hs)
local notation "hs₀(" hs ")" => (le_of_lt (zero_lt_one.trans hs₁(hs)))
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "stripTensorExists(" hα ", " hs ", " φ ")" =>
  (∃ K, sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) K =
    (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ (hStrip(hα)) hs₀(hs) φ).comp
      (spectralProjection (F := F) (1 / 2) hα hs₀(hs)))

local notation "geomDiagonal(" hα ", " hs ", " φ ", " hK ", " U ")" =>
  (fun x : C𝔽 ↦ dSequenceKernelSmoothening μ𝔽 U
    (globalStripGeometricKernel (F := F) (1 / 2) hα hs₁(hs) φ hK) (x, x))
local notation "quotientTrace(" hα ", " hs ", " φ ")" =>
  (hilbertTrace (H := spectralSobolevQuotient F (1 / 2) (hStrip(hα)) hs₀(hs))
    ⟨spectralConvolution (F := F) (1 / 2) (hStrip(hα)) hs₀(hs) φ,
      spectralStripConvolution_nuclear (F := F) (1 / 2) hα hs₁(hs) φ⟩)

/-- Paper: (12.5.1.4), p. 520. The smoothened geometric diagonal is
Haar-integrable and its integral is minus the strip quotient trace.
Gap: Theorem 10.4.2.8 gives a cutoff trace limit. Identifying it with this
Haar diagonal requires the input Sobolev weight and justification for
removing the cutoff (ERRATA I341 and I351).
Deviation: Definition 10.4.3.7 uses the tensor for convolution after projection.
The right side is the trace computed by `spectralStripConvolution_trace`. It
counts the closed strip with `spectralStripMultiplicity`. When the two edges
contain no zeros this recovers the interior sum in (12.5.1.4). -/
theorem integral_smoothenedStripGeometricKernel_diagonal (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ g : C₁, φ.val g = 0) {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s)
    (hK : stripTensorExists(hα.le, hs, φ))
    (U : ℕ → Set C𝔽) (_hU : IsDPrimeSequence μ𝔽 U) (_hBorel : ∀ n, MeasurableSet (U n)) :
    Integrable geomDiagonal(hα.le, hs, φ, hK, U) μ𝔽 ∧
      (∫ x, geomDiagonal(hα.le, hs, φ, hK, U) x ∂μ𝔽) = -quotientTrace(hα.le, hs, φ) := by sorry

end SmoothenedDiagonal

end RiemannMasullo
