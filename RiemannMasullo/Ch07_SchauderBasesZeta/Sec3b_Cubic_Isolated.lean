module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b_IsotypicAverages
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.FieldTheory.Galois.Basic
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Analysis.Complex.IsIntegral
import Mathlib.Data.Fintype.EquivFin
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-! # Repeated primary poles in cubic fields, from the Four Exponentials Conjecture

Theorem 7.3.3.4, pp. 360–363, with p. 349 (issue #7336). In Lean the theorem rests on the
open statement `sLocalPWOrbital_bases_bounded_interpolation_laurent_other_prime_shift_minima`
of `Sec3b.lean`, which assumes that the field has degree at least three and that the
character has a repeated primary pole. This file shows that in degree three that
hypothesis cannot hold if the Four Exponentials Conjecture holds, so that the open
statement is then only open in degree at least four.

The argument is duuren's, in the comment of 24 November 2026 on issue #7336
(comment 7145386474, "Degree 3, the first case left after #7413").
A repeated pole at two places above one rational prime gives an element `a` of the field
whose valuation support is those two places, and on whose archimedean diagonal the
character takes a root of unity; the global units have the same property. In degree three
the norm-one archimedean ideles modulo units form a two-dimensional torus, and the
condition becomes a singular `2 × 2` matrix of logarithms of algebraic numbers, which the
conjecture excludes. Two subcases need no conjecture: a purely angular character of a complex cubic
field, and a totally real character whose exponents point in a rational direction.

The first part, which produces `a` from the pair of poles, is adapted from dyknapp's
`Sec3b_PrimitiveQuartic_Isolated.lean` (pull request #7479), where it serves the quartic
case.

Nothing imports this file, and nothing outside it may build on it.
-/

noncomputable section

namespace RiemannMasullo.Isolated

open Function NumberField IsDedekindDomain Topology
open scoped Classical ComplexConjugate NNReal Pointwise RestrictedProduct WithZero

/-! ### Finite ideles attached to a pair of poles -/

section

variable (F : Type*) [Field F] [NumberField F]

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N₁" => MonoidHom.ker (ideleNorm F)
local notation "atInfinity" =>
  Units.map (RingHom.toMonoidHom (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
local notation "fromInfinity" =>
  Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
local notation "principal" => IdeleGroup.unitEmbedding (𝓞 F) F
local notation "integralUnits" =>
  MonoidHom.range (Units.map (RingHom.toMonoidHom (Subring.subtype (integralAdelesOutside F ∅))))

/-- A power of a norm-one idele is a principal idele times an integral unit idele. -/
theorem cubic_principalize_ratio (g : N₁) :
    ∃ n : ℕ, 0 < n ∧ ∃ a : Fˣ, ∃ u : 𝕀[F],
      u ∈ integralUnits ∧ g.val ^ n = principal a * u := by
  obtain ⟨e, _⟩ := (picard_uniformization F ∅).2.2.2
  let : Finite (CommRing.Pic (𝓞 F)) :=
    Finite.of_equiv (ClassGroup (𝓞 F)) (ClassGroup.equivPic (𝓞 F)).toEquiv
  obtain ⟨n, hn, he⟩ := (isOfFinOrder_of_finite (e (QuotientGroup.mk g))).exists_pow_eq_one
  have hg : QuotientGroup.mk (g ^ n) = 1 := e.injective <| by
    change e ((QuotientGroup.mk' _) (g ^ n)) = e 1
    rw [map_pow, map_pow, map_one]
    exact he
  have hsup := (QuotientGroup.eq_one_iff (g ^ n)).mp hg
  change g.val ^ n ∈ (IdeleGroup.principalSubgroup (𝓞 F) F ⊔ integralUnits) at hsup
  obtain ⟨_, ⟨a, rfl⟩, u, hu, h⟩ := Subgroup.mem_sup.mp hsup
  exact ⟨n, hn, a, u, hu, h.symm⟩

/-- The principal generator of the power has exactly the same finite support. -/
theorem cubic_principalize_support {g : 𝕀[F]} {n : ℕ} (hn : 0 < n)
    {a : Fˣ} {u : 𝕀[F]} (hu : u ∈ integralUnits) (h : g ^ n = principal a * u)
    (v : Primes(F)) :
    (v.valuation F (a : F) = 1) ↔ Valued.v (g.val.2 v) = (1 : ℤᵐ⁰) := by
  let eval := (RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ w.adicCompletion F) v).comp
    (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let f := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).toMonoidWithZeroHom.toMonoidHom.comp
    ((Units.coeHom (v.adicCompletion F)).comp (Units.map eval.toMonoidHom))
  have he := congrArg f h
  rw [map_pow, map_mul] at he
  have hu' : f u = 1 :=
    (mem_integralIdeleRange_iff F u).mp hu v
  have ha : f (principal a) = v.valuation F (a : F) := by
    change Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = _
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (a : F)
  rw [hu', mul_one, ha] at he
  rw [← he]
  exact pow_eq_one_iff_of_nonneg zero_le hn.ne'

local notation "C₁" => MonoidHom.ker (ideleClassNorm F)

/-- Passing a norm-one idele to its global idele class. -/
def cubicNormOneClass : N₁ →* C₁ :=
  ((QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)).comp
    (Subgroup.subtype N₁)).codRestrict
    _ fun g ↦ g.property

/-- Giving a norm-one archimedean idele finite components equal to one. -/
def cubicArchIdele : (infiniteIdeleNorm F).ker →* N₁ :=
  ((fromInfinity).comp (infiniteIdeleNorm F).ker.subtype).codRestrict _ fun a ↦
    (infiniteIdeleNorm_eq_global F a.val).symm.trans a.property

/-- The archimedean projection of an integral, norm-one idele has norm one. -/
theorem cubic_infiniteNorm_of_integral (u : 𝕀[F])
    (hu : u ∈ integralUnits) (hn : ideleNorm F u = 1) :
    infiniteIdeleNorm F (atInfinity u) = 1 := by
  have hfin : (∏ᶠ v : Primes(F), ‖u.val.2 v‖) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v ↦ Valued.toNormedField.norm_eq_one_iff.mpr
      ((mem_integralIdeleRange_iff F u).mp hu v)
  rw [infiniteIdeleNorm_eq_global, ← hn]
  apply Units.ext
  apply NNReal.coe_injective
  rw [((ideleNorm_spec F).1 (fromInfinity (atInfinity u))).2, ((ideleNorm_spec F).1 u).2, hfin]
  have h₁ (v : Primes(F)) : (fromInfinity (atInfinity u)).val.2 v = 1 := rfl
  simp only [h₁, norm_one, finprod_one]
  rfl

/-- The units supported at finite places have torsion image under any norm-one circle character. -/
theorem cubic_finite_unit_character_exponent (ω : PontryaginDual C₁) :
    ∃ n : ℕ, 0 < n ∧ ∀ (u : N₁), u.val ∈ integralUnits → atInfinity u.val = 1 →
      ω (cubicNormOneClass F u) ^ n = 1 := by
  let U := (v : Primes(F)) → (v.adicCompletionIntegers F).units
  have hC (v : Primes(F)) : CompactSpace (v.adicCompletionIntegers F).units :=
    isCompact_iff_compactSpace.mp
      (Submonoid.units_isCompact
        (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)))
  have hTD (v : Primes(F)) : TotallyDisconnectedSpace (v.adicCompletion F)ˣ :=
    ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  have : CompactSpace U := inferInstanceAs (CompactSpace (∀ v : Primes(F), _))
  have : TotallyDisconnectedSpace U :=
    inferInstanceAs (TotallyDisconnectedSpace (∀ v : Primes(F), _))
  obtain ⟨e, he⟩ := (ideleGroup_topology F).2.2.2.1
  let s : U →* Πʳ v : Primes(F), [(v.adicCompletion F)ˣ, (v.adicCompletionIntegers F).units] :=
    { toFun := RestrictedProduct.structureMap (fun v : Primes(F) ↦ (v.adicCompletion F)ˣ)
        (fun v : Primes(F) ↦ ((v.adicCompletionIntegers F).units : Set (v.adicCompletion F)ˣ))
        Filter.cofinite
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hs : Continuous s := by
    exact RestrictedProduct.isEmbedding_structureMap.continuous
  let raw : U →* 𝕀[F] := e.symm.toMonoidHom.comp ((MonoidHom.inr _ _).comp s)
  have hraw (x : U) : e (raw x) = (1, s x) := e.apply_symm_apply _
  have harch (x : U) (v : InfinitePlace F) : (raw x).val.1 v = 1 := by
    rw [← (he _).1 v, hraw]
    rfl
  have hfin (x : U) (v : Primes(F)) : (raw x).val.2 v = (x v).val.val := by
    rw [← (he _).2 v, hraw]
    rfl
  have hnorm (x : U) : ideleNorm F (raw x) = 1 := by
    apply Units.ext
    apply NNReal.coe_injective
    rw [((ideleNorm_spec F).1 (raw x)).2]
    have hlocal (v : Primes(F)) : ‖(raw x).val.2 v‖ = 1 := by
      rw [hfin]
      exact Valued.toNormedField.norm_eq_one_iff.mpr
        (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp (x v).property)
    simp only [harch, hlocal, norm_one, one_pow, Finset.prod_const_one, finprod_one, mul_one,
      Units.val_one, NNReal.coe_one]
  let i : U →* N₁ := raw.codRestrict _ hnorm
  have hi : Continuous i := (e.symm.continuous.comp (continuous_const.prodMk hs)).subtype_mk _
  let q := cubicNormOneClass F
  have hq : Continuous q :=
    (QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _
  let ψ : PontryaginDual U := ⟨ω.toMonoidHom.comp (q.comp i), ω.continuous.comp (hq.comp hi)⟩
  have hopen := (Circle.isOpen_centeredArc (Real.pi / 2)).preimage ψ.continuous
  have hone : (1 : U) ∈ ψ ⁻¹' Circle.centeredArc (Real.pi / 2) := by
    change ψ 1 ∈ Circle.centeredArc (Real.pi / 2)
    rw [map_one, Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  obtain ⟨H, _, hH⟩ := exists_compact_openSubgroup_sub_mem_nhds (hopen.mem_nhds hone)
  have hker (x : U) (hx : x ∈ H) : ψ x = 1 := by
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro n _
    rw [← map_pow]
    exact hH (H.pow_mem hx n)
  refine ⟨H.toSubgroup.index, Nat.card_pos, ?_⟩
  intro u hu harchu
  let x : U := fun v ↦ ⟨(e u.val).2 v, by
    apply HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
    rw [(he _).2 v]
    exact (mem_integralIdeleRange_iff F u.val).mp hu v⟩
  have hxu : i x = u := by
    apply Subtype.ext
    apply e.injective
    change e (raw x) = e u.val
    rw [hraw]
    apply Prod.ext
    · funext v
      apply Units.ext
      rw [(he _).1 v]
      exact congrArg (fun z : 𝕀∞ ↦ z.val v) harchu.symm
    · ext v
      rfl
  rw [← hxu]
  change ψ x ^ H.toSubgroup.index = 1
  rw [← map_pow]
  exact hker _ (H.toSubgroup.pow_index_mem x)

/-- A norm-one character trivial on a purely finite idele has torsion value on
  the archimedean projection of a generator principalizing that idele. -/
theorem cubic_principalize_character (ω : PontryaginDual C₁) (g : N₁)
    (hg : ω (cubicNormOneClass F g) = 1) (harchg : atInfinity g.val = 1) :
    ∃ a : Fˣ, ∃ b : (infiniteIdeleNorm F).ker, b.val = atInfinity (principal a) ∧
      IsOfFinOrder (ω (cubicNormOneClass F (cubicArchIdele F b))) ∧
      ∀ v : Primes(F), v.valuation F (a : F) = 1 ↔ Valued.v (g.val.val.2 v) = (1 : ℤᵐ⁰) := by
  obtain ⟨n, hn, a, u, hu, he⟩ := cubic_principalize_ratio F g
  let N := (ideleNorm F).ker
  let p : Fˣ →* N := (principal).codRestrict _ fun x ↦ (ideleNorm_spec F).2 (Set.mem_range_self x)
  have hnu : ideleNorm F u = 1 := by
    have h := congrArg (ideleNorm F) he
    rw [map_pow, map_mul, show ideleNorm F (principal a) = 1 from (p a).property,
      one_mul, g.property, one_pow] at h
    exact h.symm
  let U : N := ⟨u, hnu⟩
  have hep : g ^ n = p a * U := Subtype.ext he
  let q := cubicNormOneClass F
  have hqa : q (p a) = 1 := by
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (principal a)).mpr (Set.mem_range_self a)
  have hωu : ω (q U) = 1 := by
    have h := congrArg (fun x : N ↦ ω (q x)) hep
    change (ω.toMonoidHom.comp q) (g ^ n) = (ω.toMonoidHom.comp q) (p a * U) at h
    rw [map_pow, map_mul] at h
    change ω (q g) ^ n = ω (q (p a)) * ω (q U) at h
    rw [hg, one_pow, hqa, map_one, one_mul] at h
    exact h.symm
  have harch : atInfinity (principal a) * atInfinity u = 1 := by
    have h := congrArg (atInfinity) he
    rw [map_pow, map_mul, harchg, one_pow] at h
    exact h.symm
  let B : (infiniteIdeleNorm F).ker :=
    ⟨atInfinity u, cubic_infiniteNorm_of_integral F u hu hnu⟩
  have hBa : (B⁻¹).val = atInfinity (principal a) := (eq_inv_of_mul_eq_one_left harch).symm
  let ins := cubicArchIdele F
  let V := U / ins B
  have hUV : U = V * ins B := (div_mul_cancel U (ins B)).symm
  have hV : V.val ∈ integralUnits := by
    apply (mem_integralIdeleRange_iff F V.val).mpr
    intro v
    let ev := Units.map ((RestrictedProduct.evalRingHom
      (fun w : Primes(F) ↦ w.adicCompletion F) v).comp
      (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))).toMonoidHom
    have heval : ev (ins B).val = 1 := Units.ext rfl
    change Valued.v (ev (u / (ins B).val)).val = 1
    rw [map_div, heval, div_one]
    exact (mem_integralIdeleRange_iff F u).mp hu v
  have hVarch : atInfinity V.val = 1 := by
    change atInfinity (u / (ins B).val) = 1
    rw [map_div]
    exact div_self' (atInfinity u)
  obtain ⟨m, hm, hωm⟩ := cubic_finite_unit_character_exponent F ω
  have hωB : ω (q (ins B⁻¹)) = ω (q V) := by
    have h := congrArg (fun x : N ↦ ω (q x)) hUV
    change (ω.toMonoidHom.comp q) U = (ω.toMonoidHom.comp q) (V * ins B) at h
    rw [map_mul] at h
    change ω (q U) = ω (q V) * ω (q (ins B)) at h
    rw [hωu] at h
    rw [map_inv, map_inv, map_inv, eq_inv_of_mul_eq_one_left h.symm]
  refine ⟨a, B⁻¹, hBa, isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, ?_⟩,
    cubic_principalize_support F hn hu he⟩
  rw [hωB]
  exact hωm V hV hVarch

variable {S : Finset (Primes(F))}

/-- At a finite pole the local character is one on the chosen uniformizer. -/
private theorem cubic_pole_uniformizer
    (c : QuasiCharacter (SIdeleQuotient F S)) (w : S) (hw : w ∈ sLocalFinitePolePlaces c) :
    ∃ u : (w.val.adicCompletion F)ˣ,
      ‖u.val‖ = (w.val.asIdeal.absNorm : ℝ)⁻¹ ∧ sLocalFiniteRestriction w c u = 1 := by
  let π := (Valued.v : Valuation (w.val.adicCompletion F) ℤᵐ⁰)
    |>.exists_isUniformizer_of_isCyclic_of_nontrivial
  let u : (w.val.adicCompletion F)ˣ := Units.mk0 π.choose π.choose_spec.ne_zero
  refine ⟨u, norm_uniformizer_adicCompletion w.val _ π.choose_spec, ?_⟩
  have hzero : finiteLocalEulerFactor w.val (sLocalFiniteRestriction w c) = 0 := by
    have hm := (sLocalPrincipalPartCoeff_leading_formula_fin_factor c w).1
    have ho := (Finset.mem_filter.mp hw).2
    by_contra h
    have hz : quasiCharacterNormTwist (sIdeleQuotientNorm F S)
        (isProperMap_sIdeleQuotientNorm F S).continuous c 0 = c := by
      ext1 x
      exact (congrArg (c x * ·) (Complex.cpow_zero _)).trans (mul_one _)
    exact ho.ne (hm.meromorphicOrderAt_eq_zero_iff.mpr (by simpa only [hz] using h))
  unfold finiteLocalEulerFactor at hzero
  split at hzero
  · change (1 - sLocalFiniteRestriction w c u)⁻¹ = 0 at hzero
    exact (sub_eq_zero.mp (inv_eq_zero.mp hzero)).symm
  · exact False.elim (one_ne_zero hzero)

/-- Two distinct finite poles over one rational prime give a character-trivial norm-one
idele with exactly those two places in its valuation support. -/
theorem cubic_pole_ratio (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside ω S) (p : HeightOneSpectrum (𝓞 ℚ))
    (c : QuasiCharacter (SIdeleQuotient F S))
    (hc : ∀ x : (sIdeleQuotientNorm F S).ker,
      c x.val = (sLocalNormOneCharacter S ω hω x : ℂ))
    (v w : S) (hne : v ≠ w) (hvp : v.val ∈ sLocalPrimaryPlaces S p)
    (hwp : w.val ∈ sLocalPrimaryPlaces S p)
    (hv : v ∈ sLocalFinitePolePlaces c) (hw : w ∈ sLocalFinitePolePlaces c) :
    ∃ g : N₁, ω (cubicNormOneClass F g) = 1 ∧ atInfinity g.val = 1 ∧
      ∀ x : Primes(F), Valued.v (g.val.val.2 x) ≠ (1 : ℤᵐ⁰) ↔ x = v.val ∨ x = w.val := by
  classical
  let f (i : S) := i.val.asIdeal.inertiaDeg (𝓞 ℚ)
  have residue (i : S) (hi : i.val ∈ sLocalPrimaryPlaces S p) :
      p.asIdeal.absNorm ^ f i = i.val.asIdeal.absNorm ∧ 0 < f i := by
    have e := ((mem_sLocalPrimaryPlaces p i.val).mp hi).2
    let : i.val.asIdeal.IsPrime := i.val.isPrime
    let : i.val.asIdeal.LiesOver p.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal e).symm⟩
    have h := Ideal.absNorm_pow_inertiaDeg p.asIdeal i.val.asIdeal
    refine ⟨h, Nat.pos_of_ne_zero fun h0 ↦ ?_⟩
    change p.asIdeal.absNorm ^ f i = i.val.asIdeal.absNorm at h
    rw [h0, pow_zero] at h
    exact (HeightOneSpectrum.one_lt_absNorm i.val).ne h
  obtain ⟨u, hu, hzu⟩ := cubic_pole_uniformizer F c v hv
  obtain ⟨t, ht, hzt⟩ := cubic_pole_uniformizer F c w hw
  let q : (SAdeleRing F S)ˣ →* SIdeleQuotient F S := QuotientGroup.mk' _
  let ins (i : S) (z : (i.val.adicCompletion F)ˣ) : (SAdeleRing F S)ˣ :=
    (ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) ((s : S) → s.val.adicCompletion F)).symm
      (1, ContinuousMulEquiv.piUnits.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) i z))
  have modIns (i : S) (z : (i.val.adicCompletion F)ˣ) :
      ((sIdeleQuotientNorm F S (q (ins i z))).val : ℝ) = ‖z.val‖ := by
    have h := sLocalFiniteRestriction_norm (F := F) (S := S) i z
    change ((1 : PontryaginDual (SIdeleQuotient F S)) (q (ins i z)) : ℂ) *
      (((sIdeleQuotientNorm F S (q (ins i z))).val : ℝ) : ℂ) ^ (1 : ℂ) = _ at h
    simpa using h
  let g := ins v u ^ f w / ins w t ^ f v
  have hn : sIdeleQuotientNorm F S (q g) = 1 := by
    dsimp only [g]
    rw [map_div, map_div, div_eq_one, map_pow, map_pow, map_pow, map_pow]
    apply Units.ext
    apply NNReal.eq
    change ((sIdeleQuotientNorm F S (q (ins v u))).val : ℝ) ^ f w =
      ((sIdeleQuotientNorm F S (q (ins w t))).val : ℝ) ^ f v
    rw [modIns, modIns, hu, ht, inv_pow, inv_pow, ← Nat.cast_pow, ← Nat.cast_pow,
      ← (residue v hvp).1, ← (residue w hwp).1, ← pow_mul, ← pow_mul, Nat.mul_comm]
  let a := sIdeleInsertion F S g
  have ha : ideleNorm F a = 1 := by
    rw [ideleNorm_sIdeleInsertion, ← sIdeleQuotientNorm_mk]
    exact hn
  let A : N₁ := ⟨a, ha⟩
  refine ⟨A, ?_, ?_, ?_⟩
  · have hχ : (sLocalNormOneCharacter S ω hω ⟨q g, hn⟩ : ℂ) = 1 := by
      rw [← hc]
      change c (q (ins v u ^ f w / ins w t ^ f v)) = 1
      rw [map_div, map_div, map_pow, map_pow, map_pow, map_pow,
        show c (q (ins v u)) = 1 from hzu, show c (q (ins w t)) = 1 from hzt,
        one_pow, one_pow, div_one]
    obtain ⟨d, hd⟩ := hω
    apply Circle.ext
    have hx := sLocalNormOneCharacter_eq_sIdeleRestriction ω d hd ⟨q g, hn⟩
    rw [hχ] at hx
    change 1 = sIdeleRestriction F S d (QuotientGroup.mk g) at hx
    rw [sIdeleRestriction_mk] at hx
    exact (hd (cubicNormOneClass F A)).symm.trans hx.symm
  · apply Units.ext
    change a.val.1 = 1
    rw [(sIdeleInsertion_apply F S g).1]
    let arch :=
      Units.map (RingHom.fst (InfiniteAdeleRing F) ((i : S) → i.val.adicCompletion F)).toMonoidHom
    have hIns (i : S) (z : (i.val.adicCompletion F)ˣ) : arch (ins i z) = 1 := rfl
    have h := (show arch g = 1 by simp [g, hIns])
    exact congrArg Units.val h
  · have hnormSupport (i : S) : ‖g.val.2 i‖ ≠ 1 ↔ i = v ∨ i = w := by
      let fin : (SAdeleRing F S)ˣ →* (i.val.adicCompletion F)ˣ :=
        Units.map ((Pi.evalRingHom (fun j : S ↦ j.val.adicCompletion F) i).comp
          (RingHom.snd _ _)).toMonoidHom
      have hs (z : (i.val.adicCompletion F)ˣ) : fin (ins i z) = z := by
        change (@Pi.mulSingle S (fun j : S ↦ (j.val.adicCompletion F)ˣ) _
          (Classical.decEq _) i z) i = z
        exact @Pi.mulSingle_eq_same S (fun j : S ↦ (j.val.adicCompletion F)ˣ) _
          (Classical.decEq _) i z
      have ho (j : S) (z : (j.val.adicCompletion F)ˣ) (h : j ≠ i) : fin (ins j z) = 1 := by
        change (@Pi.mulSingle S (fun j : S ↦ (j.val.adicCompletion F)ˣ) _
          (Classical.decEq _) j z) i = 1
        exact @Pi.mulSingle_eq_of_ne S (fun j : S ↦ (j.val.adicCompletion F)ˣ) _
          (Classical.decEq _) j i h.symm z
      change ‖(fin g).val‖ ≠ 1 ↔ i = v ∨ i = w
      rw [show fin g = fin (ins v u) ^ f w / fin (ins w t) ^ f v by simp only [g, map_div, map_pow],
        Units.val_div_eq_div_val, norm_div, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
        norm_pow, norm_pow]
      by_cases hiv : i = v
      · subst i
        rw [hs u, ho w t hne.symm, Units.val_one, norm_one, one_pow, div_one, hu]
        have hq : 1 < (v.val.asIdeal.absNorm : ℝ) := by
          exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
        have hlt := pow_lt_one₀ (by positivity : 0 ≤ (v.val.asIdeal.absNorm : ℝ)⁻¹)
          (inv_lt_one_of_one_lt₀ hq) (residue w hwp).2.ne'
        exact ⟨fun _ ↦ Or.inl rfl, fun _ ↦ hlt.ne⟩
      · by_cases hiw : i = w
        · subst i
          rw [hs t, ho v u hne, Units.val_one, norm_one, one_pow, one_div, ht]
          have hq : 1 < (w.val.asIdeal.absNorm : ℝ) := by
            exact_mod_cast HeightOneSpectrum.one_lt_absNorm w.val
          have hlt := pow_lt_one₀ (by positivity : 0 ≤ (w.val.asIdeal.absNorm : ℝ)⁻¹)
            (inv_lt_one_of_one_lt₀ hq) (residue v hvp).2.ne'
          exact ⟨fun _ ↦ Or.inr rfl, fun _ h ↦ hlt.ne (inv_eq_one.mp h)⟩
        · rw [ho v u (Ne.symm hiv), ho w t (Ne.symm hiw)]
          simp [hiv, hiw]
    intro x
    by_cases hx : x ∈ S
    · let i : S := ⟨x, hx⟩
      change Valued.v (a.val.2 x) ≠ 1 ↔ x = v.val ∨ x = w.val
      rw [(sIdeleInsertion_apply F S g).2.1 i]
      refine (not_congr Valued.toNormedField.norm_eq_one_iff.symm).trans ((hnormSupport i).trans ?_)
      exact or_congr Subtype.ext_iff Subtype.ext_iff
    · change Valued.v (a.val.2 x) ≠ 1 ↔ x = v.val ∨ x = w.val
      rw [(sIdeleInsertion_apply F S g).2.2 x hx, map_one]
      simp [show x ≠ v.val from fun h ↦ hx (h ▸ v.property),
        show x ≠ w.val from fun h ↦ hx (h ▸ w.property)]

end

/-! ### The archimedean character and the logarithms -/

section

open NumberField InfinitePlace.Completion IsDedekindDomain Topology
open NumberField.Units
open scoped NNReal Classical WithZero

variable (F : Type*) [Field F] [NumberField F]

local notation "C" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => MonoidHom.ker (ideleClassNorm F)
local notation "A∞" => InfiniteAdeleRing F
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

private def cubicArchInsertion : A∞ˣ →* IdeleGroup (𝓞 F) F :=
  Units.map (MonoidHom.inl A∞ (FiniteAdeleRing (𝓞 F) F))

/-- Passage from the norm-one archimedean ideles to norm-one idele classes. -/
def cubicArchClass : N∞ →ₜ* C₁ :=
  let q : IdeleGroup (𝓞 F) F →* C := QuotientGroup.mk' _
  let f := (q.comp (cubicArchInsertion F)).comp
    (infiniteIdeleNorm F).ker.subtype
  { f.codRestrict _ (fun g => by
      change ideleNorm F (cubicArchInsertion F g.val) = 1
      rw [cubicArchInsertion, ← infiniteIdeleNorm_eq_global F]
      exact g.property) with
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact (QuotientGroup.continuous_mk.comp
        ((continuous_id.prodMk continuous_const).units_map _)).comp continuous_subtype_val }

private def cubicArchUnit (w : InfinitePlace F) (g : A∞ˣ) :
    w.Completionˣ :=
  Units.map (Pi.evalRingHom _ w).toMonoidHom g

private theorem cubicArchClass_eq_mul (w₁ w₂ : InfinitePlace F)
    (hd : w₁ ≠ w₂) (hc : ∀ w : InfinitePlace F, w = w₁ ∨ w = w₂)
    (g : N∞) :
    (cubicArchClass F g).val =
      IdeleClassGroup.ofCompletion (𝓞 F) F w₁ (cubicArchUnit F w₁ g.val) *
        IdeleClassGroup.ofCompletion (𝓞 F) F w₂ (cubicArchUnit F w₂ g.val) := by
  let q : IdeleGroup (𝓞 F) F →* C := QuotientGroup.mk' _
  change q (cubicArchInsertion F g.val) =
    q (IdeleGroup.ofCompletion (𝓞 F) F w₁ (cubicArchUnit F w₁ g.val)) *
      q (IdeleGroup.ofCompletion (𝓞 F) F w₂ (cubicArchUnit F w₂ g.val))
  rw [← map_mul]
  congr 1
  apply Units.ext
  apply Prod.ext
  · funext w
    change g.val.val w =
      Pi.mulSingle (M := fun v : InfinitePlace F => v.Completion) w₁ (g.val.val w₁) w *
        Pi.mulSingle (M := fun v : InfinitePlace F => v.Completion) w₂ (g.val.val w₂) w
    rcases hc w with rfl | rfl
    · rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hd, mul_one]
    · rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hd.symm, one_mul]
  · change (1 : FiniteAdeleRing (𝓞 F) F) = 1 * 1
    exact (one_mul _).symm

private theorem cubicArchLocal_parameters (c : HeckeCharacter (𝓞 F) F)
    (hc : ∀ a, ‖c a‖ = 1) (w : InfinitePlace F) (hw : w.IsComplex) :
    ∃ (t : ℝ) (m : ℤ), ∀ u : w.Completionˣ,
      let z := extensionEmbedding w u.val
      c (IdeleClassGroup.ofCompletion (𝓞 F) F w u) =
        Complex.exp ((t : ℂ) * Complex.I * (Real.log ‖z‖ : ℂ)) *
          (z / (‖z‖ : ℂ)) ^ m := by
  let e := ringEquivComplexOfIsComplex hw
  let p : ℂˣ →ₜ* w.Completionˣ :=
    ⟨Units.map e.symm.toMonoidHom,
      (isometryEquivComplexOfIsComplex hw).symm.continuous.units_map _⟩
  let d : ℂˣ →ₜ* ℂ := (infinitePlaceRestriction F w c).comp p
  have hdn (z : ℂˣ) : ‖d z‖ = 1 := hc _
  obtain ⟨⟨a, m⟩, ⟨ha, hp⟩, _⟩ := existsUnique_complexUnits_character_parameters d hdn
  refine ⟨2 * a.im, m, fun u => ?_⟩
  let x := Units.map e.toMonoidHom u
  have hx : (x : ℂ) = extensionEmbedding w u.val := ringEquivComplexOfIsComplex_apply hw u.val
  have hpu : p x = u := Units.ext (e.symm_apply_apply _)
  have hdp : d x = c (IdeleClassGroup.ofCompletion (𝓞 F) F w u) := by
    change c (IdeleClassGroup.ofCompletion (𝓞 F) F w (p x)) = _
    rw [hpu]
  change c (IdeleClassGroup.ofCompletion (𝓞 F) F w u) = _
  rw [← hdp, hp x]
  change ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ a * _ = _
  have hapos : 0 < ‖(x : ℂ)‖ := norm_pos_iff.mpr x.ne_zero
  have harr : a = (a.im : ℂ) * Complex.I := by
    apply Complex.ext
    · simpa using ha
    · simp
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (pow_pos hapos 2).ne'),
    ← Complex.ofReal_log (pow_pos hapos 2).le, Real.log_pow]
  nth_rw 1 [harr]
  rw [hx]
  push_cast
  congr 1
  ring

private theorem cubicArch_log (w₁ w₂ : InfinitePlace F)
    (h₁ : w₁.IsComplex) (h₂ : w₂.IsComplex) (hd : w₁ ≠ w₂)
    (hc : ∀ w : InfinitePlace F, w = w₁ ∨ w = w₂) (g : N∞) :
    Real.log ‖extensionEmbedding w₂ (g.val.val w₂)‖ =
      -Real.log ‖extensionEmbedding w₁ (g.val.val w₁)‖ := by
  have hu : (Finset.univ : Finset (InfinitePlace F)) = {w₁, w₂} := by
    ext w
    simpa using hc w
  have h := infiniteIdeleLog_sum_zero F g
  rw [hu, Finset.sum_pair hd] at h
  rw [(isometry_extensionEmbedding w₁).norm_map_of_map_zero (map_zero _) _,
    (isometry_extensionEmbedding w₂).norm_map_of_map_zero (map_zero _) _]
  simp only [infiniteIdeleLog, h₁.mult_eq_two, h₂.mult_eq_two, Nat.cast_ofNat] at h
  linarith

/-- On norm-one archimedean ideles with two complex places, a unitary character has
one radial frequency and two integral angular frequencies. -/
theorem cubicArchCharacter_parameters (ω : PontryaginDual C₁)
    (w₁ w₂ : InfinitePlace F) (h₁ : w₁.IsComplex) (h₂ : w₂.IsComplex)
    (hd : w₁ ≠ w₂) (hc : ∀ w : InfinitePlace F, w = w₁ ∨ w = w₂) :
    ∃ (t : ℝ) (m₁ m₂ : ℤ), ∀ g : N∞,
      let z₁ := extensionEmbedding w₁ (g.val.val w₁)
      let z₂ := extensionEmbedding w₂ (g.val.val w₂)
      (ω (cubicArchClass F g) : ℂ) =
        Complex.exp ((t : ℂ) * Complex.I * (Real.log ‖z₁‖ : ℂ)) *
          (z₁ / (‖z₁‖ : ℂ)) ^ m₁ * (z₂ / (‖z₂‖ : ℂ)) ^ m₂ := by
  let s : ℝ≥0ˣ →* C :=
    (QuotientGroup.mk' _).comp (canonicalIdeleNormSection F)
  have hs : Function.RightInverse s (ideleClassNorm F) :=
    canonicalIdeleNormSection_rightInverse F
  have hcNorm : Continuous (ideleClassNorm F) :=
    (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.1
  let r : C →ₜ* C₁ :=
    { toFun := fun a => ⟨a / s (ideleClassNorm F a), by
        rw [MonoidHom.mem_ker, map_div, hs, div_self']⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp [map_mul, mul_div_mul_comm]
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_id.div'
          ((QuotientGroup.continuous_mk.comp (canonicalIdeleNormSection_continuous F)).comp
            hcNorm) }
  have hr (a : C₁) : r a.val = a := by
    apply Subtype.ext
    change a.val / s (ideleClassNorm F a.val) = a.val
    rw [MonoidHom.mem_ker.mp a.property, map_one, div_one]
  let c : HeckeCharacter (𝓞 F) F :=
    (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (ω.comp r)
  have hcn (a : C) : ‖c a‖ = 1 := Circle.norm_coe _
  obtain ⟨t₁, m₁, hm₁⟩ := cubicArchLocal_parameters F c hcn w₁ h₁
  obtain ⟨t₂, m₂, hm₂⟩ := cubicArchLocal_parameters F c hcn w₂ h₂
  refine ⟨t₁ - t₂, m₁, m₂, fun g => ?_⟩
  have hcg : c (cubicArchClass F g).val = (ω (cubicArchClass F g) : ℂ) := by
    change (ω (r (cubicArchClass F g).val) : ℂ) = _
    rw [hr]
  rw [← hcg, cubicArchClass_eq_mul F w₁ w₂ hd hc, map_mul, hm₁, hm₂]
  let z₁ := extensionEmbedding w₁ (g.val.val w₁)
  let z₂ := extensionEmbedding w₂ (g.val.val w₂)
  change Complex.exp ((t₁ : ℂ) * Complex.I * (Real.log ‖z₁‖ : ℂ)) *
      (z₁ / (‖z₁‖ : ℂ)) ^ m₁ *
      (Complex.exp ((t₂ : ℂ) * Complex.I * (Real.log ‖z₂‖ : ℂ)) *
        (z₂ / (‖z₂‖ : ℂ)) ^ m₂) =
    Complex.exp (((t₁ - t₂ : ℝ) : ℂ) * Complex.I * (Real.log ‖z₁‖ : ℂ)) *
      (z₁ / (‖z₁‖ : ℂ)) ^ m₁ * (z₂ / (‖z₂‖ : ℂ)) ^ m₂
  have hlog : Real.log ‖z₂‖ = -Real.log ‖z₁‖ := cubicArch_log F w₁ w₂ h₁ h₂ hd hc g
  rw [hlog, Complex.ofReal_neg]
  rw [mul_mul_mul_comm, ← Complex.exp_add, ← mul_assoc]
  push_cast
  congr 2
  ring_nf

private theorem cubicArchUnit_normOne (u : (𝓞 F)ˣ) :
    infiniteIdeleNorm F (Units.map (((algebraMap F A∞).comp (algebraMap (𝓞 F) F)).toMonoidHom) u) =
      1 := by
  apply Units.ext
  apply NNReal.coe_injective
  have hterm (v : InfinitePlace F) :
      ‖(algebraMap F A∞ (algebraMap (𝓞 F) F u.val)) v‖ =
        v (algebraMap (𝓞 F) F u.val) := by
    rw [InfiniteAdeleRing.algebraMap_apply, AbsoluteValue.Completion.norm_coe, WithAbs.ofAbs_toAbs]
    rfl
  simp only [infiniteIdeleNorm, Units.val_one, NNReal.coe_one, MonoidHom.finsetProd_apply,
    MonoidHom.pow_apply, MonoidHom.comp_apply, Units.coe_prod, Units.val_pow_eq_pow_val,
    NNReal.coe_prod, NNReal.coe_pow]
  change ∏ v : InfinitePlace F,
      ‖(algebraMap F A∞ (algebraMap (𝓞 F) F u.val)) v‖ ^ v.mult = 1
  simp_rw [hterm, InfinitePlace.prod_eq_abs_norm, Units.norm]
  norm_cast

/-- The archimedean diagonal of a global unit has norm one. -/
def cubicArchUnitDiagonal (u : (𝓞 F)ˣ) : N∞ :=
  ⟨Units.map (((algebraMap F A∞).comp (algebraMap (𝓞 F) F)).toMonoidHom) u,
    cubicArchUnit_normOne F u⟩

/-- The archimedean diagonal agrees with the place's embedding of the global unit. -/
theorem cubicArchUnitDiagonal_apply (u : (𝓞 F)ˣ) (w : InfinitePlace F) :
    extensionEmbedding w ((cubicArchUnitDiagonal F u).val.val w) =
      w.embedding (u : F) := by
  change extensionEmbedding w (algebraMap F A∞ (u : F) w) = _
  rw [InfiniteAdeleRing.algebraMap_apply, extensionEmbedding_coe]
  rfl

/-- A number field with two infinite places has a nontorsion unit. -/
theorem cubicArch_exists_unit (h : Fintype.card (InfinitePlace F) = 2) :
    ∃ u : (𝓞 F)ˣ, u ∉ Units.torsion F := by
  let i : Fin (NumberField.Units.rank F) := ⟨0, by simp [NumberField.Units.rank, h]⟩
  refine ⟨fundSystem F i, fun hu => ?_⟩
  have he : (QuotientGroup.mk (fundSystem F i) : (𝓞 F)ˣ ⧸ Units.torsion F) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hu
  have hb := fundSystem_mk F i
  rw [he] at hb
  exact (basisModTorsion F).ne_zero i hb.symm

local notation "J" => IdeleGroup (𝓞 F) F
local notation "J₁" => MonoidHom.ker (ideleNorm F)
local notation "j" => Units.map (RingHom.toMonoidHom (Subring.subtype (integralAdelesOutside F ∅)))
local notation "q" => QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
local notation "p∞" =>
  Units.map (RingHom.toMonoidHom (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))

/-- The finite class group and a common exponent on finite integral units make any
character trivial on the norm-one archimedean ideles a finite-order character. -/
theorem cubicArch_trivial_finiteOrder (ω : PontryaginDual C₁)
    (hArch : ∀ g : N∞, ω (cubicArchClass F g) = 1) :
    IsOfFinOrder ω := by
  obtain ⟨n, hn, hfin⟩ := cubic_finite_unit_character_exponent F ω
  obtain ⟨p, _, _, hexact, _⟩ := normOne_ideal_class_exact F
  let h := Nat.card (CommRing.Pic (𝓞 F))
  obtain ⟨_, _, _, _, _, hFinite, ⟨ePic⟩⟩ := ideleClassGroup_finiteness F
  let : Finite (CommRing.Pic (𝓞 F)) := @Finite.of_equiv _ _ hFinite ePic.toEquiv
  have hh : 0 < h := Nat.card_pos
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨h * n, Nat.mul_pos hh hn, ?_⟩
  apply PontryaginDual.ext
  intro a
  change (((ω : C₁ →ₜ* Circle) ^ (h * n)) a) = 1
  refine (ContinuousMonoidHom.pow_apply (ω : C₁ →ₜ* Circle) (h * n) a).trans ?_
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective a.val
  let X : J₁ := ⟨x, by
    change ideleClassNorm F (QuotientGroup.mk x) = 1
    rw [hx]
    exact a.property⟩
  have hxa : cubicNormOneClass F X = a := Subtype.ext hx
  have hpow : p (X ^ h) = 1 :=
    (map_pow p X h).trans (pow_card_eq_one' (x := p X))
  obtain ⟨y, hy⟩ := (hexact _).mp hpow
  have hy' : (X ^ h).val ∈ IdeleGroup.principalSubgroup (𝓞 F) F ⊔ (MonoidHom.range j) := by
    rw [← hy]
    exact y.property
  obtain ⟨d, hd, b, hb, hdb⟩ := Subgroup.mem_sup.mp hy'
  have hdNorm : ideleNorm F d = 1 := (ideleNorm_spec F).2 hd
  have hbNorm : ideleNorm F b = 1 := by
    have hnorm := congrArg (ideleNorm F) hdb
    rw [map_mul, hdNorm, one_mul] at hnorm
    exact hnorm.trans (X ^ h).property
  let B : J₁ := ⟨b, hbNorm⟩
  have hba : cubicNormOneClass F B = a ^ h := by
    apply Subtype.ext
    have H := congrArg q hdb
    have hqd : q d = 1 := (QuotientGroup.eq_one_iff _).mpr hd
    rw [map_mul, hqd, one_mul] at H
    change q b = _
    exact H.trans (congrArg Subtype.val ((map_pow (cubicNormOneClass F) X h).trans
      (congrArg (fun k : C₁ => k ^ h) hxa)))
  let g : N∞ := ⟨p∞ b, cubic_infiniteNorm_of_integral F b hb hbNorm⟩
  let bArch := cubicArchInsertion F g.val
  have hbArchnorm : ideleNorm F bArch = 1 :=
    (infiniteIdeleNorm_eq_global F g.val).symm.trans g.property
  have hbArch : bArch ∈ (MonoidHom.range j) := by
    apply (mem_integralIdeleRange_iff F _).mpr
    intro v
    change Valued.v (1 : v.adicCompletion F) = 1
    exact map_one _
  let U : J₁ := ⟨b / bArch, MonoidHom.mem_ker.mpr (by rw [map_div, hbNorm, hbArchnorm, div_one])⟩
  have hU : U.val ∈ (MonoidHom.range j) := (MonoidHom.range j).div_mem hb hbArch
  have hUArch : p∞ U.val = 1 := by
    change p∞ (b / bArch) = 1
    rw [map_div, show p∞ bArch = p∞ b by apply Units.ext; rfl, div_self']
  have hB : B = U * (⟨bArch, hbArchnorm⟩ : J₁) := by
    apply Subtype.ext
    exact (div_mul_cancel b bArch).symm
  let w : C₁ →* Circle := (ω : C₁ →ₜ* Circle).toMonoidHom
  change w a ^ (h * n) = 1
  rw [pow_mul, ← map_pow w, ← hba, hB, map_mul, map_mul]
  change (ω (cubicNormOneClass F U) * ω (cubicArchClass F g)) ^ n = _
  rw [hArch g, mul_one]
  exact hfin U hU hUArch

end


/-! ### Algebraic numbers, valuations and the torsion diagonals -/

private theorem cubic_algebraic_norm {z : ℂ} (hz : IsAlgebraic ℚ z) :
    IsAlgebraic ℚ (‖z‖ : ℂ) := by
  apply IsAlgebraic.of_pow (n := 2) (by decide)
  rw [← Complex.mul_conj']
  exact hz.mul (hz.algHom (starRingEnd ℂ).toRatAlgHom)

private theorem cubic_algebraic_zpow {z : ℂ} (hz : IsAlgebraic ℚ z) (m : ℤ) :
    IsAlgebraic ℚ (z ^ m) := by
  cases m with
  | ofNat n =>
      change IsAlgebraic ℚ (z ^ (n : ℤ))
      rw [zpow_natCast]
      exact hz.pow n
  | negSucc n => simpa only [zpow_negSucc] using (hz.pow (n + 1)).inv

private theorem cubic_algebraic_embedding {F : Type*} [Field F] [NumberField F]
    (σ : F →+* ℂ) (x : F) : IsAlgebraic ℚ (σ x) :=
  (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom σ.toRatAlgHom

/-- The logarithm of the absolute value under a complex embedding, as an additive map. -/
private def cubicLogAbs {F : Type*} [Field F] (σ : F →+* ℂ) : Additive Fˣ →+ ℝ where
  toFun x := Real.log ‖σ (x.toMul : F)‖
  map_zero' := by simp
  map_add' x y := by
    change Real.log ‖σ ((x.toMul : F) * (y.toMul : F))‖ = _
    rw [map_mul, norm_mul, Real.log_mul]
    · exact norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr x.toMul.ne_zero)
    · exact norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr y.toMul.ne_zero)

private theorem cubic_zpow_infinite_order {M : Type*} [Group M] {u : M} {a : ℤ}
    (hu : ¬ IsOfFinOrder u) (h : IsOfFinOrder (u ^ a)) : a = 0 := by
  obtain ⟨N, hN, hp⟩ := h.exists_pow_eq_one
  rw [← zpow_natCast, ← zpow_mul] at hp
  by_contra hn
  exact hu (isOfFinOrder_iff_zpow_eq_one.mpr ⟨a * (N : ℤ), by exact mul_ne_zero hn (by
    exact_mod_cast hN.ne'), hp⟩)

open NumberField InfinitePlace.Completion IsDedekindDomain Topology
open scoped Classical NNReal WithZero

section

variable {F : Type*} [Field F] [NumberField F]

local notation "Prime" => HeightOneSpectrum (𝓞 F)
local notation "C₁" => MonoidHom.ker (ideleClassNorm F)
local notation "N₁" => MonoidHom.ker (ideleNorm F)
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)
local notation "J" => IdeleGroup (𝓞 F) F
local notation "atInfinity" =>
  Units.map (RingHom.toMonoidHom (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
local notation "principal" => IdeleGroup.unitEmbedding (𝓞 F) F

private def cubicOrd (v : Prime) : Fˣ →* Multiplicative ℤ :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (v.valuation F).toMonoidWithZeroHom.toMonoidHom)

private theorem cubicOrd_eq_one (v : Prime) (a : Fˣ) :
    cubicOrd v a = 1 ↔ v.valuation F (a : F) = 1 := by
  change WithZero.unitsWithZeroEquiv
    (Units.map (v.valuation F).toMonoidWithZeroHom.toMonoidHom a) = 1 ↔ _
  rw [← map_one WithZero.unitsWithZeroEquiv, WithZero.unitsWithZeroEquiv.injective.eq_iff]
  refine ⟨fun h ↦ congrArg Units.val h, fun h ↦ ?_⟩
  apply Units.ext
  exact h

private theorem cubicOrd_unit (v : Prime) (u : (𝓞 F)ˣ) :
    cubicOrd v (Units.map (algebraMap (𝓞 F) F).toMonoidHom u) = 1 := by
  rw [cubicOrd_eq_one]
  change v.valuation F (algebraMap (𝓞 F) F (u : 𝓞 F)) = 1
  rw [v.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.mpr (v.asIdeal.notMem_of_isUnit u.isUnit)

/-- A field element has a norm-one archimedean diagonal on which the given character
takes a root-of-unity value. -/
private def CubicTorsionDiagonal (ω : PontryaginDual C₁) (a : Fˣ) : Prop :=
  ∃ g : N∞,
    (∀ w : InfinitePlace F, extensionEmbedding w (g.val.val w) = w.embedding (a : F)) ∧
    IsOfFinOrder (ω (cubicArchClass F g))

private theorem cubic_unit_torsion_diagonal (ω : PontryaginDual C₁) (u : (𝓞 F)ˣ) :
    CubicTorsionDiagonal ω (Units.map (algebraMap (𝓞 F) F).toMonoidHom u) := by
  let a := Units.map (algebraMap (𝓞 F) F).toMonoidHom u
  let A := cubicArchUnitDiagonal F u
  refine ⟨A, cubicArchUnitDiagonal_apply F u, ?_⟩
  let G : N₁ := ⟨principal a, (ideleNorm_spec F).2 (Set.mem_range_self a)⟩
  let I := cubicArchIdele F A
  let V := G / I
  have hVfinite : V.val ∈ (Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom).range := by
    apply (mem_integralIdeleRange_iff F V.val).mpr
    intro v
    let ev := Units.map ((RestrictedProduct.evalRingHom
      (fun w : Prime ↦ w.adicCompletion F) v).comp
      (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))).toMonoidHom
    have heval : ev I.val = 1 := Units.ext rfl
    change Valued.v (ev (G.val / I.val)).val = 1
    rw [map_div, heval, div_one]
    change Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (a : F)).trans
      ((cubicOrd_eq_one v a).mp (cubicOrd_unit v u))
  have hVarch : atInfinity V.val = 1 := by
    change atInfinity (G.val / I.val) = 1
    rw [map_div]
    exact div_self' (atInfinity G.val)
  let q := cubicNormOneClass F
  have hG : q G = 1 := by
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (principal a)).mpr (Set.mem_range_self a)
  have hV : ω (q V) = (ω (q I))⁻¹ := by
    change (ω.toMonoidHom.comp q) (G / I) = _
    rw [map_div, MonoidHom.comp_apply, MonoidHom.comp_apply, hG, map_one, one_div]
    rfl
  obtain ⟨n, hn, hnV⟩ := cubic_finite_unit_character_exponent F ω
  have h : IsOfFinOrder (ω (q V)) := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hnV V hVfinite hVarch⟩
  rw [hV, isOfFinOrder_inv_iff] at h
  exact h

private theorem cubic_pole_torsion_diagonal {T : Finset Prime}
    (ω : PontryaginDual C₁) (hT : NormOneCharacterUnramifiedOutside ω T)
    (p : HeightOneSpectrum (𝓞 ℚ)) (c : QuasiCharacter (SIdeleQuotient F T))
    (hc : ∀ x : (sIdeleQuotientNorm F T).ker,
      c x.val = (sLocalNormOneCharacter T ω hT x : ℂ))
    (v w : T) (hvw : v ≠ w) (hvp : v.val ∈ sLocalPrimaryPlaces T p)
    (hwp : w.val ∈ sLocalPrimaryPlaces T p)
    (hv : v ∈ sLocalFinitePolePlaces c) (hw : w ∈ sLocalFinitePolePlaces c) :
    ∃ a : Fˣ, (∀ x : Prime, x.valuation F (a : F) ≠ 1 ↔ x ∈ ({v.val, w.val} : Finset Prime)) ∧
      CubicTorsionDiagonal ω a := by
  obtain ⟨G, hG, hGarch, hGsupp⟩ := cubic_pole_ratio F ω hT p c hc
    v w hvw hvp hwp hv hw
  obtain ⟨a, A, hA, htorsion, hsupp⟩ := cubic_principalize_character F ω G hG hGarch
  refine ⟨a, fun x ↦ (not_congr (hsupp x)).trans ((hGsupp x).trans (by simp)),
    A, fun w ↦ ?_, htorsion⟩
  rw [hA]
  change extensionEmbedding w (algebraMap F (InfiniteAdeleRing F) (a : F) w) = _
  rw [InfiniteAdeleRing.algebraMap_apply, extensionEmbedding_coe]
  rfl

/-! ### Logarithms of a torsion diagonal -/

/-- The logarithms of the absolute values of an element with a norm-one diagonal sum to
zero, with the multiplicities of the places. -/
private theorem cubic_log_sum_of_diagonal {a : Fˣ} (g : N∞)
    (hg : ∀ w : InfinitePlace F, extensionEmbedding w (g.val.val w) = w.embedding (a : F)) :
    ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (w (a : F)) = 0 := by
  refine (Finset.sum_congr rfl fun w _ ↦ ?_).trans (infiniteIdeleLog_sum_zero F g)
  change _ = (w.mult : ℝ) * Real.log ‖g.val.val w‖
  rw [← (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) (g.val.val w), hg w,
    InfinitePlace.norm_embedding_eq]

/-- An element with a norm-one diagonal has norm `±1`. -/
private theorem cubic_abs_norm_of_log_sum {a : F} (ha : a ≠ 0)
    (h : ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (w a) = 0) :
    |(Algebra.norm ℚ a : ℝ)| = 1 := by
  have hprod := InfinitePlace.prod_eq_abs_norm a
  have hpos (w : InfinitePlace F) : 0 < w a := InfinitePlace.pos_iff.mpr ha
  have hlog : Real.log (∏ w : InfinitePlace F, w a ^ w.mult) = 0 := by
    rw [Real.log_prod (fun w _ ↦ (pow_pos (hpos w) _).ne')]
    simpa only [Real.log_pow] using h
  have h1 : (∏ w : InfinitePlace F, w a ^ w.mult) = 1 :=
    Real.eq_one_of_pos_of_log_eq_zero (Finset.prod_pos fun w _ ↦ pow_pos (hpos w) _) hlog
  rw [h1] at hprod
  exact_mod_cast hprod.symm

/-- At a real place, an element of absolute value one is a root of unity. -/
private theorem cubic_isOfFinOrder_of_real_place {w : InfinitePlace F} (hw : w.IsReal)
    {a : Fˣ} (ha : w (a : F) = 1) : IsOfFinOrder a := by
  have h := InfinitePlace.norm_embedding_of_isReal hw (a : F)
  rw [ha, Real.norm_eq_abs] at h
  rcases (abs_eq zero_le_one).mp h with h1 | h1
  · have : (a : F) = 1 := (InfinitePlace.embedding_of_isReal hw).injective (by rw [h1, map_one])
    rw [show a = 1 from Units.ext this]
    exact IsOfFinOrder.one
  · have : (a : F) = -1 :=
      (InfinitePlace.embedding_of_isReal hw).injective (by rw [h1, map_neg, map_one])
    rw [show a = -1 from Units.ext this]
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, neg_one_sq⟩

private theorem cubic_logAbs_eq (w : InfinitePlace F) (a : Fˣ) :
    cubicLogAbs w.embedding (Additive.ofMul a) = Real.log (w (a : F)) := by
  change Real.log ‖w.embedding (a : F)‖ = _
  rw [InfinitePlace.norm_embedding_eq]

end

/-! ### Fields of degree three -/

section

variable {F : Type*} [Field F] [NumberField F]

/-- A number field of degree three has signature `(3, 0)` or `(1, 1)`. -/
private theorem cubic_signature (hdeg : Module.finrank ℚ F = 3) :
    (InfinitePlace.nrRealPlaces F = 3 ∧ InfinitePlace.nrComplexPlaces F = 0) ∨
    (InfinitePlace.nrRealPlaces F = 1 ∧ InfinitePlace.nrComplexPlaces F = 1) := by
  have h := InfinitePlace.card_add_two_mul_card_eq_rank F
  omega

/-- In a field of degree three every irrational element generates the field. -/
private theorem cubic_adjoin_eq_top (hdeg : Module.finrank ℚ F = 3) {x : F}
    (hx : x ∉ (⊥ : IntermediateField ℚ F)) : IntermediateField.adjoin ℚ {x} = ⊤ := by
  let K := IntermediateField.adjoin ℚ {x}
  have hmul := Module.finrank_mul_finrank ℚ K F
  rw [hdeg] at hmul
  have hdvd : Module.finrank ℚ K ∣ 3 := Dvd.intro _ hmul
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact absurd (IntermediateField.adjoin_simple_eq_bot_iff.mp
      (IntermediateField.finrank_eq_one_iff.mp h1)) hx
  · exact IntermediateField.eq_of_le_of_finrank_eq le_top
      (by rw [h3, IntermediateField.finrank_top', hdeg])

/-- Two `ℚ`-algebra maps out of a field generated by `x` agree when they agree on `x`. -/
private theorem cubic_algHom_eq_of_adjoin {K : Type*} [Field K] [Algebra ℚ K] {x : F}
    (hx : IntermediateField.adjoin ℚ {x} = ⊤) {φ ψ : F →ₐ[ℚ] K} (h : φ x = ψ x) : φ = ψ := by
  have halg : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have hsub : Algebra.adjoin ℚ {x} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg, hx,
      IntermediateField.top_toSubalgebra]
  exact AlgHom.ext_of_adjoin_eq_top hsub fun y hy ↦ by
    rw [Set.mem_singleton_iff.mp hy]
    exact h

/-- A root in `F` of the minimal polynomial of a generator is the image of the generator
under an endomorphism. -/
private theorem cubic_exists_algHom_of_root {x y : F}
    (hx : IntermediateField.adjoin ℚ {x} = ⊤) (hy : Polynomial.aeval y (minpoly ℚ x) = 0) :
    ∃ θ : F →ₐ[ℚ] F, θ x = y := by
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  let pb := IntermediateField.adjoin.powerBasis hint
  have hy' : Polynomial.aeval y (minpoly ℚ pb.gen) = 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]
    exact hy
  let e : IntermediateField.adjoin ℚ {x} ≃ₐ[ℚ] F :=
    (IntermediateField.equivOfEq hx).trans IntermediateField.topEquiv
  have he : e.symm x = pb.gen := by
    apply e.injective
    rw [AlgEquiv.apply_symm_apply, IntermediateField.adjoin.powerBasis_gen]
    rfl
  refine ⟨(pb.lift y hy').comp e.symm.toAlgHom, ?_⟩
  change pb.lift y hy' (e.symm x) = y
  rw [he, PowerBasis.lift_gen]

/-- A real cube root of one is one. -/
private theorem cubic_rat_eq_one_of_cube {r : ℚ} (h : r ^ 3 = 1) : r = 1 := by
  have h1 : (r - 1) * (r ^ 2 + r + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h1 with h2 | h2
  · linarith
  · nlinarith [sq_nonneg (r + 1 / 2)]

/-- A fixed-point-free injection of a three-element set cycles its points, so a relation
`p r(f e) + q r(e) = 0` with `∑ r = 0` forces `r = 0`. -/
private theorem cubic_circulant {E : Type*} [Fintype E] (hE : Fintype.card E = 3)
    (f : E → E) (hf : Injective f) (hfix : ∀ e, f e ≠ e) (r : E → ℝ) (hsum : ∑ e, r e = 0)
    (p q : ℝ) (hpq : p ≠ 0 ∨ q ≠ 0) (hrel : ∀ e, p * r (f e) + q * r e = 0) (e : E) :
    r e = 0 := by
  have h01 : f e ≠ e := hfix e
  have h12 : f (f e) ≠ f e := hfix (f e)
  have h02 : f (f e) ≠ e := by
    intro h20
    have hthird : ∃ e', e' ≠ e ∧ e' ≠ f e := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset E) ⊆ {e, f e} := fun x _ ↦ by
        by_cases hx : x = e
        · simp [hx]
        · simp [hcon x hx]
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_univ, hE] at h1
      have h2 := Finset.card_le_two (a := e) (b := f e)
      omega
    obtain ⟨e', he'1, he'2⟩ := hthird
    have hA : f e' ≠ e := fun h ↦ he'2 (hf (h.trans h20.symm))
    have hB : f e' ≠ f e := fun h ↦ he'1 (hf h)
    have hC : f e' ≠ e' := hfix e'
    have hsub : ({e, f e, e', f e'} : Finset E) ⊆ Finset.univ := Finset.subset_univ _
    have h4 : ({e, f e, e', f e'} : Finset E).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hC.symm]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨he'2.symm, hB.symm⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h01.symm, he'1.symm, hA.symm⟩
    have h5 := Finset.card_le_card hsub
    rw [h4, Finset.card_univ, hE] at h5
    omega
  have huniv : (Finset.univ : Finset E) = {e, f e, f (f e)} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem, Finset.card_pair h12.symm, hE]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h01.symm, h02.symm⟩
  have hs : r e + r (f e) + r (f (f e)) = 0 := by
    rw [huniv, Finset.sum_insert, Finset.sum_pair h12.symm] at hsum
    · linarith
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h01.symm, h02.symm⟩
  have hA := hrel e
  have hB := hrel (f e)
  have hpos : 0 < p ^ 2 - p * q + q ^ 2 := by
    rcases hpq with h | h
    · nlinarith [mul_self_pos.mpr h, sq_nonneg (2 * q - p)]
    · nlinarith [mul_self_pos.mpr h, sq_nonneg (2 * p - q)]
  have hlin : (p ^ 2 - p * q + q ^ 2) * r e = 0 := by
    linear_combination (q - p) * hA - p * (hB - p * hs)
  exact (mul_eq_zero.mp hlin).resolve_left hpos.ne'

end


/-! ### The archimedean character of a cubic field -/

section

open NumberField InfinitePlace.Completion

variable {F : Type*} [Field F] [NumberField F]

local notation "C" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => MonoidHom.ker (ideleClassNorm F)
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

/-- A norm-one character extends to a unitary Hecke character. -/
private theorem cubic_heckeCharacter_of_normOne (ω : PontryaginDual C₁) :
    ∃ c : HeckeCharacter (𝓞 F) F, (∀ a, ‖c a‖ = 1) ∧ ∀ a : C₁, c a.val = (ω a : ℂ) := by
  let s : ℝ≥0ˣ →* C :=
    (QuotientGroup.mk' _).comp (canonicalIdeleNormSection F)
  have hs : Function.RightInverse s (ideleClassNorm F) :=
    canonicalIdeleNormSection_rightInverse F
  have hcNorm : Continuous (ideleClassNorm F) :=
    (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.1
  let r : C →ₜ* C₁ :=
    { toFun := fun a => ⟨a / s (ideleClassNorm F a), by
        rw [MonoidHom.mem_ker, map_div, hs, div_self']⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp [map_mul, mul_div_mul_comm]
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_id.div'
          ((QuotientGroup.continuous_mk.comp (canonicalIdeleNormSection_continuous F)).comp
            hcNorm) }
  have hr (a : C₁) : r a.val = a := by
    apply Subtype.ext
    change a.val / s (ideleClassNorm F a.val) = a.val
    rw [MonoidHom.mem_ker.mp a.property, map_one, div_one]
  refine ⟨(⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (ω.comp r),
    fun a ↦ Circle.norm_coe _, fun a ↦ ?_⟩
  change (ω (r a.val) : ℂ) = _
  rw [hr]

/-- At a real place, the square of a unitary character is a purely imaginary power of
the absolute value. -/
private theorem cubicArchLocal_real_parameters (c : HeckeCharacter (𝓞 F) F)
    (hc : ∀ a, ‖c a‖ = 1) (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ t : ℝ, ∀ u : w.Completionˣ,
      c (IdeleClassGroup.ofCompletion (𝓞 F) F w u) ^ 2 =
        Complex.exp ((2 * t : ℝ) * Complex.I * (Real.log ‖extensionEmbedding w u.val‖ : ℂ)) := by
  let e := ringEquivRealOfIsReal hw
  let p : ℝˣ →ₜ* w.Completionˣ :=
    ⟨Units.map e.symm.toMonoidHom,
      (isometryEquivRealOfIsReal hw).symm.continuous.units_map _⟩
  let d : ℝˣ →ₜ* ℂ := (infinitePlaceRestriction F w c).comp p
  have hdn (x : ℝˣ) : ‖d x‖ = 1 := hc _
  obtain ⟨⟨a, k⟩, ⟨ha, hp⟩, _⟩ := existsUnique_realUnits_character_parameters d hdn
  refine ⟨a.im, fun u => ?_⟩
  let x := Units.map e.toMonoidHom u
  have hx : ‖(x : ℝ)‖ = ‖extensionEmbedding w u.val‖ := by
    rw [← extensionEmbeddingOfIsReal_apply hw, Complex.norm_real]
    rfl
  have hpu : p x = u := Units.ext (e.symm_apply_apply _)
  have hdp : d x = c (IdeleClassGroup.ofCompletion (𝓞 F) F w u) := by
    change c (IdeleClassGroup.ofCompletion (𝓞 F) F w (p x)) = _
    rw [hpu]
  have hsign : ((if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ k.val) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    split_ifs <;> simp
  have hpos : 0 < ‖(x : ℝ)‖ := norm_pos_iff.mpr x.ne_zero
  have harr : a = (a.im : ℂ) * Complex.I := by
    apply Complex.ext
    · simpa using ha
    · simp
  rw [← hdp, hp x, mul_pow, hsign, mul_one,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'),
    ← Complex.ofReal_log (norm_nonneg _), ← Complex.exp_nat_mul, hx]
  nth_rw 1 [harr]
  push_cast
  congr 1
  ring

/-- The class of a norm-one archimedean idele is the product of its local classes. -/
private theorem cubicArchClass_eq_prod (g : N∞) :
    (cubicArchClass F g).val =
      ∏ w, IdeleClassGroup.ofCompletion (𝓞 F) F w (cubicArchUnit F w g.val) := by
  let q : IdeleGroup (𝓞 F) F →* C := QuotientGroup.mk' _
  change q (cubicArchInsertion F g.val) =
    ∏ w, q (IdeleGroup.ofCompletion (𝓞 F) F w (cubicArchUnit F w g.val))
  rw [← map_prod]
  congr 1
  apply Units.ext
  rw [Units.coe_prod]
  apply Prod.ext
  · rw [Prod.fst_prod]
    funext w
    rw [Finset.prod_apply]
    change g.val.val w = ∏ v : InfinitePlace F,
      Pi.mulSingle (M := fun v : InfinitePlace F => v.Completion) v (g.val.val v) w
    rw [Finset.prod_pi_mulSingle]
    simp
  · rw [Prod.snd_prod]
    change (1 : FiniteAdeleRing (𝓞 F) F) = ∏ _v : InfinitePlace F, (1 : FiniteAdeleRing (𝓞 F) F)
    simp

/-- The logarithm of a component of an archimedean idele, as in `infiniteIdeleLog`. -/
private theorem cubic_infiniteIdeleLog_eq (g : N∞) (w : InfinitePlace F) :
    infiniteIdeleLog F g.val w =
      (w.mult : ℝ) * Real.log ‖extensionEmbedding w (g.val.val w)‖ := by
  change (w.mult : ℝ) * Real.log ‖g.val.val w‖ = _
  rw [(isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) (g.val.val w)]

/-- On a complex cubic field, with real place `w₁` and complex place `w₂`, the square of a
norm-one character on the norm-one archimedean ideles is a radial power at `w₂` times an
even angular power. -/
private theorem cubicArch_complex_parameters (ω : PontryaginDual C₁)
    (w₁ w₂ : InfinitePlace F) (h₁ : w₁.IsReal) (h₂ : w₂.IsComplex)
    (hd : w₁ ≠ w₂) (hc : ∀ w : InfinitePlace F, w = w₁ ∨ w = w₂) :
    ∃ (τ : ℝ) (m : ℤ), ∀ g : N∞,
      (ω (cubicArchClass F g) : ℂ) ^ 2 =
        Complex.exp ((τ : ℂ) * Complex.I *
          (Real.log ‖extensionEmbedding w₂ (g.val.val w₂)‖ : ℂ)) *
          (extensionEmbedding w₂ (g.val.val w₂) /
            (‖extensionEmbedding w₂ (g.val.val w₂)‖ : ℂ)) ^ (2 * m) := by
  obtain ⟨c, hcn, hcω⟩ := cubic_heckeCharacter_of_normOne ω
  obtain ⟨t₁, ht₁⟩ := cubicArchLocal_real_parameters c hcn w₁ h₁
  obtain ⟨t₂, m, ht₂⟩ := cubicArchLocal_parameters F c hcn w₂ h₂
  refine ⟨2 * t₂ - 4 * t₁, m, fun g => ?_⟩
  have huniv : (Finset.univ : Finset (InfinitePlace F)) = {w₁, w₂} := by
    ext w
    simpa using hc w
  have hprod := cubicArchClass_eq_prod g
  rw [huniv, Finset.prod_pair hd] at hprod
  have hlog := infiniteIdeleLog_sum_zero F g
  rw [huniv, Finset.sum_pair hd, cubic_infiniteIdeleLog_eq, cubic_infiniteIdeleLog_eq,
    h₁.mult_eq_one, h₂.mult_eq_two] at hlog
  set z₁ := extensionEmbedding w₁ (g.val.val w₁)
  set z₂ := extensionEmbedding w₂ (g.val.val w₂)
  have hl : Real.log ‖z₁‖ = -2 * Real.log ‖z₂‖ := by
    push_cast at hlog
    linarith
  rw [← hcω, hprod, map_mul, mul_pow, ht₁, ht₂, mul_pow]
  change Complex.exp ((2 * t₁ : ℝ) * Complex.I * (Real.log ‖z₁‖ : ℂ)) *
      (Complex.exp ((t₂ : ℂ) * Complex.I * (Real.log ‖z₂‖ : ℂ)) ^ 2 *
        ((z₂ / (‖z₂‖ : ℂ)) ^ m) ^ 2) = _
  have hz : ((z₂ / (‖z₂‖ : ℂ)) ^ m) ^ 2 = (z₂ / (‖z₂‖ : ℂ)) ^ (2 * m) := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
    norm_num
  have he : Complex.exp ((t₂ : ℂ) * Complex.I * (Real.log ‖z₂‖ : ℂ)) ^ 2 =
      Complex.exp ((2 * t₂ : ℝ) * Complex.I * (Real.log ‖z₂‖ : ℂ)) := by
    rw [← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [hz, he, hl, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- On a totally real cubic field, the square of a norm-one character on the norm-one
archimedean ideles is `exp (i (s₁ log |x₁| + s₂ log |x₂|))`. -/
private theorem cubicArch_real_parameters (ω : PontryaginDual C₁)
    (w₁ w₂ w₃ : InfinitePlace F) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal) (h₃ : w₃.IsReal)
    (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ w₃) (h23 : w₂ ≠ w₃)
    (hc : ∀ w : InfinitePlace F, w = w₁ ∨ w = w₂ ∨ w = w₃) :
    ∃ s₁ s₂ : ℝ, ∀ g : N∞,
      (ω (cubicArchClass F g) : ℂ) ^ 2 = Complex.exp (Complex.I *
        ((s₁ * Real.log ‖extensionEmbedding w₁ (g.val.val w₁)‖ +
          s₂ * Real.log ‖extensionEmbedding w₂ (g.val.val w₂)‖ : ℝ) : ℂ)) := by
  obtain ⟨c, hcn, hcω⟩ := cubic_heckeCharacter_of_normOne ω
  obtain ⟨t₁, ht₁⟩ := cubicArchLocal_real_parameters c hcn w₁ h₁
  obtain ⟨t₂, ht₂⟩ := cubicArchLocal_real_parameters c hcn w₂ h₂
  obtain ⟨t₃, ht₃⟩ := cubicArchLocal_real_parameters c hcn w₃ h₃
  refine ⟨2 * t₁ - 2 * t₃, 2 * t₂ - 2 * t₃, fun g => ?_⟩
  have huniv : (Finset.univ : Finset (InfinitePlace F)) = {w₁, w₂, w₃} := by
    ext w
    simpa using hc w
  have hnot : w₁ ∉ ({w₂, w₃} : Finset (InfinitePlace F)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h12, h13⟩
  have hprod := cubicArchClass_eq_prod g
  rw [huniv, Finset.prod_insert hnot, Finset.prod_pair h23] at hprod
  have hlog := infiniteIdeleLog_sum_zero F g
  rw [huniv, Finset.sum_insert hnot, Finset.sum_pair h23, cubic_infiniteIdeleLog_eq,
    cubic_infiniteIdeleLog_eq, cubic_infiniteIdeleLog_eq, h₁.mult_eq_one, h₂.mult_eq_one,
    h₃.mult_eq_one] at hlog
  set l₁ := Real.log ‖extensionEmbedding w₁ (g.val.val w₁)‖
  set l₂ := Real.log ‖extensionEmbedding w₂ (g.val.val w₂)‖
  set l₃ := Real.log ‖extensionEmbedding w₃ (g.val.val w₃)‖
  have hl : l₃ = -l₁ - l₂ := by
    push_cast at hlog
    linarith
  rw [← hcω, hprod, map_mul, map_mul, mul_pow, mul_pow, ht₁, ht₂, ht₃]
  change Complex.exp ((2 * t₁ : ℝ) * Complex.I * (l₁ : ℂ)) *
      (Complex.exp ((2 * t₂ : ℝ) * Complex.I * (l₂ : ℂ)) *
        Complex.exp ((2 * t₃ : ℝ) * Complex.I * (l₃ : ℂ))) = _
  rw [← Complex.exp_add, ← Complex.exp_add, hl]
  congr 1
  push_cast
  ring

end


/-! ### The Four Exponentials Conjecture -/

/-- The Four Exponentials Conjecture, in its qualitative form: if `x₁, x₂` are linearly
independent over `ℚ`, and so are `y₁, y₂`, then one of the four numbers `exp (xᵢ yⱼ)` is
transcendental. It is open; its case with three numbers `y` is the Six Exponentials Theorem.
See M. Waldschmidt, *The Role of Complex Conjugation in Transcendental Number Theory*, in
*Diophantine Equations* (ed. N. Saradha), Narosa and TIFR 2007, Conjecture 2.4, p. 5, which
attributes it to Siegel, Schneider, Lang and Ramachandra; the six exponentials are
Theorem 2.1, p. 4 there.
Conjecture: this definition asserts nothing. The theorems below take it as a hypothesis. -/
public def FourExponentialsConjecture : Prop :=
  ∀ x y : Fin 2 → ℂ, LinearIndependent ℚ x → LinearIndependent ℚ y →
    ∃ i j, ¬ IsAlgebraic ℚ (Complex.exp (x i * y j))

/-! ### The two signatures -/

section

open NumberField InfinitePlace.Completion

variable {F : Type*} [Field F] [NumberField F]

local notation "Prime" => HeightOneSpectrum (𝓞 F)
local notation "C₁" => MonoidHom.ker (ideleClassNorm F)
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

/-- A character whose square is trivial on the norm-one archimedean ideles has finite
order. -/
private theorem cubic_finiteOrder_of_sq_trivial (ω : PontryaginDual C₁)
    (h : ∀ g : N∞, (ω (cubicArchClass F g) : ℂ) ^ 2 = 1) : IsOfFinOrder ω := by
  have h2 : IsOfFinOrder (ω ^ 2) := by
    apply cubicArch_trivial_finiteOrder F (ω ^ 2)
    intro g
    apply Circle.ext
    change ((ω ^ 2 : PontryaginDual C₁) (cubicArchClass F g) : ℂ) = 1
    rw [show (ω ^ 2 : PontryaginDual C₁) (cubicArchClass F g) = ω (cubicArchClass F g) ^ 2 from
      ContinuousMonoidHom.pow_apply (ω : C₁ →ₜ* Circle) 2 _, Circle.coe_pow]
    exact h g
  exact (isOfFinOrder_pow.mp h2).resolve_right (by norm_num)

/-- The square of a root-of-unity value of the character is a root of unity in `ℂ`. -/
private theorem cubic_sq_isOfFinOrder (ω : PontryaginDual C₁) {g : N∞}
    (h : IsOfFinOrder (ω (cubicArchClass F g))) :
    IsOfFinOrder ((ω (cubicArchClass F g) : ℂ) ^ 2) :=
  (Circle.coeHom.isOfFinOrder h).pow

/-- The positive real number `w a` as an algebraic complex number. -/
private theorem cubic_algebraic_place (w : InfinitePlace F) (a : F) :
    IsAlgebraic ℚ ((w a : ℝ) : ℂ) := by
  rw [← InfinitePlace.norm_embedding_eq]
  exact cubic_algebraic_norm (cubic_algebraic_embedding w.embedding a)

private theorem cubic_exp_log_place (w : InfinitePlace F) {a : F} (ha : a ≠ 0) :
    Complex.exp (Real.log (w a) : ℂ) = ((w a : ℝ) : ℂ) := by
  rw [← Complex.ofReal_exp, Real.exp_log (InfinitePlace.pos_iff.mpr ha)]

/-- The logarithms at one place of a product of powers. -/
private theorem cubic_log_place_mul_zpow (w : InfinitePlace F) (x y : Fˣ) (k l : ℤ) :
    Real.log (w ((x ^ k * y ^ l : Fˣ) : F)) =
      k * Real.log (w (x : F)) + l * Real.log (w (y : F)) := by
  rw [← cubic_logAbs_eq, ← cubic_logAbs_eq, ← cubic_logAbs_eq, ofMul_mul, ofMul_zpow, ofMul_zpow,
    map_add, map_zsmul, map_zsmul, zsmul_eq_mul, zsmul_eq_mul]

private theorem cubic_log_place_mul3_zpow (w : InfinitePlace F) (x y z : Fˣ) (k l n : ℤ) :
    Real.log (w ((x ^ k * y ^ l * z ^ n : Fˣ) : F)) =
      k * Real.log (w (x : F)) + l * Real.log (w (y : F)) + n * Real.log (w (z : F)) := by
  rw [← cubic_logAbs_eq, ← cubic_logAbs_eq, ← cubic_logAbs_eq, ← cubic_logAbs_eq, ofMul_mul,
    ofMul_mul, ofMul_zpow, ofMul_zpow, ofMul_zpow, map_add, map_add, map_zsmul, map_zsmul,
    map_zsmul, zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul]

/-- A root of unity has absolute value one at every place. -/
private theorem cubic_place_eq_one_of_isOfFinOrder (w : InfinitePlace F) {a : Fˣ}
    (ha : IsOfFinOrder a) : w (a : F) = 1 := by
  obtain ⟨n, hn, he⟩ := ha.exists_pow_eq_one
  have h : w (a : F) ^ n = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, he, Units.val_one, map_one]
  exact (pow_eq_one_iff_of_nonneg (AbsoluteValue.nonneg _ _) hn.ne').mp h

/-- An element whose argument at a complex place is a rational multiple of `π`, and whose
norm is `±1`, is a root of unity, in a field of degree three. -/
private theorem cubic_complex_angular_torsion (hdeg : Module.finrank ℚ F = 3)
    {w : InfinitePlace F} (hw : w.IsComplex) {u : Fˣ}
    (hN : |(Algebra.norm ℚ (u : F) : ℝ)| = 1) {M : ℕ} (hM : 0 < M)
    (h : (w.embedding (u : F) / (‖w.embedding (u : F)‖ : ℂ)) ^ M = 1) : IsOfFinOrder u := by
  let σ := w.embedding
  let x : F := (u : F) ^ M
  have hz : σ (u : F) ≠ 0 := (map_ne_zero σ).mpr u.ne_zero
  have hr : (‖σ (u : F)‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hreal : σ x = ((‖σ (u : F)‖ ^ M : ℝ) : ℂ) := by
    have h' := h
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hr)] at h'
    change σ ((u : F) ^ M) = _
    rw [map_pow, h']
    push_cast
    rfl
  have hconj : (ComplexEmbedding.conjugate σ) x = σ x := by
    rw [ComplexEmbedding.conjugate_coe_eq, hreal, Complex.conj_ofReal]
  by_cases hx : x ∈ (⊥ : IntermediateField ℚ F)
  · obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hx
    have hnorm : Algebra.norm ℚ x = q ^ 3 := by
      rw [← hq, Algebra.norm_algebraMap, hdeg]
    have hnorm' : |(Algebra.norm ℚ x : ℝ)| = 1 := by
      change |((Algebra.norm ℚ ((u : F) ^ M) : ℚ) : ℝ)| = 1
      rw [map_pow, Rat.cast_pow, abs_pow, hN, one_pow]
    rw [hnorm, Rat.cast_pow, abs_pow] at hnorm'
    have hq1 : |(q : ℝ)| = 1 :=
      (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by norm_num)).mp hnorm'
    have hq2 : q ^ 2 = 1 := by
      have : ((q : ℝ)) ^ 2 = 1 := by rw [← sq_abs, hq1, one_pow]
      exact_mod_cast this
    have hx2 : (u : F) ^ (M * 2) = 1 := by
      rw [pow_mul]
      change x ^ 2 = 1
      rw [← hq, ← map_pow, hq2, map_one]
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨M * 2, by omega, Units.ext (by
      rw [Units.val_pow_eq_pow_val, hx2, Units.val_one])⟩
  · exfalso
    have hadj := cubic_adjoin_eq_top hdeg hx
    have he : (ComplexEmbedding.conjugate σ).toRatAlgHom = σ.toRatAlgHom :=
      cubic_algHom_eq_of_adjoin hadj hconj
    have hσ : ComplexEmbedding.conjugate σ = σ := by
      ext z
      exact DFunLike.congr_fun he z
    have hwr : w.IsReal := by
      rw [InfinitePlace.isReal_iff]
      exact ComplexEmbedding.isReal_iff.mpr hσ
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr hw) hwr

/-- In a cubic field, with a nontorsion element `ε` that is a unit and an element `a` with
nonzero valuation at some place, both with norm-one diagonals, the logarithms of their
absolute values at any one place are independent over `ℤ`. -/
private theorem cubic_log_independent2 {w₀ : InfinitePlace F} (h₀ : w₀.IsReal)
    (w : InfinitePlace F) (hw : ∀ β : Fˣ,
      ∑ x : InfinitePlace F, (x.mult : ℝ) * Real.log (x (β : F)) = 0 →
        Real.log (w (β : F)) = 0 → Real.log (w₀ (β : F)) = 0)
    {ε a : Fˣ} (hε : ¬ IsOfFinOrder ε)
    (hεs : ∑ x : InfinitePlace F, (x.mult : ℝ) * Real.log (x (ε : F)) = 0)
    (has : ∑ x : InfinitePlace F, (x.mult : ℝ) * Real.log (x (a : F)) = 0)
    (v : Prime) (hεv : cubicOrd v ε = 1) (hav : cubicOrd v a ≠ 1) (k l : ℤ)
    (hkl : (k : ℝ) * Real.log (w (ε : F)) + l * Real.log (w (a : F)) = 0) : k = 0 ∧ l = 0 := by
  let β : Fˣ := ε ^ k * a ^ l
  have hβs : ∑ x : InfinitePlace F, (x.mult : ℝ) * Real.log (x (β : F)) = 0 := by
    simp_rw [β, cubic_log_place_mul_zpow, mul_add, Finset.sum_add_distrib]
    simp_rw [mul_left_comm (_ : ℝ) (k : ℝ), mul_left_comm (_ : ℝ) (l : ℝ), ← Finset.mul_sum,
      hεs, has, mul_zero, add_zero]
  have hβw : Real.log (w (β : F)) = 0 := by rw [cubic_log_place_mul_zpow]; exact hkl
  have hβ0 := hw β hβs hβw
  have hβt : IsOfFinOrder β := cubic_isOfFinOrder_of_real_place h₀
    (Real.eq_one_of_pos_of_log_eq_zero (InfinitePlace.pos_iff.mpr β.ne_zero) hβ0)
  have hord : (cubicOrd v a) ^ l = 1 := by
    have h1 : cubicOrd v β = 1 := ((cubicOrd v).isOfFinOrder hβt).eq_one'
    simpa only [β, map_mul, map_zpow, hεv, one_zpow, one_mul] using h1
  have hl : l = 0 := by
    have he : l * (cubicOrd v a).toAdd = 0 := congrArg Multiplicative.toAdd hord
    refine (mul_eq_zero.mp he).resolve_right fun h ↦ hav ?_
    exact Multiplicative.toAdd.injective (by simpa using h)
  refine ⟨cubic_zpow_infinite_order hε ?_, hl⟩
  simpa only [β, hl, zpow_zero, mul_one] using hβt

/-- **Complex cubic fields.** A repeated pole, through the element `a`, contradicts the Four
Exponentials Conjecture. If the radial exponent of the character vanishes, it contradicts
the angular torsion of the unit instead, with no conjecture. -/
private theorem cubic_complex_false (hFEC : FourExponentialsConjecture)
    (hdeg : Module.finrank ℚ F = 3) (ω : PontryaginDual C₁) (hω : ¬ IsOfFinOrder ω)
    (w₁ w₂ : InfinitePlace F) (h₁ : w₁.IsReal) (h₂ : w₂.IsComplex) (hd : w₁ ≠ w₂)
    (hc : ∀ w : InfinitePlace F, w = w₁ ∨ w = w₂) (ε : Fˣ) (hε : ¬ IsOfFinOrder ε)
    (hεv : ∀ v : Prime, cubicOrd v ε = 1) (hεχ : CubicTorsionDiagonal ω ε)
    (a : Fˣ) (v : Prime) (hav : cubicOrd v a ≠ 1) (haχ : CubicTorsionDiagonal ω a) : False := by
  obtain ⟨τ, m, hpar⟩ := cubicArch_complex_parameters ω w₁ w₂ h₁ h₂ hd hc
  let σ := w₂.embedding
  let ℓ (η : Fˣ) : ℝ := Real.log (w₂ (η : F))
  let ζ (η : Fˣ) : ℂ := σ (η : F) / (‖σ (η : F)‖ : ℂ)
  have huniv : (Finset.univ : Finset (InfinitePlace F)) = {w₁, w₂} := by
    ext w
    simpa using hc w
  -- The torsion relation and the norm relation for an element with a torsion diagonal.
  have key (η : Fˣ) (hη : CubicTorsionDiagonal ω η) :
      (∑ x : InfinitePlace F, (x.mult : ℝ) * Real.log (x (η : F)) = 0) ∧
      IsOfFinOrder (Complex.exp ((τ : ℂ) * Complex.I * (ℓ η : ℂ)) * ζ η ^ (2 * m)) := by
    obtain ⟨g, hg, htor⟩ := hη
    refine ⟨cubic_log_sum_of_diagonal g hg, ?_⟩
    have h := cubic_sq_isOfFinOrder ω htor
    rw [hpar g, hg w₂] at h
    have hℓ : ℓ η = Real.log ‖σ (η : F)‖ := by
      change Real.log (w₂ (η : F)) = _
      rw [InfinitePlace.norm_embedding_eq]
    rw [hℓ]
    exact h
  obtain ⟨hεs, hεt⟩ := key ε hεχ
  obtain ⟨has, hat⟩ := key a haχ
  -- `log w₁ = -2 log w₂` on elements with a norm-one diagonal.
  have hrel (β : Fˣ) (hβ : ∑ x : InfinitePlace F, (x.mult : ℝ) * Real.log (x (β : F)) = 0) :
      Real.log (w₁ (β : F)) = -2 * Real.log (w₂ (β : F)) := by
    rw [huniv, Finset.sum_pair hd, h₁.mult_eq_one, h₂.mult_eq_two] at hβ
    push_cast at hβ
    linarith
  have hind := cubic_log_independent2 h₁ w₂ (fun β hβ h0 ↦ by rw [hrel β hβ, h0, mul_zero])
    hε hεs has v (hεv v) hav
  have hN (η : Fˣ) (hηs : ∑ x : InfinitePlace F, (x.mult : ℝ) * Real.log (x (η : F)) = 0) :
      |(Algebra.norm ℚ (η : F) : ℝ)| = 1 := cubic_abs_norm_of_log_sum η.ne_zero hηs
  by_cases hτ : τ = 0
  · -- Purely angular: the unit has a torsion argument, impossible in degree three.
    have hm : m ≠ 0 := by
      intro hm0
      apply hω
      apply cubic_finiteOrder_of_sq_trivial ω
      intro g
      rw [hpar g, hτ, hm0]
      simp
    rw [hτ] at hεt
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul] at hεt
    obtain ⟨N, hNpos, hNe⟩ := hεt.exists_pow_eq_one
    have hpow : ζ ε ^ (2 * m * N : ℤ).natAbs = 1 := by
      have h1 : ζ ε ^ (2 * m * N : ℤ) = 1 := by
        rw [zpow_mul, zpow_natCast]
        exact hNe
      rcases Int.natAbs_eq (2 * m * N) with h2 | h2
      · rw [h2, zpow_natCast] at h1
        exact h1
      · rw [h2, zpow_neg, inv_eq_one, zpow_natCast] at h1
        exact h1
    have hM : 0 < (2 * m * N : ℤ).natAbs := by
      apply Int.natAbs_pos.mpr
      exact mul_ne_zero (mul_ne_zero two_ne_zero hm) (by exact_mod_cast hNpos.ne')
    exact hε (cubic_complex_angular_torsion hdeg h₂ (hN ε hεs) hM hpow)
  · -- The radial exponent is nonzero: the Four Exponentials Conjecture applies.
    obtain ⟨N₁, hN₁, hN₁e⟩ := hεt.exists_pow_eq_one
    obtain ⟨N₂, hN₂, hN₂e⟩ := hat.exists_pow_eq_one
    let N : ℕ := N₁ * N₂
    have hNpos : 0 < N := Nat.mul_pos hN₁ hN₂
    have hrelN (η : Fˣ) (n : ℕ) (hn : n ∣ N)
        (he : (Complex.exp ((τ : ℂ) * Complex.I * (ℓ η : ℂ)) * ζ η ^ (2 * m)) ^ n = 1) :
        Complex.exp (ℓ η * (-(τ * N : ℝ) * Complex.I)) = ζ η ^ (2 * m * N : ℤ) := by
      obtain ⟨d, hd⟩ := hn
      have hN' : (Complex.exp ((τ : ℂ) * Complex.I * (ℓ η : ℂ)) * ζ η ^ (2 * m)) ^ N = 1 := by
        rw [hd, pow_mul, he, one_pow]
      rw [mul_pow, ← Complex.exp_nat_mul, ← zpow_natCast, ← zpow_mul] at hN'
      have hζ : ζ η ^ (2 * m * N : ℤ) =
          (Complex.exp ((N : ℂ) * ((τ : ℂ) * Complex.I * (ℓ η : ℂ))))⁻¹ :=
        eq_inv_of_mul_eq_one_right hN'
      rw [hζ, ← Complex.exp_neg]
      congr 1
      push_cast
      ring
    have hεN := hrelN ε N₁ (Dvd.intro _ rfl) hN₁e
    have haN := hrelN a N₂ (Dvd.intro_left _ rfl) hN₂e
    let x : Fin 2 → ℂ := ![(ℓ ε : ℂ), (ℓ a : ℂ)]
    let y : Fin 2 → ℂ := ![1, -(τ * N : ℝ) * Complex.I]
    have hxr : LinearIndependent ℚ ![ℓ ε, ℓ a] := by
      apply (LinearIndependent.iff_fractionRing ℤ ℚ).mp
      apply Fintype.linearIndependent_iff.mpr
      intro e he i
      rw [Fin.sum_univ_two] at he
      have he' : (e 0 : ℝ) * ℓ ε + (e 1 : ℝ) * ℓ a = 0 := by
        simpa [zsmul_eq_mul] using he
      obtain ⟨h0, h1⟩ := hind (e 0) (e 1) he'
      fin_cases i
      · exact h0
      · exact h1
    have hx : LinearIndependent ℚ x := by
      let f : ℝ →ₗ[ℚ] ℂ := Complex.ofRealCLM.toLinearMap.restrictScalars ℚ
      have hf : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr Complex.ofReal_injective
      have h := hxr.map' f hf
      convert h using 1
      funext i
      fin_cases i <;> rfl
    have hy : LinearIndependent ℚ y := by
      rw [linearIndependent_fin2]
      constructor
      · simp only [y, Matrix.cons_val_one, Matrix.cons_val_zero]
        exact mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
          (mul_ne_zero hτ (by exact_mod_cast hNpos.ne')))) Complex.I_ne_zero
      · intro q hq
        have h := congrArg Complex.re hq
        simp [y, Rat.smul_def, Complex.mul_re] at h
    obtain ⟨i, j, hij⟩ := hFEC x y hx hy
    have hζalg (η : Fˣ) : IsAlgebraic ℚ (ζ η ^ (2 * m * N : ℤ)) := by
      apply cubic_algebraic_zpow
      change IsAlgebraic ℚ (σ (η : F) / (‖σ (η : F)‖ : ℂ))
      rw [div_eq_mul_inv]
      exact (cubic_algebraic_embedding σ (η : F)).mul
        (cubic_algebraic_norm (cubic_algebraic_embedding σ (η : F))).inv
    apply hij
    fin_cases i <;> fin_cases j
    · change IsAlgebraic ℚ (Complex.exp ((Real.log (w₂ (ε : F)) : ℂ) * 1))
      rw [mul_one, cubic_exp_log_place w₂ ε.ne_zero]
      exact cubic_algebraic_place w₂ (ε : F)
    · change IsAlgebraic ℚ (Complex.exp ((ℓ ε : ℂ) * (-(τ * N : ℝ) * Complex.I)))
      rw [hεN]
      exact hζalg ε
    · change IsAlgebraic ℚ (Complex.exp ((Real.log (w₂ (a : F)) : ℂ) * 1))
      rw [mul_one, cubic_exp_log_place w₂ a.ne_zero]
      exact cubic_algebraic_place w₂ (a : F)
    · change IsAlgebraic ℚ (Complex.exp ((ℓ a : ℂ) * (-(τ * N : ℝ) * Complex.I)))
      rw [haN]
      exact hζalg a

end


/-! ### Totally real cubic fields -/

section

open NumberField InfinitePlace.Completion

variable {F : Type*} [Field F] [NumberField F]

local notation "Prime" => HeightOneSpectrum (𝓞 F)
local notation "C₁" => MonoidHom.ker (ideleClassNorm F)
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

/-- At a real place the embedding of a square is the square of the absolute value. -/
private theorem cubic_real_embedding_sq {w : InfinitePlace F} (hw : w.IsReal) (x : F) :
    w.embedding (x ^ 2) = ((w x ^ 2 : ℝ) : ℂ) := by
  rw [map_pow, ← InfinitePlace.embedding_of_isReal_apply hw,
    ← InfinitePlace.norm_embedding_of_isReal hw, Real.norm_eq_abs, sq_abs]
  push_cast
  rfl

/-- **The Galois step.** In a field of degree three, at two distinct real places, a
multiplicative relation `|δ|₁ ^ P * |δ|₂ ^ Q = 1` with `(P, Q) ≠ 0` and `|N δ| = 1` forces
`δ` to be a root of unity. If `δ ^ (2P)` is irrational it generates the field, and the
relation gives an automorphism `θ ≠ 1` with `θ(δ²) ^ P * (δ²) ^ Q = 1`; composing with `θ`
permutes the three complex embeddings without fixed points, which forces all the
logarithms `log |φ (δ²)|` to vanish. -/
private theorem cubic_relation_torsion (hdeg : Module.finrank ℚ F = 3)
    {w₁ w₂ : InfinitePlace F} (h₁ : w₁.IsReal) (h₂ : w₂.IsReal) (hne : w₁ ≠ w₂)
    {δ : Fˣ} (hN : |(Algebra.norm ℚ (δ : F) : ℝ)| = 1) {P Q : ℤ} (hPQ : P ≠ 0 ∨ Q ≠ 0)
    (hrel : (P : ℝ) * Real.log (w₁ (δ : F)) + Q * Real.log (w₂ (δ : F)) = 0) :
    IsOfFinOrder δ := by
  have hA : 0 < w₁ (δ : F) := InfinitePlace.pos_iff.mpr δ.ne_zero
  have hB : 0 < w₂ (δ : F) := InfinitePlace.pos_iff.mpr δ.ne_zero
  rcases eq_or_ne Q 0 with hQ | hQ
  · have hP : (P : ℝ) ≠ 0 := by exact_mod_cast hPQ.resolve_right (not_not.mpr hQ)
    rw [hQ, Int.cast_zero, zero_mul, add_zero] at hrel
    exact cubic_isOfFinOrder_of_real_place h₁ (Real.eq_one_of_pos_of_log_eq_zero hA
      ((mul_eq_zero.mp hrel).resolve_left hP))
  rcases eq_or_ne P 0 with hP | hP
  · rw [hP, Int.cast_zero, zero_mul, zero_add] at hrel
    exact cubic_isOfFinOrder_of_real_place h₂ (Real.eq_one_of_pos_of_log_eq_zero hB
      ((mul_eq_zero.mp hrel).resolve_left (by exact_mod_cast hQ)))
  wlog hPpos : 0 < P generalizing P Q
  · exact this (P := -P) (Q := -Q) (Or.inl (neg_ne_zero.mpr hP))
      (by push_cast; linarith) (neg_ne_zero.mpr hQ) (neg_ne_zero.mpr hP) (by omega)
  -- The square `b` of `δ` and the relation between its two real embeddings.
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, P = n := ⟨P.toNat, (Int.toNat_of_nonneg hPpos.le).symm⟩
  have hn : 0 < n := by exact_mod_cast hPpos
  let b : F := (δ : F) ^ 2
  have hb : b ≠ 0 := pow_ne_zero _ δ.ne_zero
  let σ₁ := w₁.embedding
  let σ₂ := w₂.embedding
  have hAB : (w₁ (δ : F) ^ 2) ^ n = (w₂ (δ : F) ^ 2) ^ (-Q) := by
    have hl : Real.log (w₁ (δ : F) ^ n * w₂ (δ : F) ^ Q) = 0 := by
      rw [Real.log_mul (pow_pos hA n).ne' (zpow_pos hB Q).ne', Real.log_pow, Real.log_zpow]
      push_cast at hrel
      exact hrel
    have h1 : w₁ (δ : F) ^ n * w₂ (δ : F) ^ Q = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero (mul_pos (pow_pos hA n) (zpow_pos hB Q)) hl
    have h2 : w₁ (δ : F) ^ n = w₂ (δ : F) ^ (-Q) := by
      rw [zpow_neg]
      exact eq_inv_of_mul_eq_one_left h1
    calc (w₁ (δ : F) ^ 2) ^ n = (w₁ (δ : F) ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = (w₂ (δ : F) ^ (-Q)) ^ 2 := by rw [h2]
      _ = (w₂ (δ : F) ^ 2) ^ (-Q) := by
        rw [← zpow_natCast (w₂ (δ : F) ^ (-Q)) 2, ← zpow_mul, ← zpow_natCast (w₂ (δ : F)) 2,
          ← zpow_mul, mul_comm]
  let x : F := b ^ n
  let y : F := b ^ (-Q)
  have hxy : σ₁ x = σ₂ y := by
    change σ₁ (((δ : F) ^ 2) ^ n) = σ₂ (((δ : F) ^ 2) ^ (-Q))
    rw [map_pow, map_zpow₀, cubic_real_embedding_sq h₁, cubic_real_embedding_sq h₂,
      ← Complex.ofReal_pow,
      ← Complex.ofReal_zpow, hAB]
  have hNb : Algebra.norm ℚ b = 1 := by
    change Algebra.norm ℚ ((δ : F) ^ 2) = 1
    rw [map_pow]
    have : ((Algebra.norm ℚ (δ : F) : ℝ)) ^ 2 = 1 := by rw [← sq_abs, hN, one_pow]
    exact_mod_cast this
  by_cases hx : x ∈ (⊥ : IntermediateField ℚ F)
  · -- A rational power: then `δ ^ (2n) = 1`.
    obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp hx
    have hr3 : r ^ 3 = 1 := by
      have h1 : Algebra.norm ℚ x = r ^ 3 := by rw [← hr, Algebra.norm_algebraMap, hdeg]
      have h2 : Algebra.norm ℚ x = 1 := by
        change Algebra.norm ℚ (b ^ n) = 1
        rw [map_pow, hNb, one_pow]
      rw [← h1, h2]
    have hx1 : x = 1 := by rw [← hr, cubic_rat_eq_one_of_cube hr3, map_one]
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨2 * n, by omega, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, pow_mul, Units.val_one]
    exact hx1
  -- An irrational power generates the field and gives an automorphism.
  have hadj := cubic_adjoin_eq_top hdeg hx
  let σ₁' := σ₁.toRatAlgHom
  let σ₂' := σ₂.toRatAlgHom
  have hroot : Polynomial.aeval y (minpoly ℚ x) = 0 := by
    apply σ₂'.toRingHom.injective
    rw [map_zero]
    change σ₂' (Polynomial.aeval y (minpoly ℚ x)) = 0
    rw [← Polynomial.aeval_algHom_apply]
    change Polynomial.aeval (σ₂ y) (minpoly ℚ x) = 0
    rw [← hxy]
    change Polynomial.aeval (σ₁' x) (minpoly ℚ x) = 0
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  obtain ⟨θ, hθ⟩ := cubic_exists_algHom_of_root hadj hroot
  have hσ : σ₁' = σ₂'.comp θ := cubic_algHom_eq_of_adjoin hadj (by
    change σ₁ x = σ₂ (θ x)
    rw [hθ, hxy])
  have hθne : ∀ φ : F →ₐ[ℚ] ℂ, φ.comp θ ≠ φ := by
    intro φ hφ
    have hid : θ = AlgHom.id ℚ F := by
      ext z
      exact φ.toRingHom.injective (DFunLike.congr_fun hφ z)
    apply hne
    have h12 : σ₁ = σ₂ := by
      ext z
      have := DFunLike.congr_fun hσ z
      rw [hid, AlgHom.comp_id] at this
      exact this
    rw [← InfinitePlace.mk_embedding w₁, ← InfinitePlace.mk_embedding w₂]
    exact congrArg InfinitePlace.mk h12
  -- `θ(b) ^ n * b ^ Q = 1`.
  have hθb : θ b ^ n * b ^ Q = 1 := by
    have h1 : σ₂ (θ x) = σ₂ y := by
      rw [← hxy]
      exact (DFunLike.congr_fun hσ x).symm
    have h2 : θ x = y := σ₂.injective h1
    change θ (b ^ n) = b ^ (-Q) at h2
    rw [map_pow, zpow_neg] at h2
    rw [h2, inv_mul_cancel₀ (zpow_ne_zero _ hb)]
  -- The circulant system over the three embeddings.
  have hcard : Fintype.card (F →ₐ[ℚ] ℂ) = 3 := by rw [AlgHom.card, hdeg]
  have hsurj : Surjective θ := (AlgHom.bijective θ).2
  have hinj : Injective fun φ : F →ₐ[ℚ] ℂ ↦ φ.comp θ := by
    intro φ ψ h
    ext z
    obtain ⟨z', rfl⟩ := hsurj z
    exact DFunLike.congr_fun h z'
  have hsum : ∑ φ : F →ₐ[ℚ] ℂ, Real.log ‖φ b‖ = 0 := by
    have hp := Algebra.norm_eq_prod_embeddings ℚ ℂ b
    rw [hNb, map_one] at hp
    rw [← Real.log_prod (fun φ _ ↦ norm_ne_zero_iff.mpr ((map_ne_zero φ).mpr hb)), ← norm_prod,
      ← hp, norm_one, Real.log_one]
  have hcirc (φ : F →ₐ[ℚ] ℂ) :
      (n : ℝ) * Real.log ‖(φ.comp θ) b‖ + (Q : ℝ) * Real.log ‖φ b‖ = 0 := by
    have h := congrArg (fun z ↦ Real.log ‖φ z‖) hθb
    simp only [map_mul, map_pow, map_zpow₀, map_one, norm_one, Real.log_one, norm_mul, norm_pow,
      norm_zpow] at h
    rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr ((map_ne_zero φ).mpr
      ((map_ne_zero θ).mpr hb)))) (zpow_ne_zero _ (norm_ne_zero_iff.mpr ((map_ne_zero φ).mpr hb))),
      Real.log_pow, Real.log_zpow] at h
    exact h
  have hzero := cubic_circulant hcard (fun φ ↦ φ.comp θ) hinj hθne
    (fun φ ↦ Real.log ‖φ b‖) hsum n Q (Or.inl (by exact_mod_cast hn.ne')) hcirc σ₁'
  have h1 : w₁ (δ : F) ^ 2 = 1 := by
    have hpos : 0 < ‖σ₁' b‖ := norm_pos_iff.mpr ((map_ne_zero σ₁').mpr hb)
    have := Real.eq_one_of_pos_of_log_eq_zero hpos hzero
    change ‖σ₁ ((δ : F) ^ 2)‖ = 1 at this
    rwa [cubic_real_embedding_sq h₁, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)] at this
  exact cubic_isOfFinOrder_of_real_place h₁
    ((pow_eq_one_iff_of_nonneg (AbsoluteValue.nonneg _ _) two_ne_zero).mp h1)

/-- Two independent integral vectors orthogonal to a given integral vector of length
three. -/
private theorem cubic_two_relations (n : Fin 3 → ℤ) :
    ∃ c c' : Fin 3 → ℤ, ∑ k, c k * n k = 0 ∧ ∑ k, c' k * n k = 0 ∧
      ∀ u v : ℤ, (∀ k, u * c k + v * c' k = 0) → u = 0 ∧ v = 0 := by
  by_cases h0 : n 0 = 0
  · by_cases h1 : n 1 = 0
    · refine ⟨![1, 0, 0], ![0, 1, 0], ?_, ?_, ?_⟩
      · simp [Fin.sum_univ_three, h0]
      · simp [Fin.sum_univ_three, h1]
      · intro u v h
        have e0 := h 0
        have e1 := h 1
        simp at e0 e1
        exact ⟨e0, e1⟩
    · refine ⟨![1, 0, 0], ![0, n 2, -n 1], ?_, ?_, ?_⟩
      · simp [Fin.sum_univ_three, h0]
      · simp [Fin.sum_univ_three]
        ring
      · intro u v h
        have e0 := h 0
        have e2 := h 2
        simp at e0 e2
        exact ⟨e0, by rcases e2 with e2 | e2 <;> simp_all⟩
  · refine ⟨![n 1, -n 0, 0], ![n 2, 0, -n 0], ?_, ?_, ?_⟩
    · simp [Fin.sum_univ_three]
      ring
    · simp [Fin.sum_univ_three]
      ring
    · intro u v h
      have e1 := h 1
      have e2 := h 2
      simp at e1 e2
      exact ⟨by rcases e1 with e1 | e1 <;> simp_all, by rcases e2 with e2 | e2 <;> simp_all⟩

end



/-! ### The totally real case -/

section

open NumberField InfinitePlace.Completion

variable {F : Type*} [Field F] [NumberField F]

local notation "Prime" => HeightOneSpectrum (𝓞 F)
local notation "C₁" => MonoidHom.ker (ideleClassNorm F)
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

/-- The logarithms at the place `w` of the integral combination `ε₁ ^ e₀ ε₂ ^ e₁ a ^ e₂`. -/
private theorem cubic_log_combination (w : InfinitePlace F) (η : Fin 3 → Fˣ) (e : Fin 3 → ℤ) :
    Real.log (w ((η 0 ^ e 0 * η 1 ^ e 1 * η 2 ^ e 2 : Fˣ) : F)) =
      ∑ k, (e k : ℝ) * Real.log (w (η k : F)) := by
  rw [cubic_log_place_mul3_zpow, Fin.sum_univ_three]

/-- **Totally real cubic fields.** A repeated pole contradicts the Four Exponentials
Conjecture when the exponents of the character point in an irrational direction, and
contradicts the Galois step `cubic_relation_torsion` when they point in a rational one. -/
private theorem cubic_totallyReal_false (hFEC : FourExponentialsConjecture)
    (hdeg : Module.finrank ℚ F = 3) (ω : PontryaginDual C₁) (hω : ¬ IsOfFinOrder ω)
    (w₁ w₂ w₃ : InfinitePlace F) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal) (h₃ : w₃.IsReal)
    (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ w₃) (h23 : w₂ ≠ w₃)
    (hc : ∀ w : InfinitePlace F, w = w₁ ∨ w = w₂ ∨ w = w₃) (η : Fin 3 → Fˣ)
    (hind : ∀ e : Fin 3 → ℤ, IsOfFinOrder (η 0 ^ e 0 * η 1 ^ e 1 * η 2 ^ e 2) → e = 0)
    (hχ : ∀ k, CubicTorsionDiagonal ω (η k)) : False := by
  obtain ⟨s₁, s₂, hpar⟩ := cubicArch_real_parameters ω w₁ w₂ w₃ h₁ h₂ h₃ h12 h13 h23 hc
  have hs : s₁ ≠ 0 ∨ s₂ ≠ 0 := by
    by_contra h
    push Not at h
    apply hω
    apply cubic_finiteOrder_of_sq_trivial ω
    intro g
    rw [hpar g, h.1, h.2]
    simp
  let L (w : InfinitePlace F) (k : Fin 3) : ℝ := Real.log (w (η k : F))
  -- The norm relation and the torsion relation for the three elements.
  have hsum (k : Fin 3) : ∑ x : InfinitePlace F, (x.mult : ℝ) * Real.log (x (η k : F)) = 0 := by
    obtain ⟨g, hg, -⟩ := hχ k
    exact cubic_log_sum_of_diagonal g hg
  have htor (k : Fin 3) : ∃ N : ℕ, 0 < N ∧ ∃ n : ℤ,
      (N : ℝ) * (s₁ * L w₁ k + s₂ * L w₂ k) = 2 * Real.pi * n := by
    obtain ⟨g, hg, ht⟩ := hχ k
    have h := cubic_sq_isOfFinOrder ω ht
    rw [hpar g, hg w₁, hg w₂, InfinitePlace.norm_embedding_eq,
      InfinitePlace.norm_embedding_eq] at h
    obtain ⟨N, hN, he⟩ := h.exists_pow_eq_one
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at he
    obtain ⟨n, hn⟩ := he
    refine ⟨N, hN, n, ?_⟩
    have h' : (((N : ℝ) * (s₁ * Real.log (w₁ (η k : F)) + s₂ * Real.log (w₂ (η k : F))) : ℝ) :
        ℂ) = ((2 * Real.pi * n : ℝ) : ℂ) := by
      apply mul_right_cancel₀ Complex.I_ne_zero
      push_cast at hn ⊢
      linear_combination hn
    exact_mod_cast h'
  choose N hN n hn using htor
  let M : ℕ := ∏ k, N k
  have hM : 0 < M := Finset.prod_pos fun k _ ↦ hN k
  have hrel (k : Fin 3) : ∃ m : ℤ, (M : ℝ) * (s₁ * L w₁ k + s₂ * L w₂ k) = 2 * Real.pi * m := by
    have hdvd : N k ∣ M := Finset.dvd_prod_of_mem N (Finset.mem_univ k)
    obtain ⟨d, hd⟩ := hdvd
    refine ⟨n k * d, ?_⟩
    rw [hd]
    push_cast
    rw [mul_comm (N k : ℝ), mul_assoc, hn k]
    ring
  choose m hm using hrel
  obtain ⟨c, c', hc0, hc0', hcc⟩ := cubic_two_relations m
  -- The two combinations killed by the character.
  have hkill (e : Fin 3 → ℤ) (he : ∑ k, e k * m k = 0) :
      s₁ * (∑ k, (e k : ℝ) * L w₁ k) + s₂ * (∑ k, (e k : ℝ) * L w₂ k) = 0 := by
    have h : (M : ℝ) * (s₁ * (∑ k, (e k : ℝ) * L w₁ k) + s₂ * (∑ k, (e k : ℝ) * L w₂ k)) =
        2 * Real.pi * ((∑ k, e k * m k : ℤ) : ℝ) := by
      simp only [Fin.sum_univ_three]
      push_cast
      linear_combination (e 0 : ℝ) * hm 0 + (e 1 : ℝ) * hm 1 + (e 2 : ℝ) * hm 2
    rw [he, Int.cast_zero, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hM.ne')
  -- Independence of the logarithms at `w₁`.
  have hL1 (e : Fin 3 → ℤ) (he : ∑ k, (e k : ℝ) * L w₁ k = 0) : e = 0 := by
    apply hind e
    apply cubic_isOfFinOrder_of_real_place h₁
    apply Real.eq_one_of_pos_of_log_eq_zero (InfinitePlace.pos_iff.mpr (Units.ne_zero _))
    rw [cubic_log_combination]
    exact he
  let δ (e : Fin 3 → ℤ) : Fˣ := η 0 ^ e 0 * η 1 ^ e 1 * η 2 ^ e 2
  have hδlog (w : InfinitePlace F) (e : Fin 3 → ℤ) :
      Real.log (w (δ e : F)) = ∑ k, (e k : ℝ) * L w k := cubic_log_combination w η e
  have hδN (e : Fin 3 → ℤ) : |(Algebra.norm ℚ (δ e : F) : ℝ)| = 1 := by
    apply cubic_abs_norm_of_log_sum (δ e).ne_zero
    simp_rw [hδlog, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [mul_left_comm (_ : ℝ) (e _ : ℝ), ← Finset.mul_sum]
    simp only [L]
    simp_rw [hsum, mul_zero, Finset.sum_const_zero]
  have hc_ne : c ≠ 0 := by
    intro h0
    have := (hcc 1 0 (fun k ↦ by simp [h0])).1
    exact one_ne_zero this
  by_cases hrat : ∃ P Q : ℤ, (P ≠ 0 ∨ Q ≠ 0) ∧ s₁ * Q = s₂ * P
  · -- A rational direction: the Galois step.
    obtain ⟨P, Q, hPQ, hsPQ⟩ := hrat
    have hX := hkill c hc0
    set X := ∑ k, (c k : ℝ) * L w₁ k
    set Y := ∑ k, (c k : ℝ) * L w₂ k
    have hPX : (P : ℝ) * X + Q * Y = 0 := by
      rcases hs with hs | hs
      · have : s₁ * ((P : ℝ) * X + Q * Y) = 0 := by linear_combination (P : ℝ) * hX + Y * hsPQ
        exact (mul_eq_zero.mp this).resolve_left hs
      · have : s₂ * ((P : ℝ) * X + Q * Y) = 0 := by
          linear_combination (Q : ℝ) * hX - X * hsPQ
        exact (mul_eq_zero.mp this).resolve_left hs
    have htors := cubic_relation_torsion hdeg h₁ h₂ h12 (hδN c) hPQ
      (by rw [hδlog, hδlog]; exact hPX)
    exact hc_ne (hind c htors)
  · -- An irrational direction: the Four Exponentials Conjecture.
    push Not at hrat
    have hs₂ : s₂ ≠ 0 := by
      intro h0
      exact hrat 1 0 (Or.inl one_ne_zero) (by rw [h0]; simp)
    have hs₁ : s₁ ≠ 0 := by
      intro h0
      exact hrat 0 1 (Or.inr one_ne_zero) (by rw [h0]; simp)
    let X (e : Fin 3 → ℤ) : ℝ := ∑ k, (e k : ℝ) * L w₁ k
    let Y (e : Fin 3 → ℤ) : ℝ := ∑ k, (e k : ℝ) * L w₂ k
    have hY (e : Fin 3 → ℤ) (he : ∑ k, e k * m k = 0) : Y e = -(s₁ / s₂) * X e := by
      have h := hkill e he
      field_simp
      linarith
    let x : Fin 2 → ℂ := ![(X c : ℂ), (X c' : ℂ)]
    let y : Fin 2 → ℂ := ![1, (-(s₁ / s₂) : ℝ)]
    have hxr : LinearIndependent ℚ ![X c, X c'] := by
      apply (LinearIndependent.iff_fractionRing ℤ ℚ).mp
      apply Fintype.linearIndependent_iff.mpr
      intro e he i
      rw [Fin.sum_univ_two] at he
      have he' : ∑ k, ((e 0 * c k + e 1 * c' k : ℤ) : ℝ) * L w₁ k = 0 := by
        simp only [X, Matrix.cons_val_zero, Matrix.cons_val_one, zsmul_eq_mul] at he
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib] at he
        rw [← he]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        push_cast
        ring
      have h0 := hL1 _ he'
      obtain ⟨hu, hv⟩ := hcc (e 0) (e 1) (fun k ↦ congrFun h0 k)
      fin_cases i
      · exact hu
      · exact hv
    have hx : LinearIndependent ℚ x := by
      let f : ℝ →ₗ[ℚ] ℂ := Complex.ofRealCLM.toLinearMap.restrictScalars ℚ
      have hf : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr Complex.ofReal_injective
      have h := hxr.map' f hf
      convert h using 1
      funext i
      fin_cases i <;> rfl
    have hy : LinearIndependent ℚ y := by
      rw [linearIndependent_fin2]
      constructor
      · change ((-(s₁ / s₂) : ℝ) : ℂ) ≠ 0
        exact Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr (div_ne_zero hs₁ hs₂))
      · intro q hq
        change (q : ℚ) • (((-(s₁ / s₂) : ℝ)) : ℂ) = 1 at hq
        rw [Rat.smul_def] at hq
        have hq' : (q : ℝ) * (-(s₁ / s₂)) = 1 := by exact_mod_cast hq
        apply hrat q.den (-q.num) (Or.inl (by exact_mod_cast q.den_nz))
        have hq'' : (q : ℝ) = q.num / q.den := by exact_mod_cast (Rat.num_div_den q).symm
        rw [hq''] at hq'
        have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
        field_simp at hq'
        push_cast
        linarith
    obtain ⟨i, j, hij⟩ := hFEC x y hx hy
    have halg (e : Fin 3 → ℤ) (w : InfinitePlace F) :
        IsAlgebraic ℚ (Complex.exp ((∑ k, (e k : ℝ) * L w k : ℝ) : ℂ)) := by
      rw [← hδlog, cubic_exp_log_place w (δ e).ne_zero]
      exact cubic_algebraic_place w _
    apply hij
    fin_cases i <;> fin_cases j
    · change IsAlgebraic ℚ (Complex.exp ((X c : ℂ) * 1))
      rw [mul_one]
      exact halg c w₁
    · change IsAlgebraic ℚ (Complex.exp ((X c : ℂ) * ((-(s₁ / s₂) : ℝ) : ℂ)))
      rw [← Complex.ofReal_mul, mul_comm, ← hY c hc0]
      exact halg c w₂
    · change IsAlgebraic ℚ (Complex.exp ((X c' : ℂ) * 1))
      rw [mul_one]
      exact halg c' w₁
    · change IsAlgebraic ℚ (Complex.exp ((X c' : ℂ) * ((-(s₁ / s₂) : ℝ) : ℂ)))
      rw [← Complex.ofReal_mul, mul_comm, ← hY c' hc0']
      exact halg c' w₂

end


/-! ### Repeated primary poles in degree three -/

section

open NumberField InfinitePlace.Completion

variable {F : Type*} [Field F] [NumberField F]

local notation "Prime" => HeightOneSpectrum (𝓞 F)
local notation "C₁" => MonoidHom.ker (ideleClassNorm F)

/-- Two fundamental units of a field of unit rank two are multiplicatively independent. -/
private theorem cubic_fundSystem_independent (hr : NumberField.Units.rank F = 2) (e₀ e₁ : ℤ)
    (h : IsOfFinOrder (NumberField.Units.fundSystem F ⟨0, by omega⟩ ^ e₀ *
      NumberField.Units.fundSystem F ⟨1, by omega⟩ ^ e₁)) : e₀ = 0 ∧ e₁ = 0 := by
  let B := NumberField.Units.basisModTorsion F
  let i₀ : Fin (NumberField.Units.rank F) := ⟨0, by omega⟩
  let i₁ : Fin (NumberField.Units.rank F) := ⟨1, by omega⟩
  have hli : LinearIndependent ℤ ![B i₀, B i₁] := by
    have h := B.linearIndependent.comp ![i₀, i₁] (by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [i₀, i₁])
    convert h using 1
    funext k
    fin_cases k <;> rfl
  apply (LinearIndependent.pair_iff.mp hli) e₀ e₁
  have hmem : NumberField.Units.fundSystem F i₀ ^ e₀ * NumberField.Units.fundSystem F i₁ ^ e₁ ∈
      NumberField.Units.torsion F := (CommGroup.mem_torsion _).mpr h
  have hq := (QuotientGroup.eq_one_iff _).mpr hmem
  have h2 := congrArg Additive.ofMul hq
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, QuotientGroup.mk_zpow, ofMul_mul, ofMul_zpow,
    ofMul_zpow, NumberField.Units.fundSystem_mk, NumberField.Units.fundSystem_mk] at h2
  exact h2

/-- Paper: Theorem 7.3.3.4, p. 360, with the coefficient change on p. 349.
In a number field of degree three, if the Four Exponentials Conjecture holds, an
infinite-order norm-one character has no repeated primary pole: no two distinct finite
places above one rational prime are poles of a quasi-character on its component.
Over a complex cubic field with purely angular character, and over a totally real cubic
field when the exponents of the character point in a rational direction, the proof uses
no conjecture. See duuren's argument on issue #7336. -/
public theorem cubic_repeatedPrimaryPole_false_of_fourExponentials
    (hFEC : FourExponentialsConjecture) (hdeg : Module.finrank ℚ F = 3)
    {T : Finset Prime} (ω : PontryaginDual C₁) (hω : ¬ IsOfFinOrder ω)
    (hT : NormOneCharacterUnramifiedOutside ω T) (p : HeightOneSpectrum (𝓞 ℚ))
    (c : QuasiCharacter (SIdeleQuotient F T))
    (hc : ∀ x : (sIdeleQuotientNorm F T).ker, c x.val = (sLocalNormOneCharacter T ω hT x : ℂ))
    (v w : T) (hvw : v ≠ w) (hvp : v.val ∈ sLocalPrimaryPlaces T p)
    (hwp : w.val ∈ sLocalPrimaryPlaces T p)
    (hv : v ∈ sLocalFinitePolePlaces c) (hw : w ∈ sLocalFinitePolePlaces c) : False := by
  obtain ⟨a, ha, haχ⟩ := cubic_pole_torsion_diagonal ω hT p c hc v w hvw hvp hwp hv hw
  have hav : cubicOrd v.val a ≠ 1 := by
    rw [Ne, cubicOrd_eq_one]
    exact (ha v.val).mpr (by simp)
  let U : (𝓞 F)ˣ →* Fˣ := Units.map (algebraMap (𝓞 F) F).toMonoidHom
  have hU : Injective U := Units.map_injective (FaithfulSMul.algebraMap_injective (𝓞 F) F)
  rcases cubic_signature hdeg with ⟨hr, hc0⟩ | ⟨hr, hc1⟩
  · -- Totally real: three real places and two fundamental units.
    have hreal (x : InfinitePlace F) : x.IsReal :=
      (InfinitePlace.isReal_or_isComplex x).resolve_right fun hx ↦
        (Fintype.card_eq_zero_iff.mp hc0).false ⟨x, hx⟩
    have hcard : Fintype.card (InfinitePlace F) = 3 := by
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hr, hc0]
    let e := Fintype.equivFinOfCardEq hcard
    have hne (i j : Fin 3) (hij : i ≠ j) : e.symm i ≠ e.symm j := e.symm.injective.ne hij
    have hall (x : InfinitePlace F) : x = e.symm 0 ∨ x = e.symm 1 ∨ x = e.symm 2 := by
      have h : e x = 0 ∨ e x = 1 ∨ e x = 2 :=
        (show ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 from by decide) (e x)
      rcases h with h | h | h
      · exact Or.inl (by rw [← h, Equiv.symm_apply_apply])
      · exact Or.inr (Or.inl (by rw [← h, Equiv.symm_apply_apply]))
      · exact Or.inr (Or.inr (by rw [← h, Equiv.symm_apply_apply]))
    have hrank : NumberField.Units.rank F = 2 := by
      simp [NumberField.Units.rank, hcard]
    let u₀ := NumberField.Units.fundSystem F ⟨0, by omega⟩
    let u₁ := NumberField.Units.fundSystem F ⟨1, by omega⟩
    let η : Fin 3 → Fˣ := ![U u₀, U u₁, a]
    have hind (k : Fin 3 → ℤ) (hk : IsOfFinOrder (η 0 ^ k 0 * η 1 ^ k 1 * η 2 ^ k 2)) :
        k = 0 := by
      have hU₀ : cubicOrd v.val (U u₀) = 1 := cubicOrd_unit _ _
      have hU₁ : cubicOrd v.val (U u₁) = 1 := cubicOrd_unit _ _
      have hord : (cubicOrd v.val a) ^ k 2 = 1 := by
        have h1 := ((cubicOrd v.val).isOfFinOrder hk).eq_one'
        simpa only [η, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, map_mul, map_zpow, hU₀, hU₁, one_zpow,
          one_mul] using h1
      have hk2 : k 2 = 0 := by
        have he : k 2 * (cubicOrd v.val a).toAdd = 0 := congrArg Multiplicative.toAdd hord
        refine (mul_eq_zero.mp he).resolve_right fun h ↦ hav ?_
        exact Multiplicative.toAdd.injective (by simpa using h)
      have hk' : IsOfFinOrder (u₀ ^ k 0 * u₁ ^ k 1) := by
        rw [← hU.isOfFinOrder_iff, map_mul, map_zpow, map_zpow]
        simpa only [η, hk2, zpow_zero, mul_one, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons] using hk
      obtain ⟨h0, h1⟩ := cubic_fundSystem_independent hrank (k 0) (k 1) hk'
      funext j
      fin_cases j
      · exact h0
      · exact h1
      · exact hk2
    have hχ (k : Fin 3) : CubicTorsionDiagonal ω (η k) := by
      fin_cases k
      · exact cubic_unit_torsion_diagonal ω u₀
      · exact cubic_unit_torsion_diagonal ω u₁
      · exact haχ
    exact cubic_totallyReal_false hFEC hdeg ω hω (e.symm 0) (e.symm 1) (e.symm 2)
      (hreal _) (hreal _) (hreal _) (hne 0 1 (by decide)) (hne 0 2 (by decide))
      (hne 1 2 (by decide)) hall η hind hχ
  · -- Complex cubic: one real place, one complex place and one fundamental unit.
    obtain ⟨⟨w₁, h₁⟩, hw₁⟩ := Fintype.card_eq_one_iff.mp hr
    obtain ⟨⟨w₂, h₂⟩, hw₂⟩ := Fintype.card_eq_one_iff.mp hc1
    have hd : w₁ ≠ w₂ := fun h ↦ (InfinitePlace.not_isReal_iff_isComplex.mpr h₂) (h ▸ h₁)
    have hall (x : InfinitePlace F) : x = w₁ ∨ x = w₂ := by
      rcases InfinitePlace.isReal_or_isComplex x with hx | hx
      · exact Or.inl (congrArg Subtype.val (hw₁ ⟨x, hx⟩))
      · exact Or.inr (congrArg Subtype.val (hw₂ ⟨x, hx⟩))
    have hcard : Fintype.card (InfinitePlace F) = 2 := by
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hr, hc1]
    obtain ⟨u, hu⟩ := cubicArch_exists_unit F hcard
    have hε : ¬ IsOfFinOrder (U u) := by
      intro h
      apply hu
      exact (CommGroup.mem_torsion u).mpr (hU.isOfFinOrder_iff.mp h)
    exact cubic_complex_false hFEC hdeg ω hω w₁ w₂ h₁ h₂ hd hall (U u) hε
      (fun x ↦ cubicOrd_unit x u) (cubic_unit_torsion_diagonal ω u) a v.val hav haχ

/-- Paper: Theorem 7.3.3.4, p. 360, with the coefficient change on p. 349.
In a number field of degree three, if the Four Exponentials Conjecture holds, the primary
finite pole multiplicity of a quasi-character on the component of an infinite-order
norm-one character is at most one. -/
public theorem cubic_primaryPoleMultiplicity_le_one_of_fourExponentials
    (hFEC : FourExponentialsConjecture) (hdeg : Module.finrank ℚ F = 3)
    {T : Finset Prime} (ω : PontryaginDual C₁) (hω : ¬ IsOfFinOrder ω)
    (hT : NormOneCharacterUnramifiedOutside ω T) (p : HeightOneSpectrum (𝓞 ℚ))
    (c : QuasiCharacter (SIdeleQuotient F T))
    (hc : ∀ x : (sIdeleQuotientNorm F T).ker, c x.val = (sLocalNormOneCharacter T ω hT x : ℂ)) :
    sLocalFinitePoleMultiplicity (sLocalPrimaryPlaces T p) c ≤ 1 := by
  by_contra! h
  obtain ⟨v, hv, w, hw, hvw⟩ := Finset.one_lt_card.mp h
  obtain ⟨hv, hvp⟩ := Finset.mem_filter.mp hv
  obtain ⟨hw, hwp⟩ := Finset.mem_filter.mp hw
  exact cubic_repeatedPrimaryPole_false_of_fourExponentials hFEC hdeg ω hω hT p c hc v w hvw
    hvp hwp hv hw

end

/-! ### The open statement of Theorem 7.3.3.4 in degree three -/

section

open Classical

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
variable {S T : Finset (HeightOneSpectrum (𝓞 F))}

local notation "C₁" => (ideleClassNorm F).ker
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "J(" T ")" => SIdeleQuotient F T
local notation "m(" T ")" => sIdeleQuotientNorm F T
local notation "J₁(" T ")" => (m(T)).ker
local notation "PicTrivial" => Subsingleton (CommRing.Pic ((S : Set V).integer F))
local notation "descend(" h ", " ω ", " hu ")" =>
  sLocalNormOneCharacter (F := F) T ω
    (NormOneCharacterUnramifiedOutside.mono (F := F) hu h)
local notation "Iₚ(" p ", " ω ")" => SLocalOrbitalIndex (F := F) (S := T)
  (sLocalPrimaryPlaces (F := F) T p) ω

/-- Paper: Theorem 7.3.3.4, p. 360, with the coefficient change on p. 349.
The open statement `sLocalPWOrbital_bases_bounded_interpolation_laurent_other_prime_shift_minima`
of `Sec3b.lean` (issue #7336), word for word, for a field of degree three, proved from the
Four Exponentials Conjecture. In degree three that conjecture excludes repeated primary
poles (`cubic_primaryPoleMultiplicity_le_one_of_fourExponentials`), so the set `A` of the
statement is empty and its hypothesis that `A` has infinitely many centers fails. What the
open statement still asks for beyond the conjecture is the case of degree at least four. -/
public theorem cubic_shift_minima_of_fourExponentials
    (hFEC : FourExponentialsConjecture) (hdeg : Module.finrank ℚ F = 3)
    {S₀ : Finset V} (hST : S ⊆ T) (_hT : T = S ∪ S₀) (_hdis : Disjoint S S₀)
    (_hsat : IsSaturatedPlaceSet (F := F) S₀) (_hPic : PicTrivial)
    (p : Vℚ) (_hp₀ : sLocalPrimaryPlaces (F := F) T p ⊆ S₀)
    (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu)) (_hinf : ¬ IsOfFinOrder ω)
    (τ : ℝ≥0ˣ →ₜ* J(T)) (_hτ : RightInverse τ (m(T))) (v w : T)
    (_hv : v.val ∉ sLocalPrimaryPlaces T p) (_hw : w.val ∈ sLocalPrimaryPlaces T p)
    (u : (v.val.adicCompletion F)ˣ) (_hu : ‖u.val‖ = (v.val.asIdeal.absNorm : ℝ)⁻¹)
    (_hind : ¬ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ v.val.asIdeal.absNorm ^ k = w.val.asIdeal.absNorm ^ l) :
    let s (j : Iₚ(p, χ)) := (existsUnique_complexPower (j.val.1.comp τ)).exists.choose
    let z (j : Iₚ(p, χ)) := sLocalFiniteRestriction v j.val.1 u
    let E (j : Iₚ(p, χ)) := finiteLocalEulerFactor v.val (sLocalFiniteRestriction v j.val.1)
    let A := {j : Iₚ(p, χ) | j.val.2 ≠ 0 ∧ w ∈ sLocalFinitePolePlaces j.val.1 ∧ 1 < ‖E j‖}
    let H (j : Iₚ(p, χ)) := 2 + ‖s j‖
    let R := {j ∈ A | ∀ k ∈ A, k.val.1 ≠ j.val.1 → H k ≤ H j ^ 2 → ‖1 - z j‖ < ‖1 - z k‖}
    1 < (sLocalPrimaryPlaces (F := F) T p).card → ((fun j ↦ j.val.1) '' A).Infinite →
    ¬ BddAbove ((fun j ↦ ‖E j‖) '' A) →
    (¬ ∃ σ : ℂ, ∃ N : ℕ, 0 < N ∧ ∀ j ∈ A,
      Complex.exp (N * (-(Real.log w.val.asIdeal.absNorm : ℂ) * (s j - σ))) = 1 ∧
      z j ^ N = Complex.exp (N * (-(Real.log v.val.asIdeal.absNorm : ℂ) * (s j - σ)))) →
    (∀ j ∈ R, ∀ k ∈ R, j.val.1 ≠ k.val.1 → H j ≤ H k → H j ^ 2 < H k ∧ ‖1 - z k‖ < ‖1 - z j‖) →
    ((fun j ↦ j.val.1) '' R).Infinite → ¬ BddAbove ((fun j ↦ ‖1 - z j‖⁻¹) '' R) →
    2 < Module.finrank ℚ F →
    (¬ ∀ x : J₁(T), χ x = 1 →
      ∃ n : ℕ, 0 < n ∧ ∃ t : (SAdeleRing F T)ˣ, (∀ σ : InfinitePlace F, t.val.1 σ = 1) ∧
        (∀ i : T, ‖t.val.2 i‖ = 1) ∧ x.val ^ n = QuotientGroup.mk t) →
    ∃ d : ℕ, ∃ C ≥ (0 : ℝ), ∀ j ∈ R, 1 ≤ C * (1 + ‖s j‖) ^ d * ‖1 - z j‖ := by
  subst _hχ
  intro s z E A H R _ hA
  exfalso
  apply hA
  convert Set.finite_empty
  apply Set.image_eq_empty.mpr
  ext j
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hj
  have hmult := cubic_primaryPoleMultiplicity_le_one_of_fourExponentials hFEC hdeg ω _hinf
    (NormOneCharacterUnramifiedOutside.mono hu hST) p j.val.1
    (fun x ↦ by have h := DFunLike.congr_fun j.property.1 x; exact h)
  have hlt := j.property.2
  have hj2 : j.val.2 ≠ 0 := hj.1
  omega

end

end RiemannMasullo.Isolated
