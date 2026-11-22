module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a

/-! # §7.3.1 Statements that are false as printed -/

@[expose] public noncomputable section

open IsDedekindDomain NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

local notation "chart(" field ", " places ", " χ ")" =>
  quasiCharacterNormTwist (sIdeleQuotientNorm field places)
  (isProperMap_sIdeleQuotientNorm field places).continuous
  ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (χ))
local notation "period(" places ", " v ")" =>
  (2 * Real.pi / Real.log ((v : places).val.asIdeal.absNorm : ℝ))
local notation "phase(" field ", " places ", " χ ", " v ", " u ", " t ")" =>
  (t ∈ Ico 0 period(places, v) ∧
    sLocalFiniteRestriction v (chart(field, places, χ) (-(t : ℂ) * Complex.I)) u = 1)
local notation "uniformizerNorm(" field ", " places ", " v ", " u ")" =>
  (‖(↑(u) : (v : places).val.adicCompletion field)‖ = ((v : places).val.asIdeal.absNorm : ℝ)⁻¹)

/-- Paper: Discussion after (7.3.1.11), p. 344.
At a common pole, the phases at two places over the same rational prime differ by a unique
integer multiple of the period for that prime. The integer norm of the rational place is p. -/
def Printed.sLocalOrbitalPhase_sub : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
    let Jₛ := SIdeleQuotient F S
    IsSaturatedPlaceSet S →
    ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (χ : PontryaginDual Jₛ) (v w : S),
      v.val ∈ sLocalPrimaryPlaces S p → w.val ∈ sLocalPrimaryPlaces S p →
      ∀ (uᵥ : (v.val.adicCompletion F)ˣ) (u_w : (w.val.adicCompletion F)ˣ),
        uniformizerNorm(F, S, v, uᵥ) → uniformizerNorm(F, S, w, u_w) →
        ∀ (tᵥ t_w : ℝ), phase(F, S, χ, v, uᵥ, tᵥ) → phase(F, S, χ, w, u_w, t_w) →
          ∀ c : QuasiCharacter Jₛ, (∃ s, c = chart(F, S, χ) s) →
            v ∈ sLocalFinitePolePlaces (F := F) (S := S) c →
            w ∈ sLocalFinitePolePlaces (F := F) (S := S) c →
            ∃! n : ℤ, tᵥ - t_w = (n : ℝ) * (2 * Real.pi / Real.log (p.asIdeal.absNorm : ℝ))

/-- Paper: Discussion after (7.3.1.11), p. 344.
Take F = ℚ(∛2), p = 5, and S consisting of the places over 5 together with the archimedean
places. Modulo 5, X³ - 2 factors as (X - 3)(X² + 3X + 4), with irreducible quadratic
and discriminant of X³ - 2 prime to 5. The local residue sizes are 5 and 25.
With T = 2π/log 5 and χ = |·|^(3iT/4), take the common pole c = 1.
The local phases are 3T/4 and T/4, so their difference is T/2. -/
theorem Printed.sLocalOrbitalPhase_sub_false : ¬ Printed.sLocalOrbitalPhase_sub := by sorry

end RiemannMasullo
