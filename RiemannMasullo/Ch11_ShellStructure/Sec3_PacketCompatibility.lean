module

public import Mathlib.Analysis.Normed.Operator.Banach

/-! # Compatibility of two Paley–Wiener packet lifts

For the fixed-box lifting question in (11.3.1.3)–(11.3.1.4), p. 494, this
isolates an obstruction to combining two packet lifts in one preceding stage.
The hypotheses describe the bounded quotient maps and the induced difference
operator on the second packet. Nothing imports this file.
-/

public section

open Function Set

namespace RiemannMasullo.Isolated

/-- Paper: (11.3.1.3)–(11.3.1.4), p. 494.
Fix a lift of the first packet. A second packet can be realized by the same
stage vector exactly when its discrepancy from the fixed lift is in the range
of the first period difference acting on the second quotient.
Reconstruction: This is the two-packet compatibility condition in one fixed box. -/
theorem packetJointLift_iff
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E Q₁ Q₂ : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup Q₁] [NormedSpace 𝕜 Q₁]
    [NormedAddCommGroup Q₂] [NormedSpace 𝕜 Q₂]
    (q₁ : E →L[𝕜] Q₁) (q₂ : E →L[𝕜] Q₂) (hq₂ : Surjective q₂)
    (A : E →L[𝕜] E) (D : Q₂ →L[𝕜] Q₂)
    (hker : q₁.toLinearMap.ker = A.toLinearMap.range) (hcomp : ∀ v, q₂ (A v) = D (q₂ v))
    (x : E) (y : Q₂) :
    (q₁ x, y) ∈ Set.range (fun v ↦ (q₁ v, q₂ v)) ↔ y - q₂ x ∈ Set.range D := by
  constructor
  · rintro ⟨v, hv⟩
    have hmem : v - x ∈ A.toLinearMap.range := by
      rw [← hker, LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.mpr (congrArg Prod.fst hv)
    obtain ⟨u, hu⟩ := hmem
    change A u = v - x at hu
    have hv₂ : q₂ v = y := congrArg Prod.snd hv
    refine ⟨q₂ u, ?_⟩
    rw [← hcomp, hu, map_sub, hv₂]
  · rintro ⟨z, hz⟩
    obtain ⟨u, rfl⟩ := hq₂ z
    have hzero : q₁ (A u) = 0 := by
      change q₁.toLinearMap (A u) = 0
      apply LinearMap.mem_ker.mp
      rw [hker]
      exact ⟨u, rfl⟩
    refine ⟨x + A u, Prod.ext ?_ ?_⟩
    · change q₁ (x + A u) = q₁ x
      rw [map_add, hzero, add_zero]
    · change q₂ (x + A u) = y
      rw [map_add, hcomp, hz, add_comm, sub_add_cancel]

private theorem packetDifference_range_not_isClosed
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace 𝕜 Q] [CompleteSpace Q]
    (D : Q →L[𝕜] Q) (P : ℕ → Q →L[𝕜] Q) (z : ℕ → Q) (μ : ℕ → 𝕜) {C : ℝ}
    (hC : 0 ≤ C) (hP : ∀ n, ‖P n‖ ≤ C)
    (hz : ∀ n, z n ∈ Set.range D) (hnorm : ∀ n, ‖z n‖ = 1)
    (hfix : ∀ n, P n (z n) = z n) (hmul : ∀ n v, P n (D v) = μ n • P n v)
    (hsmall : ∀ ε > 0, ∃ n, ‖μ n‖ < ε) :
    ¬ IsClosed (Set.range D) := by
  intro hclosed
  let : CompleteSpace D.toLinearMap.range := hclosed.completeSpace_coe
  have hsurj : Surjective D.rangeRestrict := by
    intro y
    obtain ⟨v, hv⟩ := y.property
    exact ⟨v, Subtype.ext hv⟩
  obtain ⟨K, hK, hpre⟩ := D.rangeRestrict.exists_preimage_norm_le hsurj
  have hpos : 0 < C * K + 1 := add_pos_of_nonneg_of_pos (mul_nonneg hC hK.le) zero_lt_one
  obtain ⟨n, hn⟩ := hsmall (1 / (C * K + 1)) (div_pos zero_lt_one hpos)
  obtain ⟨v, hv, hvnorm⟩ := hpre ⟨z n, hz n⟩
  have hv' : D v = z n := congrArg Subtype.val hv
  have hvle : ‖v‖ ≤ K := by
    change ‖v‖ ≤ K * ‖z n‖ at hvnorm
    simpa only [hnorm n, mul_one] using hvnorm
  have hPv : ‖P n v‖ ≤ C * K :=
    ((P n).le_opNorm v).trans (mul_le_mul (hP n) hvle (norm_nonneg v) hC)
  have hone : 1 ≤ ‖μ n‖ * (C * K) := calc
    1 = ‖P n (D v)‖ := by rw [hv', hfix, hnorm]
    _ = ‖μ n‖ * ‖P n v‖ := by rw [hmul, norm_smul]
    _ ≤ ‖μ n‖ * (C * K) := mul_le_mul_of_nonneg_left hPv (norm_nonneg _)
  refine (not_lt_of_ge hone) ?_
  calc
    ‖μ n‖ * (C * K) ≤ ‖μ n‖ * (C * K + 1) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)
    _ < 1 := (lt_div_iff₀ hpos).mp hn

/-- Paper: (11.3.1.3)–(11.3.1.4), p. 494.
In a completed stage with two quotient maps, suppose the kernel of the first map
is a period-difference range. On the second quotient the same difference acts
on uniformly bounded mode projections by multipliers arbitrarily close to zero.
If these modes belong to the difference range, the jointly realizable pairs
form a nonclosed subspace of the product of the two packet quotients.

Reconstruction: This is a test for simultaneous lifting in two packet quotients
with the same preceding fixed box. It applies to the period differences for
two distinct rational primes via the second packet's circle action. -/
theorem packetJointLift_range_not_isClosed
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E Q₁ Q₂ : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup Q₁] [NormedSpace 𝕜 Q₁]
    [NormedAddCommGroup Q₂] [NormedSpace 𝕜 Q₂] [CompleteSpace Q₂]
    (q₁ : E →L[𝕜] Q₁) (q₂ : E →L[𝕜] Q₂) (hq₂ : Surjective q₂)
    (A : E →L[𝕜] E) (D : Q₂ →L[𝕜] Q₂)
    (hker : q₁.toLinearMap.ker = A.toLinearMap.range) (hcomp : ∀ v, q₂ (A v) = D (q₂ v))
    (P : ℕ → Q₂ →L[𝕜] Q₂) (z : ℕ → Q₂) (μ : ℕ → 𝕜) {C : ℝ}
    (hC : 0 ≤ C) (hP : ∀ n, ‖P n‖ ≤ C)
    (hz : ∀ n, z n ∈ Set.range D) (hnorm : ∀ n, ‖z n‖ = 1)
    (hfix : ∀ n, P n (z n) = z n) (hmul : ∀ n v, P n (D v) = μ n • P n v)
    (hsmall : ∀ ε > 0, ∃ n, ‖μ n‖ < ε) :
    ¬ IsClosed (Set.range fun v ↦ (q₁ v, q₂ v)) := by
  intro hclosed
  have heq : (fun y : Q₂ ↦ ((0 : Q₁), y)) ⁻¹' (Set.range fun v ↦ (q₁ v, q₂ v)) =
      Set.range D := by
    ext y
    change ((0 : Q₁), y) ∈ Set.range (fun v ↦ (q₁ v, q₂ v)) ↔ y ∈ Set.range D
    simpa only [map_zero, sub_zero] using packetJointLift_iff q₁ q₂ hq₂ A D hker hcomp 0 y
  apply packetDifference_range_not_isClosed D P z μ hC hP hz hnorm hfix hmul hsmall
  rw [← heq]
  exact hclosed.preimage (continuous_const.prodMk continuous_id)

end RiemannMasullo.Isolated
