module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Group.Neighborhood

/-! # Continuous actions and splittings on kernel quotients -/

public section

namespace RiemannMasullo

/-- A discrete subgroup acting by continuous linear endomorphisms descends to a
jointly continuous action on the quotient by an invariant kernel. -/
theorem exists_ker_quotientAction {R U X Y : Type*} [Ring R] [Group U] [TopologicalSpace U]
    [AddCommGroup X] [Module R X] [TopologicalSpace X]
    [AddCommGroup Y] [Module R Y] [TopologicalSpace Y] (N : Subgroup U) [DiscreteTopology N]
    (A : X →L[R] Y) (ρ : U →* (X →L[R] X))
    (hinv : ∀ (g : N) (f : X), f ∈ A.ker → ρ g.val f ∈ A.ker) :
    let V := X ⧸ A.ker
    ∃ r : N →* (V →L[R] V),
      (∀ (g : N) (f : X), r g (A.ker.mkQ f) = A.ker.mkQ (ρ g.val f)) ∧
      Continuous (fun z : N × V ↦ r z.1 z.2) := by
  let r₀ := ρ.comp N.subtype
  let act (g : N) := A.ker.liftQL (A.ker.mkQL.comp (r₀ g)) fun x hx ↦
    (Submodule.Quotient.mk_eq_zero A.ker).mpr (hinv g x hx)
  have happ (g : N) (x : X) : act g (A.ker.mkQ x) = A.ker.mkQ (r₀ g x) := rfl
  let r : N →* ((X ⧸ A.ker) →L[R] (X ⧸ A.ker)) :=
    { toFun := act
      map_one' := by
        apply ContinuousLinearMap.ext
        intro v
        obtain ⟨x, rfl⟩ := A.ker.mkQ_surjective v
        rw [happ, map_one]
        rfl
      map_mul' := fun g k ↦ by
        apply ContinuousLinearMap.ext
        intro v
        obtain ⟨x, rfl⟩ := A.ker.mkQ_surjective v
        rw [mul_apply_eq_comp, happ, happ, happ, map_mul, mul_apply_eq_comp] }
  exact ⟨r, happ, continuous_prod_of_discrete_left.mpr fun g ↦ (act g).continuous⟩

/-- A continuous linear map with a continuous linear right inverse identifies its
kernel quotient continuously and linearly with its target. -/
theorem exists_ker_quotientEquiv_of_rightInverse {R X Y : Type*} [Ring R]
    [AddCommGroup X] [Module R X] [TopologicalSpace X] [AddCommGroup Y] [Module R Y] [TopologicalSpace Y]
    (A : X →L[R] Y) (J : Y →L[R] X) (hJ : ∀ y, A (J y) = y) :
    ∃ e : (X ⧸ A.ker) ≃L[R] Y, ∀ x, e (A.ker.mkQ x) = A x := by
  have hr : Function.RightInverse J A := hJ
  let e := A.toLinearMap.quotKerEquivOfSurjective hr.surjective
  have he : Continuous e := A.ker.isQuotientMap_mkQL.continuous_iff.mpr A.continuous
  have hi : Continuous e.symm := (A.ker.mkQL.continuous.comp J.continuous).congr fun y ↦
    (A.toLinearMap.quotKerEquivOfSurjective_symm_apply hr.surjective (J y)).symm.trans
      (congrArg e.symm (hJ y))
  exact ⟨⟨e, he, hi⟩, fun _ ↦ rfl⟩

section

open Function Topology

/-- A quotient linear map identifies its target with the quotient by any submodule equal to its kernel. -/
theorem exists_quotient_equiv_of_kernel {R X Y : Type*} [Ring R]
    [AddCommGroup X] [Module R X] [TopologicalSpace X]
    [AddCommGroup Y] [Module R Y] [TopologicalSpace Y]
    (A : X →L[R] Y) (hA : IsQuotientMap A) (N : Submodule R X) (hN : A.ker = N) :
    ∃ F : (X ⧸ N) ≃L[R] Y, ∀ x, F (N.mkQ x) = A x := by
  subst N
  let equiv := A.toLinearMap.quotKerEquivOfSurjective hA.surjective
  have hf : (equiv : (X ⧸ A.ker) → Y) ∘ A.ker.mkQ = A :=
    funext (A.toLinearMap.quotKerEquivOfSurjective_apply_mk hA.surjective)
  have hb : (equiv.symm : Y → (X ⧸ A.ker)) ∘ A = A.ker.mkQ :=
    funext (A.toLinearMap.quotKerEquivOfSurjective_symm_apply hA.surjective)
  exact ⟨{ equiv with
    continuous_toFun := A.ker.isQuotientMap_mkQ.continuous_iff.mpr (hf.symm ▸ A.continuous)
    continuous_invFun := hA.continuous_iff.mpr (hb.symm ▸ A.ker.continuous_mkQ) }, congrFun hf⟩

/-- For a linear map open onto its range, scaling the induced isomorphism by a nonzero
scalar gives a topological isomorphism onto any submodule equal to the range. -/
theorem quotient_equiv_of_scaled_range {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [ContinuousConstSMul ℂ Y]
    (A : X →L[ℂ] Y) (ho : IsOpenMap A.rangeRestrict) (c : ℂ) (hc : c ≠ 0)
    (H : Submodule ℂ Y) (hH : A.range = H) :
    ∃ F : (X ⧸ A.ker) ≃L[ℂ] H, ∀ v, (F v).val = c • A.ker.liftQL A le_rfl v := by
  subst H
  let U : X →L[ℂ] A.range := c • A.rangeRestrict
  have hq : IsQuotientMap U := (isHomeomorph_smul₀ (α := A.range) hc).isQuotientMap.comp
    (ho.isQuotientMap A.rangeRestrict.continuous A.toLinearMap.surjective_rangeRestrict)
  have hk : U.ker = A.ker := by
    ext x
    change c • A.rangeRestrict x = 0 ↔ A x = 0
    have hinj := (isHomeomorph_smul₀ (α := A.range) hc).injective
    rw [← smul_zero c, hinj.eq_iff, Subtype.ext_iff]
    rfl
  refine (exists_quotient_equiv_of_kernel U hq _ hk).elim fun F hF ↦ ⟨F, fun v ↦ ?_⟩
  obtain ⟨x, rfl⟩ := A.ker.mkQ_surjective v
  exact congrArg Subtype.val (hF x)

/-- Precomposition with a surjection and multiplication by a nonzero scalar preserve the range. -/
theorem range_smul_comp_of_surjective {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (A B : X →L[ℂ] Y) (T : Y →L[ℂ] Y) (hB : Surjective B) (c : ℂ) (hc : c ≠ 0)
    (h : ∀ x, A x = c • T (B x)) : A.range = T.range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨c • B x, (T.map_smul _ _).trans (h x).symm⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, hx⟩ := hB (c⁻¹ • z)
    exact ⟨x, (h x).trans (by rw [hx, map_smul, smul_inv_smul₀ hc]; rfl)⟩

/-- Composing a surjective open linear map with a scalar multiple of a retraction
gives a map that is open onto its range. -/
theorem isOpenMap_rangeRestrict_of_factor {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [ContinuousConstSMul ℂ Y] (F P : X →L[ℂ] Y) (A : Y →L[ℂ] Y)
    (hsur : Surjective P) (ho : IsOpenMap P) (c : ℂ) (hc : c ≠ 0)
    (h : ∀ x, F x = c • A (P x)) (hfix : ∀ x, A (F x) = F x) :
    IsOpenMap F.rangeRestrict := by
  let T := (c • A).codRestrict F.range fun y ↦ (hsur y).elim fun x hx ↦
    ⟨x, (h x).trans (congrArg (fun z ↦ c • A z) hx)⟩
  let s : F.range →L[ℂ] Y := c⁻¹ • F.range.subtypeL
  have hs : (T : Y → F.range) ∘ s = id := by
    funext y
    apply Subtype.ext
    have hy : A y.val = y.val := y.property.elim fun x hx ↦ (congrArg A hx).symm.trans ((hfix x).trans hx)
    change c • A (c⁻¹ • y.val) = y.val
    rw [map_smul, hy, smul_inv_smul₀ hc]
  have hq : IsQuotientMap T := IsQuotientMap.of_comp s.continuous T.continuous
    (Eq.mpr (congrArg IsQuotientMap hs) IsQuotientMap.id)
  have ht := (AddMonoidHom.isOpenQuotientMap_of_isQuotientMap hq).isOpenMap
  have he : (T : Y → F.range) ∘ P = F.rangeRestrict := funext fun x ↦ Subtype.ext (h x).symm
  exact Eq.mp (congrArg IsOpenMap he) (ht.comp ho)

/-- The range of a continuous linear retraction is the closed set of its fixed points. -/
theorem isClosed_range_of_factor {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [T2Space Y]
    (F P : X →L[ℂ] Y) (A : Y →L[ℂ] Y) (hsur : Surjective P) (c : ℂ) (hc : c ≠ 0)
    (h : ∀ x, F x = c • A (P x)) (hfix : ∀ x, A (F x) = F x) :
    IsClosed (Set.range F) := by
  have he : Set.range F = {y | A y = y} := by
    apply Set.ext
    intro y
    constructor
    · exact fun ⟨x, hx⟩ ↦ (congrArg A hx).symm.trans ((hfix x).trans hx)
    · intro hy
      refine (hsur (c⁻¹ • y)).elim fun x hx ↦ ⟨x, ?_⟩
      have hA : A (P x) = c⁻¹ • y := (congrArg A hx).trans
        ((A.map_smul c⁻¹ y).trans (congrArg (c⁻¹ • ·) hy))
      exact (h x).trans ((congrArg (c • ·) hA).trans (smul_inv_smul₀ hc y))
  exact Eq.mpr (congrArg IsClosed he) (isClosed_eq A.continuous continuous_id)

/-- Transport an open linear quotient through a continuous linear comparison whose inverse
is sequentially continuous. The resulting quotient has a continuous inverse map. -/
theorem quotient_of_sequential_comparison {R X Y Z : Type*} [Ring R]
    [AddCommGroup X] [Module R X] [TopologicalSpace X]
    [AddCommGroup Y] [Module R Y] [TopologicalSpace Y]
    [AddCommGroup Z] [Module R Z] [TopologicalSpace Z]
    (C : X ≃ₗ[R] Y) (hc : Continuous C) (hs : SeqContinuous C.symm)
    (F : X →L[R] Z) (hF : IsQuotientMap F) :
    ∃ A : Y →ₗ[R] Z, SeqContinuous A ∧ Surjective A ∧ (∀ x, A (C x) = F x) ∧
      ∃ B : Z ≃ₗ[R] (Y ⧸ A.ker), SeqContinuous B ∧ ∀ y, B (A y) = A.ker.mkQ y := by
  let A := F.toLinearMap.comp C.symm.toLinearMap
  have hA : Surjective A := hF.surjective.comp C.symm.surjective
  let B := (A.quotKerEquivOfSurjective hA).symm
  have hb (y : Y) : B (A y) = A.ker.mkQ y := A.quotKerEquivOfSurjective_symm_apply hA y
  have hf (x : X) : A (C x) = F x := congrArg F (C.symm_apply_apply x)
  have he : B ∘ F = A.ker.mkQ ∘ C := funext fun x ↦ (congrArg B (hf x).symm).trans (hb _)
  have hB : Continuous B := hF.continuous_iff.mpr
    (Eq.mpr (congrArg Continuous he) (A.ker.continuous_mkQ.comp hc))
  refine ⟨A, ?_, hA, hf, B, hB.seqContinuous, hb⟩
  intro u y hu
  exact F.continuous.continuousAt.tendsto.comp (hs hu)

end

end RiemannMasullo
