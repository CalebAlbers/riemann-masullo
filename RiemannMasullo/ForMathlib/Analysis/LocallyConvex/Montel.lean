module

public import Mathlib.Analysis.LocallyConvex.Montel

public section

open Bornology Filter Function Set Topology

namespace RiemannMasullo

/-- The inverse of a continuous linear bijection from a Montel space is sequentially
continuous when it takes bounded sets to bounded sets. On the compact closure of each
lifted sequence, the comparison is a topological embedding. -/
theorem seqContinuous_symm_of_bounded_comparison {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul 𝕜 X] [T2Space X] [MontelSpace 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [ContinuousSMul 𝕜 Y] [T2Space Y]
    (C : X ≃ₗ[𝕜] Y) (hc : Continuous C)
    (hb : ∀ B : Set X, IsVonNBounded 𝕜 (C '' B) → IsVonNBounded 𝕜 B) :
    SeqContinuous C.symm := by
  intro u y hu
  let B := closure (insert (C.symm y) (range (fun n ↦ C.symm (u n))))
  have hIm : C '' (insert (C.symm y) (range (fun n ↦ C.symm (u n)))) = insert y (range u) := by
    rw [image_insert_eq, ← range_comp]
    simp [Function.comp_def]
  have hB : IsVonNBounded 𝕜 B := (hb _ (hIm ▸ (hu.isVonNBounded_range 𝕜).insert y)).closure
  let : CompactSpace B := isCompact_iff_compactSpace.mp
    (MontelSpace.isCompact_of_isClosed_of_isVonNBounded 𝕜 isClosed_closure hB)
  let F (z : B) := C z.val
  have he := (hc.comp (continuous_subtype_val (p := (· ∈ B)))).isClosedEmbedding
    (C.injective.comp Subtype.val_injective)
  let v (n : ℕ) : B := ⟨C.symm (u n), subset_closure (mem_insert_of_mem _ (mem_range_self n))⟩
  let z : B := ⟨C.symm y, subset_closure (mem_insert _ _)⟩
  have hF : F ∘ v = u := funext fun n ↦ C.apply_symm_apply (u n)
  have ht : Tendsto v atTop (𝓝 z) := he.isInducing.tendsto_nhds_iff.mpr
    (Eq.mpr (congrArg₂ (fun a b ↦ Tendsto a atTop (𝓝 b)) hF (C.apply_symm_apply y)) hu)
  exact continuous_subtype_val.continuousAt.tendsto.comp ht

end RiemannMasullo
