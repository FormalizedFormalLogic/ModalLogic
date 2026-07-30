module

public import Neighborhood.Semantics.Logic.E
import Neighborhood.Semantics.Example.SimpleBlackhole

/-!
# The neighborhood logic `LogicE5`

Soundness, consistency and completeness of `LogicE5`, the classical modal logic axiomatized by
`Five := ◇A 🡒 □◇A` over `LogicE`, with respect to the euclidean frames (`Frame.IsEuclidean`).
Also its strict inclusion in `LogicE`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicE5.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsEuclidean] :
    A ∈ @LogicE5 α → F ⊧ A :=
  Hilbert.sound (fun B hB => by obtain ⟨B, rfl⟩ := hB; exact valid_axiomFive_of_isEuclidean)

theorem LogicE5.consistent : (@LogicE5 α).IsConsistent := by
  by_contra! hC
  simpa using LogicE5.sound Frame.simple_blackhole hC

instance : Nonempty (MaximalConsistentSet (@LogicE5 α)) :=
  MaximalConsistentSet.nonempty LogicE5.consistent

variable [DecidableEq α]

theorem LogicE5.complete (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsEuclidean] → F ⊧ A) :
    A ∈ @LogicE5 α :=
  (maximalRelativeMaximalCanonicity LogicE5).mem_of_valid
    (h (maximalRelativeMaximalCanonicity LogicE5).toModel.toFrame
      (maximalRelativeMaximalCanonicity LogicE5).toModel.Val)


theorem LogicE_ssubset_LogicE5 : @LogicE ℕ ⊂ LogicE5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hFive : Axioms.Five (.atom 0) ∈ @LogicE ℕ := h (ProvableHilbert.axm ⟨_, rfl⟩)
    let F : Frame (Fin 3) := ⟨fun x => {{x}, Set.univ}⟩
    have hE : F.IsEuclidean := isEuclidean_of_valid_axiomFive (LogicE.sound F hFive)
    have hdia : F.dia ({0, 1} : Set (Fin 3)) = {0, 1} := by
      simp only [Set.ext_iff, Frame.dia, Frame.box, F, Set.mem_compl_iff, Set.mem_setOf_eq,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      decide
    have hbox : F.box ({0, 1} : Set (Fin 3)) = ∅ := by
      simp only [Set.ext_iff, Frame.box, F, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff, Set.mem_empty_iff_false]
      decide
    have h2 := hE.eucl {0, 1}
    rw [hdia, hbox] at h2
    exact (Set.nonempty_of_mem (Set.mem_insert 0 {1})).ne_empty (Set.subset_empty_iff.mp h2)

end
