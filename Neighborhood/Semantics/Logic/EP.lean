module

public import Neighborhood.Semantics.Logic.E
import Neighborhood.Semantics.Example.Frame1_2
import Neighborhood.Semantics.Example.Frame2_78

/-!
# The neighborhood logic `LogicEP`

Soundness and consistency of `LogicEP`, the classical modal logic axiomatised by the
possibility axiom `P := ∼□⊥`, with respect to the neighborhood frames in which no world has the
empty set as one of its neighborhoods (`Frame.NotContainsEmpty`). Also its strict inclusion in
`LogicE`, and that `D` is not among its theorems.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEP.sound {κ} [Nonempty κ] (F : Frame κ) [F.NotContainsEmpty] :
    A ∈ LogicEP → F ⊧ A :=
  Hilbert.sound
    (fun B hB => by
      simp only [Set.mem_singleton_iff] at hB; subst hB
      exact valid_axiomP_of_notContainsEmpty)

theorem LogicEP.consistent : (@LogicEP α).IsConsistent := by
  by_contra! hC
  simpa using LogicEP.sound frame_1_2 hC


theorem LogicE_ssubset_LogicEP : @LogicE ℕ ⊂ LogicEP := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hP : (Axioms.P : Formula ℕ) ∈ @LogicE ℕ := h (ProvableHilbert.axm rfl)
    have := notContainsEmpty_of_valid_axiomP
      (F := (⟨fun _ => {∅}⟩ : Frame (Fin 1))) (LogicE.sound _ hP)
    simpa using this.not_contains_empty (x := 0)

theorem LogicEP.not_mem_axiomD {a : ℕ} : Axioms.D (.atom a) ∉ @LogicEP ℕ := fun hD =>
  frame_2_78.not_isSerial <| isSerial_of_valid_axiomD <|
    LogicEP.sound frame_2_78 hD

end
