module

public import Neighborhood.Semantics.Logic.E
import Neighborhood.Semantics.Example.SimpleBlackhole

/-!
# The neighborhood logic `LogicED`

Soundness and consistency of `LogicED`, the classical modal logic axiomatised by the seriality
axiom `D`, with respect to the serial neighborhood frames (`Frame.IsSerial`), and the strict
inclusion of `LogicE` in `LogicED`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicED.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSerial] :
    A ∈ LogicED → F ⊧ A :=
  Hilbert.sound (fun _ hB => by obtain ⟨_, rfl⟩ := hB; exact valid_axiomD_of_isSerial)

theorem LogicED.consistent : (@LogicED α).IsConsistent := by
  by_contra! hC
  simpa using LogicED.sound Frame.simple_blackhole hC


theorem LogicE_ssubset_LogicED : @LogicE ℕ ⊂ LogicED := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hD : Axioms.D (.atom 0) ∈ @LogicE ℕ := h (ProvableHilbert.axm ⟨_, rfl⟩)
    have hS : (⟨fun w => match w with | 0 => {{0}} | 1 => Set.univ⟩ : Frame (Fin 2)).IsSerial :=
      isSerial_of_valid_axiomD (LogicE.sound _ hD)
    have := hS.serial {1} (show (1 : Fin 2) ∈ _ by simp [Frame.box])
    simp [Frame.dia, Frame.box] at this

end
