module

public import Neighborhood.Semantics.Hilbert
public import Neighborhood.Semantics.Completeness
public import Neighborhood.Semantics.AxiomGeach
public import Neighborhood.Hilbert.Logics
public import Neighborhood.Semantics.Logic.E

/-!
# The neighborhood logic `LogicED`

Soundness and consistency of `LogicED`, the classical modal logic axiomatised by the seriality
axiom `D`, with respect to the serial neighborhood frames (`Frame.IsSerial`), and the strict
inclusion of `LogicE` in `LogicED`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicED.sound (h : A ∈ LogicED) {κ} [Nonempty κ] (F : Frame κ) [F.IsSerial] : F ⊧ A :=
  Hilbert.sound (fun _ hB => by obtain ⟨_, rfl⟩ := hB; exact valid_axiomD_of_isSerial) h

instance : Frame.simple_blackhole.IsSerial where
  serial X x hx := by
    simp only [Frame.box, Set.mem_singleton_iff, Set.mem_setOf_eq] at hx
    subst hx
    simp [Frame.dia, Frame.box, Set.ext_iff]

instance : (@LogicED α).Consistent :=
  Hilbert.consistent_of (F := Frame.simple_blackhole)
    (fun _ hB => by obtain ⟨_, rfl⟩ := hB; exact valid_axiomD_of_isSerial)


theorem LogicE_ssubset_LogicED : @LogicE ℕ ⊂ LogicED := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hD : Axioms.D (.atom 0) ∈ @LogicE ℕ := h (ProvableHilbert.axm ⟨_, rfl⟩)
    have hS : (⟨fun w => match w with | 0 => {{0}} | 1 => Set.univ⟩ : Frame (Fin 2)).IsSerial :=
      isSerial_of_valid_axiomD (LogicE.sound hD _)
    have := hS.serial {1} (show (1 : Fin 2) ∈ _ by simp [Frame.box])
    simp [Frame.dia, Frame.box] at this

end
