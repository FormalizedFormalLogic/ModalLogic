module

public import Neighborhood.Semantics.Hilbert
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomGeach
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Hilbert.Logics
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_8


@[expose] public section

variable {α : Type u} {A : Formula α}


namespace LogicE

theorem sound {κ} [Nonempty κ] (F : Frame κ) : A ∈ LogicE → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨⟩)

instance : (@LogicE α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicE.sound frame_1_2 hC⟩

theorem complete [DecidableEq α] (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), F ⊧ A) : A ∈ @LogicE α :=
  (basicCanonicalModel LogicE).mem_of_valid
  (h (basicCanonicalModel LogicE).toFrame (basicCanonicalModel LogicE).Val)


lemma not_provable_axiomFour {a : α} : ∃ A, Axioms.Four A ∉ (@LogicE α) := by
  by_contra! hC;
  exact frame_2_8.not_valid_axiomFour (LogicE.sound (frame_2_8) $ hC #a)

end LogicE


end
