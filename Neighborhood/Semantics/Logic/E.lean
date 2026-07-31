module

public import Neighborhood.Semantics.Hilbert
public import Neighborhood.Hilbert.Logics
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_8
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame2_22
public import Neighborhood.Semantics.Example.Frame2_79
public import Neighborhood.Semantics.Example.Frame3_130
public import Neighborhood.Semantics.Example.Frame3_137264
public import Neighborhood.Semantics.Example.Frame3_9471106


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

lemma not_provable_axiomB {a : α} : ∃ A, Axioms.B A ∉ (@LogicE α) := by
  by_contra! hcon
  have hS : frame_1_0.IsSymmetric := isSymmetric_of_valid_axiomB (LogicE.sound _ (hcon #a))
  have := hS.symm {0} (show (0 : Fin 1) ∈ _ by simp)
  simp [Frame.box] at this

lemma not_provable_axiomC [DecidableEq α] {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicE α) := by
  by_contra! hcon
  exact frame_2_22.not_valid_axiomC hab (LogicE.sound _ (hcon #a #b))

lemma not_provable_axiomD {a : α} : ∃ A, Axioms.D A ∉ (@LogicE α) := by
  by_contra! hcon
  exact frame_2_79.not_isSerial (isSerial_of_valid_axiomD (LogicE.sound _ (hcon #a)))

lemma not_provable_axiomFive {a : α} : ∃ A, Axioms.Five A ∉ (@LogicE α) := by
  by_contra! hcon
  exact frame_3_9471106.not_isEuclidean (isEuclidean_of_valid_axiomFive (LogicE.sound _ (hcon #a)))

lemma not_provable_axiomK [DecidableEq α] {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicE α) := by
  by_contra! hcon
  exact frame_3_130.not_valid_axiomK hab (LogicE.sound _ (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicE α) := by
  by_contra! hcon
  exact frame_3_137264.not_valid_axiomM hab (LogicE.sound _ (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicE α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicE.sound frame_1_0 hcon)

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicE α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomP (LogicE.sound _ hcon)

end LogicE


end
