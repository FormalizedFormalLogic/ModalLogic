module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Supplementation
public import Neighborhood.Semantics.Logic.EMP
public import Neighborhood.Semantics.Example.Frame2_238

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMD.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSerial] :
    A ∈ LogicEMD → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

theorem LogicEMD.consistent : (@LogicEMD α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMD.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMD α)) :=
  MaximalConsistentSet.nonempty LogicEMD.consistent

variable [DecidableEq α]

theorem LogicEMD.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsSerial] → F ⊧ A) :
    A ∈ @LogicEMD α :=
  (supplementedBasicCanonicity LogicEMD).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMD).toModel.toFrame
      (supplementedBasicCanonicity LogicEMD).toModel.Val)

theorem LogicEMP_ssubset_LogicEMD : @LogicEMP ℕ ⊂ LogicEMD := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A (⟨B, C, rfl⟩ | rfl) <;> first | exact Logic.axiomM | exact Logic.axiomP_of_MD
  · intro h
    have hD : Axioms.D #0 ∈ @LogicEMP ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_238.not_valid_axiomD (LogicEMP.sound frame_2_238 hD)

end
