module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Logic.ED
public import Neighborhood.Semantics.Logic.EM
public import Neighborhood.Semantics.Logic.EMP
public import Neighborhood.Semantics.Supplementation
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_238

/-!
# The neighborhood logic `LogicEMD`

Soundness and consistency of `LogicEMD`, the classical modal logic axiomatised by the
monotonicity axiom `M` and the seriality axiom `D`, with respect to the monotonic and
serial neighborhood frames.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicEMD

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSerial] :
    A ∈ LogicEMD → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
theorem consistent : (@LogicEMD α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMD.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMD α)) :=
  MaximalConsistentSet.nonempty LogicEMD.consistent

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsSerial] → F ⊧ A) :
    A ∈ @LogicEMD α :=
  (supplementedBasicCanonicity LogicEMD).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMD).toModel.toFrame
      (supplementedBasicCanonicity LogicEMD).toModel.Val)

end LogicEMD

theorem LogicED_ssubset_LogicEMD : @LogicED ℕ ⊂ LogicEMD := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hM : Axioms.M #0 #1 ∈ (@LogicED ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_1.not_valid_axiomM (LogicED.sound frame_1_1 hM)

theorem LogicEMP_ssubset_LogicEMD : @LogicEMP ℕ ⊂ LogicEMD := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A (⟨B, C, rfl⟩ | rfl) <;> first | exact Logic.axiomM | exact Logic.axiomP_of_MD
  · intro h
    have hD : Axioms.D #0 ∈ @LogicEMP ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_238.not_valid_axiomD (LogicEMP.sound frame_2_238 hD)

end
