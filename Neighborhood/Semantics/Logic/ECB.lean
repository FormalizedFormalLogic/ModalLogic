module

public import Neighborhood.Semantics.Logic.EB
public import Neighborhood.Semantics.Logic.EC
public import Neighborhood.Semantics.Example.Frame2_95

/-!
# The neighborhood logic `LogicECB`

Soundness and consistency of `LogicECB`, the classical
modal logic axiomatised by the regularity axiom `C` and the symmetry axiom `B` over
`LogicE`, with respect to the regular and symmetric neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSymmetric] :
    A ∈ LogicECB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECB.sound frame_1_2 hC⟩

lemma not_provable_axiomD {a : α} : ∃ A, Axioms.D A ∉ (@LogicECB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicECB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECB α) := by
  intro hcon
  exact frame_2_95.not_valid_axiomN (LogicECB.sound frame_2_95 hcon)

end LogicECB

theorem LogicEC_ssubset_LogicECB : (@LogicEC ℕ) ⊂ LogicECB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEC.not_provable_axiomB (a := (0 : ℕ))
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEB_ssubset_LogicECB : @LogicEB ℕ ⊂ LogicECB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicEB.not_provable_axiomC (a := (0 : ℕ)) (b := 1) (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
