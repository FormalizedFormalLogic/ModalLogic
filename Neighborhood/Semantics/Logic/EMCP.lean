module

public import Neighborhood.Semantics.Logic.ECP
public import Neighborhood.Semantics.Logic.EMP
public import Neighborhood.Semantics.Logic.EMC
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_8
public import Neighborhood.Semantics.Example.Frame2_140

/-!
# The neighborhood logic `LogicEMCP`

Soundness and consistency of `LogicEMCP`, the classical modal logic axiomatised by
the monotonicity axiom `M`, the regularity axiom `C`, and the possibility axiom `P := ∼□⊥`,
with respect to the neighborhood frames that are monotonic, regular, and do not contain the
empty set as one of their neighborhoods.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCP

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.NotContainsEmpty] :
    A ∈ LogicEMCP → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) <;> simp)

instance : (@LogicEMCP α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCP.sound frame_1_2 hC⟩

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMCP α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMCP.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMCP α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicEMCP.sound frame_2_140 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMCP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMCP.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMCP α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicEMCP.sound frame_2_8 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMCP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMCP.sound frame_1_0 (hcon #a))

end LogicEMCP

end
