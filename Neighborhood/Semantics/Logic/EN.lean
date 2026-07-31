module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_137
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame2_172
public import Neighborhood.Semantics.Example.Frame2_206

/-!
# The neighborhood logic `LogicEN`

Soundness, consistency and completeness of `LogicEN`, the classical modal logic axiomatized by
`N := □⊤` over `LogicE`, with respect to the frames containing their unit
(`Frame.ContainsUnit`).
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEN

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] :
    A ∈ @LogicEN α → F ⊧ A :=
  Hilbert.sound (by rintro _ rfl; simp)

instance : (@LogicEN α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEN.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.ContainsUnit] → F ⊧ A) :
    A ∈ @LogicEN α :=
  (basicCanonicalModel LogicEN).mem_of_valid
    (h (basicCanonicalModel LogicEN).toFrame
      (basicCanonicalModel LogicEN).Val)

omit [DecidableEq α] in
lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEN α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEN.sound frame_2_170 (hcon #a))

lemma not_provable_axiomC (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEN α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab (LogicEN.sound frame_2_206 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEN α) := by
  by_contra! hcon
  exact frame_2_137.not_valid_axiomFive (LogicEN.sound frame_2_137 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEN α) := by
  by_contra! hcon
  exact frame_2_172.not_valid_axiomFour
    (LogicEN.sound frame_2_172 (hcon #a))

lemma not_provable_axiomM (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEN α) := by
  by_contra! hcon
  exact frame_2_137.not_valid_axiomM hab (LogicEN.sound _ (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEN α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEN.sound frame_1_3 hcon)

end LogicEN

theorem LogicE_ssubset_LogicEN : @LogicE ℕ ⊂ LogicEN := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicE.not_provable_axiomN⟩

end
