module

public import Neighborhood.Semantics.Logic.ED
public import Neighborhood.Semantics.Logic.ENP
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame3_8421506
public import Neighborhood.Semantics.Example.Frame3_8431784

/-!
# The neighborhood logic `LogicEND`

Soundness, consistency and completeness of `LogicEND`, the classical modal logic axiomatised by
both `N := □⊤` and the seriality axiom `D` over `LogicE`, with respect to the serial neighborhood
frames containing their unit.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEND

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit]
    [F.IsSerial] :
    A ∈ LogicEND → F ⊧ A :=
  Hilbert.sound (by rintro _ (rfl | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEND α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEND.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.ContainsUnit] → [F.IsSerial] → F ⊧ A) :
    A ∈ @LogicEND α :=
  (basicCanonicalModel LogicEND).mem_of_valid
    (h (basicCanonicalModel LogicEND).toFrame
      (basicCanonicalModel LogicEND).Val)

omit [DecidableEq α] in
lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEND α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB
    (LogicEND.sound frame_2_138 (hcon #a))

lemma not_provable_axiomC (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEND α) := by
  by_contra! hcon
  exact frame_3_8431784.not_valid_axiomC hab (LogicEND.sound frame_3_8431784 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEND α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive
    (LogicEND.sound frame_2_140 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEND α) := by
  by_contra! hcon
  exact frame_2_172.not_valid_axiomFour
    (LogicEND.sound frame_2_172 (hcon #a))

lemma not_provable_axiomM (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEND α) := by
  by_contra! hcon
  exact frame_3_8421506.not_valid_axiomM hab (LogicEND.sound frame_3_8421506 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEND α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEND.sound frame_2_170 (hcon #a))

end LogicEND

theorem LogicED_ssubset_LogicEND : @LogicED ℕ ⊂ LogicEND := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicED.not_provable_axiomN⟩

instance {κ} [Nonempty κ] {F : Frame κ} [F.ContainsUnit] [F.IsSerial] : F.NotContainsEmpty where
  not_contains_empty x hx := by
    have hbox : x ∈ F.box (∅ : Set κ) := hx
    have hd := F.serial (X := (∅ : Set κ)) hbox
    simp [Frame.dia, F.contains_unit] at hd

theorem LogicENP_ssubset_LogicEND : @LogicENP ℕ ⊂ LogicEND := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A (rfl | rfl) <;> first | exact Logic.axiomN | exact Logic.axiomP_of_ND
  · obtain ⟨A, hA⟩ := LogicENP.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end
