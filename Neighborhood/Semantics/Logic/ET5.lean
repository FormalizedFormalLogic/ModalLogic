module

public import Neighborhood.Semantics.Logic.ENT4
public import Neighborhood.Semantics.Logic.E5
public import Neighborhood.Semantics.Logic.ETB
public import Neighborhood.Semantics.Logic.EB4
public import Neighborhood.Semantics.Example.Frame3_9472136

/-!
# The neighborhood logic `LogicET5`

Soundness, consistency and completeness of `LogicET5`, the classical modal logic axiomatised by
the reflexivity axiom `T` and the euclideanness axiom `Five` over `LogicE`, with respect to the
neighborhood frames that are both reflexive and euclidean.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicET5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsReflexive] [F.IsEuclidean] :
    A ∈ LogicET5 → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicET5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicET5.sound frame_1_2 hC⟩

instance : (@LogicET5 α).HasAxiomN :=
  ⟨have hiff : (⊤ : Formula α) 🡘 ◇⊤ ∈ (@LogicET5 α) :=
      Logic.E_intro Logic.diaTc (Logic.C_of_conseq Logic.verum)
   Logic.C_of_E_mpr (Logic.re hiff) ⨀ (Logic.axiomFive ⨀ (Logic.diaTc ⨀ Logic.verum))⟩

section

variable [DecidableEq α]

omit [DecidableEq α] in
theorem hasAxiomFour : Axioms.Four A ∈ (@LogicET5 α) :=
  have h1 : (□A : Formula α) 🡒 ◇□A ∈ (@LogicET5 α) := Logic.diaTc
  have h2 : ◇□A 🡒 (□A : Formula α) ∈ (@LogicET5 α) :=
    (Logic.hasAxiomGeachSwap (L := @LogicET5 α) (g := ⟨1, 1, 0, 1⟩)).Geach A
  have hiff : (□A : Formula α) 🡘 ◇□A ∈ (@LogicET5 α) := Logic.E_intro h1 h2
  Logic.C_trans (Logic.C_trans h1 Logic.axiomFive)
    (Logic.C_of_E_mp (Logic.re (Logic.E_symm hiff)))

instance : (basicCanonicalModel (@LogicET5 α)).IsEuclidean := by
  apply CanonicalModel.isEuclidean'
  intro X hX
  have hbox : (basicCanonicalModel (@LogicET5 α)).box X = ∅ := by
    ext Ω
    simp only [Set.mem_empty_iff_false, iff_false]
    exact fun hΩ => basicCanonicalModel.not_isNonproofset_of_mem_box hΩ hX
  rw [hbox]
  simp [Frame.dia, Frame.contains_unit]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsReflexive] → [F.IsEuclidean] → F ⊧ A) :
    A ∈ @LogicET5 α :=
  (basicCanonicalModel LogicET5).mem_of_valid
    (h (basicCanonicalModel LogicET5).toFrame (basicCanonicalModel LogicET5).Val)

end

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicET5 α) := by
  by_contra! hcon
  exact frame_3_11570344.not_valid_axiomC hab (LogicET5.sound frame_3_11570344 (hcon #a #b))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicET5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicET5.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicET5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicET5.sound frame_3_9472136 (hcon #a #b))

end LogicET5

theorem LogicENT4_ssubset_LogicET5 : @LogicENT4 ℕ ⊂ LogicET5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩)
    · exact Logic.axiomN
    · exact Logic.axiomT
    · exact LogicET5.hasAxiomFour
  · obtain ⟨A, hA⟩ := LogicENT4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, Logic.axiomFive, hA⟩

theorem LogicE5_ssubset_LogicET5 : @LogicE5 ℕ ⊂ LogicET5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, hA⟩ := LogicE5.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, Logic.axiomT, hA⟩

theorem LogicETB_ssubset_LogicET5 : @LogicETB ℕ ⊂ LogicET5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩)
    · exact Logic.axiomT
    · exact Logic.axiomB
  · obtain ⟨A, hA⟩ := LogicETB.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEB4_ssubset_LogicET5 : @LogicEB4 ℕ ⊂ LogicET5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩)
    · exact Logic.axiomB
    · exact Logic.axiomFour
  · obtain ⟨A, hA⟩ := LogicEB4.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

end
