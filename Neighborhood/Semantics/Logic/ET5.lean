module

public import Neighborhood.Semantics.Logic.ENT4
public import Neighborhood.Semantics.Logic.E5
public import Neighborhood.Semantics.Logic.ETB
public import Neighborhood.Semantics.Logic.EB4
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame3_9471106
public import Neighborhood.Semantics.Example.Frame3_8437920

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

end LogicET5

theorem LogicENT4_ssubset_LogicET5 : @LogicENT4 ℕ ⊂ LogicET5 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩)
    · exact Logic.axiomN
    · exact Logic.axiomT
    · exact LogicET5.hasAxiomFour
  · intro h
    have hFive : Axioms.Five #0 ∈ @LogicENT4 ℕ := h Logic.axiomFive
    exact frame_3_9471106.not_isEuclidean
      (isEuclidean_of_valid_axiomFive (LogicENT4.sound frame_3_9471106 hFive))

theorem LogicE5_ssubset_LogicET5 : @LogicE5 ℕ ⊂ LogicET5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hT : Axioms.T #0 ∈ @LogicE5 ℕ := h Logic.axiomT
    exact frame_1_3.not_isReflexive
      (isReflexive_of_valid_axiomT (LogicE5.sound frame_1_3 hT))

theorem LogicETB_ssubset_LogicET5 : @LogicETB ℕ ⊂ LogicET5 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩)
    · exact Logic.axiomT
    · exact Logic.axiomB
  · intro h
    have hFive : Axioms.Five #0 ∈ @LogicETB ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_8437920.not_valid_axiomFive (LogicETB.sound frame_3_8437920 hFive)

theorem LogicEB4_ssubset_LogicET5 : @LogicEB4 ℕ ⊂ LogicET5 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩)
    · exact Logic.axiomB
    · exact Logic.axiomFour
  · intro h
    have hT : Axioms.T #0 ∈ @LogicEB4 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomT (LogicEB4.sound frame_1_3 hT)

end
