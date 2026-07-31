module

public import Neighborhood.Semantics.Logic.EM
public import Neighborhood.Semantics.Logic.EC
public import Neighborhood.Semantics.Logic.EK
public import Neighborhood.Semantics.Example.Frame2_206

/-!
# The neighborhood logic `LogicEMC`

Soundness, consistency and completeness of `LogicEMC`, the classical modal logic axiomatised by
the monotonicity axiom `M` and the regularity axiom `C`, with respect to the neighborhood frames
that are both monotonic and regular.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMC

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] :
    A ∈ LogicEMC → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> simp)

instance : (@LogicEMC α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMC.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsRegular] → F ⊧ A) :
    A ∈ @LogicEMC α :=
  (supplementedBasicCanonicalModel LogicEMC).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMC).toFrame
      (supplementedBasicCanonicalModel LogicEMC).Val)

omit [DecidableEq α] in
lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMC α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMC.sound frame_1_3 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMC α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour
    (LogicEMC.sound frame_2_8 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMC α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMC.sound frame_1_0 hcon)

end LogicEMC

theorem LogicEC_ssubset_LogicEMC : @LogicEC ℕ ⊂ LogicEMC := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicEC.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end
