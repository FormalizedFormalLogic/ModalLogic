module

public import Neighborhood.Semantics.Logic.EMT4
public import Neighborhood.Semantics.Logic.EMN
public import Neighborhood.Semantics.Logic.ENT4
public import Neighborhood.Semantics.Logic.EMN4
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_9471106

/-!
# The neighborhood logic `LogicEMNT4`

Soundness, consistency and completeness of `LogicEMNT4`, the classical modal logic axiomatised by
the monotonicity axiom `M`, `N := □⊤`, the reflexivity axiom `T` and the transitivity axiom `Four`,
with respect to the neighborhood frames that are monotonic, contain their unit, are reflexive and
are transitive, together with its finite frame property. Also proves the strict inclusions of
`LogicEMT4` and `LogicENT4` in `LogicEMNT4`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMNT4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.ContainsUnit] [F.IsReflexive] [F.IsTransitive] :
    A ∈ LogicEMNT4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicEMNT4.consistent : (@LogicEMNT4 α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMNT4.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMNT4 α)) :=
  MaximalConsistentSet.nonempty LogicEMNT4.consistent

variable [DecidableEq α]

theorem LogicEMNT4.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.ContainsUnit] →
      [F.IsReflexive] → [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMNT4 α :=
  (supplementedBasicCanonicity LogicEMNT4).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMNT4).toModel.toFrame
      (supplementedBasicCanonicity LogicEMNT4).toModel.Val)

theorem LogicEMNT4.finite_complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsFinite] → [F.IsMonotonic] →
      [F.ContainsUnit] → [F.IsReflexive] → [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMNT4 α :=
  LogicEMNT4.complete <| by
    intro κ _ F hMono hUnit hRefl hTrans V x
    let M : Model κ α := ⟨F, V⟩
    let T : FormulaSet α := (A.subformulas : Set (Formula α)) ∪ (□⊤ : Formula α).subformulas
    haveI : Finite (FilterEqvQuotient M T) := FilterEqvQuotient.finite (by simp [T])
    haveI := supplementedTransitiveFiltration.containsUnit (M := M) (T := T) (by simp [T])
    apply (supplementedTransitiveFiltration M T).filtration_satisfies _ (by simp [T]) |>.mp
    haveI : (supplementedTransitiveFiltration M T).toModel.toFrame.IsFinite := ⟨‹_›⟩
    exact h (supplementedTransitiveFiltration M T).toModel.toFrame
      (supplementedTransitiveFiltration M T).toModel.Val ⟦x⟧

theorem LogicEMT4_ssubset_LogicEMNT4 : @LogicEMT4 ℕ ⊂ LogicEMNT4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ (@LogicEMT4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicEMT4.sound frame_1_0 hN)

theorem LogicENT4_ssubset_LogicEMNT4 : @LogicENT4 ℕ ⊂ LogicEMNT4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hM : (Axioms.M #0 #1 : Formula ℕ) ∈ (@LogicENT4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_9471106.not_valid_axiomM (LogicENT4.sound frame_3_9471106 hM)

theorem LogicEMN4_ssubset_LogicEMNT4 : @LogicEMN4 ℕ ⊂ LogicEMNT4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hT : Axioms.T #0 ∈ @LogicEMN4 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_170.not_valid_axiomT (LogicEMN4.sound frame_2_170 hT)

end
