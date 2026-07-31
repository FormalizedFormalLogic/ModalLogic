module

public import Neighborhood.Semantics.Logic.EC
public import Neighborhood.Semantics.Logic.EN
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_206

/-!
# The neighborhood logic `LogicECN`

Soundness, consistency and completeness of `LogicECN`, the classical modal logic axiomatised by
both the regularity axiom `C` and `N := □⊤` over `LogicE`, with respect to the regular
neighborhood frames containing their unit.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicECN.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular]
    [F.ContainsUnit] :
    A ∈ LogicECN → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | rfl) <;> simp)

instance : (@LogicECN α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECN.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem LogicECN.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsRegular] → [F.ContainsUnit] → F ⊧ A) :
    A ∈ @LogicECN α :=
  (basicCanonicalModel LogicECN).mem_of_valid
    (h (basicCanonicalModel LogicECN).toFrame
      (basicCanonicalModel LogicECN).Val)

theorem LogicEC_ssubset_LogicECN : @LogicEC ℕ ⊂ LogicECN := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicEC ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicEC.sound frame_1_0 hN)

theorem LogicEN_ssubset_LogicECN : @LogicEN ℕ ⊂ LogicECN := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicEN ℕ := h (ProvableHilbert.axm (by grind))
    let M : Model (Fin 2) ℕ :=
      ⟨frame_2_206,
       fun a => match a with
        | 0 => {0}
        | 1 => {1}
        | _ => Set.univ⟩
    have h0 := LogicEN.sound M.toFrame hC M.Val 0
    simp [M, Forces, Frame.box, frame_2_206, Set.ext_iff] at h0

end
