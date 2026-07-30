module

public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.Logic.E

/-!
# The neighborhood logic `LogicEK`

Soundness and consistency of `LogicEK`, obtained from `LogicE` by adding every instance of the
axiom scheme `K`, with respect to all neighborhood frames satisfying the `K`-property, and its
strict inclusion of `LogicE`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEK.sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] :
    A ∈ LogicEK → F ⊧ A :=
  Hilbert.sound (fun B hB => by obtain ⟨A, B, rfl⟩ := hB; exact valid_axiomK_of_hasPropertyK)

theorem LogicEK.consistent : (@LogicEK α).IsConsistent :=
  Hilbert.consistent_of (F := Frame.simple_blackhole)
    (fun B hB => by obtain ⟨A, B, rfl⟩ := hB; exact valid_axiomK_of_hasPropertyK)


theorem LogicE_ssubset_LogicEK : @LogicE ℕ ⊂ LogicEK := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hK : Axioms.K (.atom 0) (.atom 1) ∈ @LogicE ℕ := h (ProvableHilbert.axm ⟨_, _, rfl⟩)
    let M : Model (Fin 3) ℕ :=
      ⟨⟨fun w => match w with
        | 0 => {{0}, {0, 1, 2}}
        | 1 => ∅
        | 2 => ∅⟩,
       fun a => match a with
        | 0 => {0}
        | 1 => {0, 1}
        | _ => Set.univ⟩
    have h0 := LogicE.sound M.toFrame hK M.Val 0
    simp [M, Forces, Frame.box, Set.ext_iff] at h0
    revert h0
    decide

end
