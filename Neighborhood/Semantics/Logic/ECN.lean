module

public import Neighborhood.Semantics.Logic.EC
public import Neighborhood.Semantics.Logic.EN

/-!
# The neighborhood logic `LogicECN`

Soundness, consistency and completeness of `LogicECN`, the classical modal logic axiomatised by
both the regularity axiom `C` and `N := □⊤` over `LogicE`, with respect to the regular
neighborhood frames containing their unit. Also its strict inclusions in `LogicEC` and `LogicEN`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicECN.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular]
    [F.ContainsUnit] :
    A ∈ LogicECN → F ⊧ A :=
  Hilbert.sound
    (fun _ hB => by
      rcases hB with ⟨_, _, rfl⟩ | rfl
      · exact valid_axiomC_of_isRegular
      · exact valid_axiomN_of_containsUnit)

theorem LogicECN.consistent : (@LogicECN α).IsConsistent := by
  by_contra! hC
  simpa using LogicECN.sound Frame.simple_blackhole hC

instance : Nonempty (MaximalConsistentSet (@LogicECN α)) :=
  MaximalConsistentSet.nonempty LogicECN.consistent

variable [DecidableEq α]

theorem LogicECN.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsRegular] → [F.ContainsUnit] → F ⊧ A) :
    A ∈ @LogicECN α :=
  (basicCanonicity LogicECN).mem_of_valid
    (h (basicCanonicity LogicECN).toModel.toFrame
      (basicCanonicity LogicECN).toModel.Val)


instance : Frame.simple_whitehole.IsRegular := ⟨by simp [Frame.box, Frame.simple_whitehole]⟩

theorem LogicEC_ssubset_LogicECN : @LogicEC ℕ ⊂ LogicECN := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicEC ℕ := h (ProvableHilbert.axm (Or.inr rfl))
    exact Frame.simple_whitehole.not_valid_axiomN (LogicEC.sound Frame.simple_whitehole hN)

abbrev Frame.trivial_nonregular : Frame (Fin 2) :=
  ⟨fun w => match w with | 0 => {{0}, {1}, Set.univ} | 1 => {{1}, Set.univ}⟩

instance : Frame.trivial_nonregular.ContainsUnit := ⟨by
  ext x; match x with | 0 | 1 => simp [Frame.box, Frame.trivial_nonregular]⟩

theorem LogicEN_ssubset_LogicECN : @LogicEN ℕ ⊂ LogicECN := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hC : Axioms.C (.atom 0) (.atom 1) ∈ @LogicEN ℕ := h (ProvableHilbert.axm (Or.inl ⟨_, _, rfl⟩))
    let M : Model (Fin 2) ℕ :=
      ⟨Frame.trivial_nonregular,
       fun a => match a with
        | 0 => {0}
        | 1 => {1}
        | _ => Set.univ⟩
    have h0 := LogicEN.sound M.toFrame hC M.Val 0
    simp [M, Forces, Frame.box, Frame.trivial_nonregular, Set.ext_iff] at h0

end
