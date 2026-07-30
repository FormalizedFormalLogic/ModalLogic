module

public import Neighborhood.Semantics.Logic.EM
public import Neighborhood.Semantics.Logic.EN
import Neighborhood.Semantics.Example.SimpleBlackhole
import Neighborhood.Semantics.Example.SimpleWhitehole

/-!
# The neighborhood logic `LogicEMN`

Soundness, consistency and completeness of `LogicEMN`, the classical modal logic axiomatised by
the monotonicity axiom `M` together with `N := □⊤`, with respect to the monotonic frames
containing their unit.

Also proves the strict inclusions of `LogicEM` and `LogicEN` in `LogicEMN` (a comparison of two
logics lives in the stronger logic's module).
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMN.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.ContainsUnit] :
    A ∈ LogicEMN → F ⊧ A :=
  Hilbert.sound
    (by rintro _ (⟨_, _, rfl⟩ | rfl)
        exacts [valid_axiomM_of_isMonotonic, valid_axiomN_of_containsUnit])

theorem LogicEMN.consistent : (@LogicEMN α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMN.sound Frame.simple_blackhole hC

instance : Nonempty (MaximalConsistentSet (@LogicEMN α)) :=
  MaximalConsistentSet.nonempty LogicEMN.consistent

variable [DecidableEq α]

theorem LogicEMN.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.ContainsUnit] → F ⊧ A) :
    A ∈ @LogicEMN α :=
  (supplementedBasicCanonicity LogicEMN).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMN).toModel.toFrame
      (supplementedBasicCanonicity LogicEMN).toModel.Val)

theorem LogicEM_ssubset_LogicEMN : @LogicEM ℕ ⊂ LogicEMN := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicEM ℕ := h (ProvableHilbert.axm (Or.inr rfl))
    exact Frame.simple_whitehole.not_valid_axiomN (LogicEM.sound Frame.simple_whitehole hN)

theorem LogicEN_ssubset_LogicEMN : @LogicEN ℕ ⊂ LogicEMN := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hM : Axioms.M (.atom 0) (.atom 1) ∈ (@LogicEN ℕ) :=
      h (ProvableHilbert.axm (Or.inl ⟨_, _, rfl⟩))
    let M : Model (Fin 2) ℕ :=
      ⟨⟨fun w => match w with
        | 0 => {∅, Set.univ}
        | 1 => {Set.univ}⟩,
       fun a => match a with
        | 0 => {0}
        | 1 => {1}
        | _ => Set.univ⟩
    have : M.toFrame.ContainsUnit := ⟨by ext x; match x with | 0 | 1 => simp [M, Frame.box]⟩
    have h0 := LogicEN.sound M.toFrame hM M.Val 0
    simp [M, Forces, Frame.box, Set.ext_iff] at h0

end
