module

public import Neighborhood.Semantics.Hilbert
public import Neighborhood.Semantics.Completeness
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Hilbert.Logics
public import Neighborhood.Semantics.Logic.E

/-!
# The neighborhood logic `LogicEC`

Soundness, consistency and completeness of `LogicEC`, the classical modal logic axiomatised by
the regularity axiom `C`, with respect to the regular neighborhood frames, and its strict
inclusion in `LogicE`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEC.sound (h : A ∈ LogicEC) {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] : F ⊧ A :=
  Hilbert.sound (fun _ hB => by
    obtain ⟨_, _, rfl⟩ := hB; exact valid_axiomC_of_isRegular) h

instance : (@LogicEC α).Consistent :=
  Hilbert.consistent_of (F := Frame.simple_blackhole) (fun _ hB => by
    obtain ⟨_, _, rfl⟩ := hB; exact valid_axiomC_of_isRegular)

variable [DecidableEq α]

theorem LogicEC.complete (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), F.IsRegular → F ⊧ A) :
    A ∈ @LogicEC α :=
  (basicCanonicity LogicEC).mem_of_valid
    (h (basicCanonicity LogicEC).toModel.toFrame inferInstance
      (basicCanonicity LogicEC).toModel.Val)


theorem LogicE_ssubset_LogicEC : (@LogicE ℕ) ⊂ LogicEC := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hC : Axioms.C (.atom 0) (.atom 1) ∈ (@LogicE ℕ) := h (ProvableHilbert.axm ⟨_, _, rfl⟩)
    let M : Model (Fin 2) ℕ :=
      ⟨⟨fun w => match w with
        | 0 => {{0}, {1}}
        | 1 => {∅}⟩,
       fun a => match a with
        | 0 => {0}
        | 1 => {1}
        | _ => Set.univ⟩
    have h0 := LogicE.sound hC M.toFrame M.Val 0
    simp [M, Forces, Frame.box, Set.ext_iff] at h0

end
