module

public import Neighborhood.Semantics.Hilbert
public import Neighborhood.Semantics.Completeness
public import Neighborhood.Semantics.Supplementation
public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomGeach
public import Neighborhood.Hilbert.Logics
public import Neighborhood.Semantics.Logic.EM
public import Neighborhood.Semantics.Logic.ET

/-!
# The neighborhood logic `LogicEMT`

Soundness, consistency and completeness of `LogicEMT`, the classical modal logic axiomatised by
the monotonicity axiom `M` and the reflexivity axiom `T`, with respect to the neighborhood frames
that are both monotonic and reflexive, and its strict inclusion of `LogicEM`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMT.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsReflexive] :
    A ∈ LogicEMT → F ⊧ A :=
  Hilbert.sound (by
    rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩)
    · exact valid_axiomM_of_isMonotonic
    · exact valid_axiomT_of_isReflexive)

theorem LogicEMT.consistent : (@LogicEMT α).IsConsistent :=
  Hilbert.consistent_of (F := Frame.simple_blackhole) (by
    rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩)
    · exact valid_axiomM_of_isMonotonic
    · exact valid_axiomT_of_isReflexive)

instance : Nonempty (MaximalConsistentSet (@LogicEMT α)) :=
  MaximalConsistentSet.nonempty LogicEMT.consistent

variable [DecidableEq α]

theorem LogicEMT.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsReflexive] → F ⊧ A) :
    A ∈ @LogicEMT α :=
  (supplementedBasicCanonicity LogicEMT).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMT).toModel.toFrame
      (supplementedBasicCanonicity LogicEMT).toModel.Val)


theorem LogicEM_ssubset_LogicEMT : @LogicEM ℕ ⊂ LogicEMT := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hT : Axioms.T (.atom 0) ∈ @LogicEM ℕ := h (ProvableHilbert.axm (Or.inr ⟨_, rfl⟩))
    haveI : (⟨fun _ => Set.univ⟩ : Frame (Fin 1)).IsMonotonic := ⟨fun X Y => by simp [Frame.box]⟩
    have hR := isReflexive_of_valid_axiomT
      (LogicEM.sound (⟨fun _ => Set.univ⟩ : Frame (Fin 1)) hT)
    have := hR.refl (∅ : Set (Fin 1)) (show (0 : Fin 1) ∈ _ by simp [Frame.box])
    simp at this

end
