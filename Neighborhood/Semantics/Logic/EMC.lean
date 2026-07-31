module

public import Neighborhood.Semantics.Logic.EM
public import Neighborhood.Semantics.Logic.EC
public import Neighborhood.Semantics.Logic.EK
public import Neighborhood.Semantics.Example.Frame4_11259170869739560
public import Neighborhood.Semantics.Example.Frame2_206
public import Neighborhood.Semantics.Example.Frame3_137520
public import Neighborhood.Semantics.Example.Frame1_2

/-!
# The neighborhood logic `LogicEMC`

Soundness, consistency and completeness of `LogicEMC`, the classical modal logic axiomatised by
the monotonicity axiom `M` and the regularity axiom `C`, with respect to the neighborhood frames
that are both monotonic and regular.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEMC.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] :
    A ∈ LogicEMC → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> simp)

theorem LogicEMC.consistent : (@LogicEMC α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMC.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMC α)) :=
  MaximalConsistentSet.nonempty LogicEMC.consistent

variable [DecidableEq α]

theorem LogicEMC.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsRegular] → F ⊧ A) :
    A ∈ @LogicEMC α :=
  (supplementedBasicCanonicity LogicEMC).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMC).toModel.toFrame
      (supplementedBasicCanonicity LogicEMC).toModel.Val)

theorem LogicEC_ssubset_LogicEMC : @LogicEC ℕ ⊂ LogicEMC := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hM : Axioms.M #0 #1 ∈ @LogicEC ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_137520.not_valid_axiomM (LogicEC.sound frame_3_137520 hM)

end
