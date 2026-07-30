module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Logic.EMN
public import Neighborhood.Semantics.Logic.EMD
public import Neighborhood.Semantics.Logic.EMNP
public import Neighborhood.Semantics.Supplementation
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_238

/-!
# The neighborhood logic `LogicEMND`

Soundness and consistency of `LogicEMND`, the classical modal logic axiomatised by
the monotonicity axiom `M`, `N := □⊤`, and the seriality axiom `D` over `LogicE`,
with respect to the monotonic frames containing their unit and being serial.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMND.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.ContainsUnit] [F.IsSerial] :
    A ∈ LogicEMND → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

theorem LogicEMND.consistent : (@LogicEMND α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMND.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMND α)) :=
  MaximalConsistentSet.nonempty LogicEMND.consistent

theorem LogicEMN_ssubset_LogicEMND : @LogicEMN ℕ ⊂ LogicEMND := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hD : Axioms.D #0 ∈ @LogicEMN ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicEMN.sound frame_1_3 hD)

theorem LogicEMD_ssubset_LogicEMND : @LogicEMD ℕ ⊂ LogicEMND := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicEMD ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicEMD.sound frame_1_0 hN)

theorem LogicEMNP_ssubset_LogicEMND : @LogicEMNP ℕ ⊂ LogicEMND := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | rfl) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomP_of_ND
  · intro h
    have hD : Axioms.D #0 ∈ @LogicEMNP ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_238.not_valid_axiomD (LogicEMNP.sound frame_2_238 hD)

section

variable [DecidableEq α]

theorem LogicEMND.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.ContainsUnit] →
      [F.IsSerial] → F ⊧ A) :
    A ∈ @LogicEMND α :=
  (supplementedBasicCanonicity LogicEMND).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMND).toModel.toFrame
      (supplementedBasicCanonicity LogicEMND).toModel.Val)

end

end
