module

public import Neighborhood.Semantics.Logic.EK
public import Neighborhood.Semantics.Logic.EM

/-!
# The neighborhood logic `LogicEMK`

Soundness and consistency of `LogicEMK`, the classical modal logic axiomatised by the
monotonicity axiom `M` together with every instance of the axiom scheme `K`, with respect to all
monotonic neighborhood frames satisfying the `K`-property.

Also proves the strict inclusions of `LogicEK` and `LogicEM` in `LogicEMK`, and — combined with
the coincidence `LogicEMK_eq_LogicEMCK` — the strict inclusion of `LogicEM` in `LogicEMCK`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMK.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.HasPropertyK] :
    A ∈ LogicEMK → F ⊧ A :=
  Hilbert.sound
    (by rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩)
        exacts [valid_axiomM_of_isMonotonic, valid_axiomK_of_hasPropertyK])

theorem LogicEMK.consistent : (@LogicEMK α).IsConsistent :=
  Hilbert.consistent_of (F := Frame.simple_blackhole)
    (by rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩)
        exacts [valid_axiomM_of_isMonotonic, valid_axiomK_of_hasPropertyK])


theorem LogicEK_ssubset_LogicEMK : @LogicEK ℕ ⊂ LogicEMK := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hM : Axioms.M ((.atom 0) ⋎ (.atom 1)) (.atom 1) ∈ @LogicEK ℕ :=
      h (ProvableHilbert.axm (Or.inl ⟨_, _, rfl⟩))
    let M : Model (Fin 4) ℕ :=
      ⟨⟨fun _ => {{0, 1}, {0, 2}}⟩,
       fun a => match a with
        | 0 => {0, 1}
        | 1 => {0, 2}
        | _ => ∅⟩
    -- Both `{0, 1}` and `{0, 2}` avoid the world `3`, so no `X` in the neighborhood filter has
    -- an `Xᶜ ∪ Y` in the filter either: the `K`-property holds vacuously.
    have : M.toFrame.HasPropertyK := ⟨fun X Y w hw => by
      simp only [
        Frame.box, M, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff
      ] at hw;
      obtain ⟨h1, h2⟩ := hw
      have h3 : (3 : Fin 4) ∈ Xᶜ ∪ Y := by
        rcases h2 with h2 | h2 <;> subst h2 <;> exact Set.mem_union_left _ (by decide)
      rcases h1 with h1 | h1 <;> rw [h1] at h3 <;> simp at h3⟩
    have h0 := LogicEK.sound M.toFrame hM M.Val 0
    simp [M, Forces, Frame.box, Set.ext_iff] at h0
    revert h0
    decide

theorem LogicEM_ssubset_LogicEMK : @LogicEM ℕ ⊂ LogicEMK := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hK : Axioms.K (.atom 0) (.atom 1) ∈ @LogicEM ℕ := h (ProvableHilbert.axm (Or.inr ⟨_, _, rfl⟩))
    let M : Model (Fin 2) ℕ := ⟨⟨fun _ => {S | S ≠ ∅}⟩, fun a => match a with | 0 => {0} | _ => ∅⟩
    -- Every nonempty subset of the two worlds is a neighborhood, so the frame is monotonic; but
    -- `{1}` and `{0}` are both neighborhoods while `∅` is not, refuting `K`.
    have : M.toFrame.IsMonotonic := ⟨fun X Y w hw => by
      simp only [Frame.box, M, Set.mem_setOf_eq, ne_eq] at hw ⊢
      constructor
      · rintro rfl; simp at hw
      · rintro rfl; simp at hw⟩
    have h0 := LogicEM.sound M.toFrame hK M.Val 0
    simp [M, Forces, Frame.box, Set.ext_iff] at h0


theorem LogicEM_ssubset_LogicEMCK : @LogicEM ℕ ⊂ LogicEMCK := by
  rw [← LogicEMK_eq_LogicEMCK]
  exact LogicEM_ssubset_LogicEMK

end
