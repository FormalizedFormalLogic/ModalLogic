module

public import Fin74.Kripke.Basic

@[expose]
public section

namespace Model

variable {κ α : Type*} {M : Model κ α} {P : ℕ → M.World → Prop} {u : ℕ → M.World}

/-- Dependent recursion producing, at each stage `m`, a witness world satisfying `P m`
together with its proof, by repeatedly invoking `step` and choosing the resulting successor. -/
private noncomputable def chainAux (w₀ : M.World) (h0 : P 0 w₀)
    (step : ∀ (m : ℕ) w, P m w → ∃ v, w ≺ v ∧ ¬(v ≺ w) ∧ P (m + 1) v) :
    (m : ℕ) → {x : M.World // P m x}
  | 0 => ⟨w₀, h0⟩
  | m + 1 =>
    have prev := chainAux w₀ h0 step m;
    ⟨(step m prev.1 prev.2).choose, (step m prev.1 prev.2).choose_spec.2.2⟩

/-- From a step function producing strict successors, build an infinite strict ascending
chain. Generic in `P`: also used for the three-phase cyclic chain in [Fin74] Lemma 2. -/
theorem exists_strictChain {w₀ : M.World} (h0 : P 0 w₀)
    (step : ∀ (m : ℕ) w, P m w → ∃ v, w ≺ v ∧ ¬(v ≺ w) ∧ P (m + 1) v) :
    ∃ u : ℕ → M.World, u 0 = w₀ ∧ ∀ m : ℕ, (u m ≺ u (m + 1)) ∧ ¬(u (m + 1) ≺ u m) ∧ P m (u m) := by
  use fun m => (chainAux w₀ h0 step m).1;
  refine ⟨rfl, fun m => ?_⟩;
  have hm := (chainAux w₀ h0 step m).2;
  have hspec := (step m (chainAux w₀ h0 step m).1 hm).choose_spec;
  exact ⟨hspec.1, hspec.2.1, hm⟩

/-- An ascending chain relates along `<`. -/
theorem strictChain_rel_of_lt (hR : ∀ m : ℕ, u m ≺ u (m + 1)) {i j : ℕ} (hij : i < j) : u i ≺ u j := by
  induction j, hij using Nat.le_induction with
  | base => exact hR i;
  | succ j _ ih =>
    trans u j;
    . exact ih;
    . exact hR j;

/-- An ascending chain relates along `≤`. -/
theorem strictChain_rel_of_le (hR : ∀ m : ℕ, u m ≺ u (m + 1)) {i j : ℕ} (hij : i ≤ j) : u i ≺ u j := by
  rcases Nat.lt_or_eq_of_le hij with hij | rfl
  · exact strictChain_rel_of_lt hR hij;
  · simp;

/-- A strict ascending chain has pairwise-distinct points (transitivity + reflexivity only;
antisymmetry is not assumed, since Lemma 1's frames need not be posets). -/
theorem strictChain_injective (hR : ∀ m : ℕ, u m ≺ u (m + 1)) (hs : ∀ m : ℕ, ¬(u (m + 1) ≺ u m)) :
    Function.Injective u := by
  have key : ∀ i j : ℕ, i < j → u i ≠ u j := by
    intro i j hij heq;
    have h1 : u (i + 1) ≺ u j := strictChain_rel_of_le hR hij;
    rw [← heq] at h1;
    exact hs i h1;
  intro a b hab;
  rcases lt_trichotomy a b with h | h | h;
  · exact absurd hab (key a b h);
  · exact h;
  · exact absurd hab.symm (key b a h);

end Model

end
