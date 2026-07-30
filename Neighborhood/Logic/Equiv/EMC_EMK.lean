module

public import Neighborhood.Logic.Equiv.EMC_EMCK
public import Neighborhood.Logic.Equiv.EMK_EMCK

/-! # `EMC`, `EMK`, and `EMCK` are all the same logic -/

@[expose] public section

variable {α : Type u}

/-- `EMC`, `EMK`, and `EMCK` are all the same logic. -/
theorem LogicEMC_eq_LogicEMK : (@LogicEMC α) = LogicEMK :=
  LogicEMC_eq_LogicEMCK.trans LogicEMK_eq_LogicEMCK.symm

end
