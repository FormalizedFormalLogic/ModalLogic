module

public import ModalLogicArchive.Modal.Entailment.EM

@[expose] public section

namespace LO.Modal.Entailment

open LO.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S}

instance [Entailment.EN 𝓢] : Entailment.Necessitation 𝓢 where
  nec h := K_left (re (E_intro (C_of_conseq h) (C_of_conseq verum))) ⨀ axiomN

instance [Entailment.Minimal 𝓢] [Entailment.Necessitation 𝓢] : Entailment.HasAxiomN 𝓢 where
  N := nec verum

end LO.Modal.Entailment
end
