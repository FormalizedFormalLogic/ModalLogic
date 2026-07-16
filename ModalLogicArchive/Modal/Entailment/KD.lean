module

public import ModalLogicArchive.Modal.Entailment.END

@[expose] public section

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S}

instance [Entailment.KD 𝓢] : Entailment.END 𝓢 where

end LO.Modal.Entailment
end
