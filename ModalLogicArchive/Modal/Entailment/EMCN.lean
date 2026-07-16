module

public import ModalLogicArchive.Modal.Entailment.EMC
public import ModalLogicArchive.Modal.Entailment.EN
public import ModalLogicArchive.Modal.Entailment.K

@[expose] public section

namespace LO.Modal.Entailment

open LO.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S}

instance [Entailment.EMCN 𝓢] : Entailment.K 𝓢 where
instance [Entailment.K 𝓢] : Entailment.EMCN 𝓢 where
  re h := by
    apply K_intro;
    . exact axiomK' $ nec $ K_left h;
    . exact axiomK' $ nec $ K_right h;

end LO.Modal.Entailment
end
