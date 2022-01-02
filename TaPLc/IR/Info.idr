module TaPLc.IR.Info

public export
data Info : Type where
  EmptyInfo : Info
  IdInfo    : Nat -> Info

export
Show Info where
  showPrec _ EmptyInfo  = "EmptyInfo"
  showPrec d (IdInfo i) = showCon d "IdInfo" $ showArg i
