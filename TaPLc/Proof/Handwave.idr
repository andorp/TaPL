module TaPLc.Proof.Handwave

||| Handwavy proof of two things being equal. 
|||
||| Sometimes we want to postpone a complicated proof, or the proof is straightworward,
||| or we hit an Idris issue. This proof techinque gives us help in the situations when
||| we want to believe that two values reduce to the same normal form after some steps
||| and we are convinced that this is the truth, so we can just simply tell to the
||| Idris compiler about this beleif.
|||
||| Rather than using the underlying implementation, the belive_me function, we need
||| to state the two things meant to be the same. This approach improves the
||| readability of the proofs and shows us the parts we need to get better at.
|||
||| For example: handwaving (a + (b + c)) ((a + b) + c)
|||
||| Disclaimer, this should have 0 quantity as the created Refl value should not be
||| used at runtime.
export -- TODO: Make this 0 quantity. If it is not 0 than it is magic, as we craete things from nothing waving our hands.
handwaving : {t : Type} -> (a : t) -> (b : t) -> (a = b)
handwaving a b = believe_me (the (a=a) Refl)
