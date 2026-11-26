import ProvedConjectures

-- Prints the axioms each main theorem depends on. Expected: only
-- [propext, Classical.choice, Quot.sound], i.e. no `sorry` and no extra axioms.
#print axioms ProvedConjectures.Carmichael.A182132
#print axioms ProvedConjectures.Carmichael.A182088
#print axioms ProvedConjectures.Carmichael.A182207
#print axioms ProvedConjectures.Carmichael.IsCarmichael.isKorselt
