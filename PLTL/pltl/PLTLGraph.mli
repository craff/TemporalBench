type formula = PLTLFormula.formula

val isSat : ?verbose:int -> ?print:string option -> formula -> bool
