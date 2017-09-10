(** Accepts formulae from the standard input and tests them for satisfiability.
    Each formula has to be on a separate line and empty lines are ignored.
    The input is terminated by EOF.
    @author Florian Widmann
 *)


let _ = 
  let verb = (Array.length Sys.argv) - 1 in
  let prtgrph = if Array.length Sys.argv >= 3 then Some Sys.argv.(2)
	else None
  in
    let printRes sat =
      if verb = 0 then
        print_endline (if sat then "satisfiable\n" else "unsatisfiable\n")
      else ()
    in
    try
      while true do
        let input = read_line () in
        if not (GenAndComp.isEmptyString input) then
          let f = PLTLFormula.importFormula input in
		  printRes (PLTLGraph.isSat ~verbose:verb ~print:prtgrph f)
        else ()
      done
    with End_of_file -> ()
