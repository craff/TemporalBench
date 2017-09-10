(** Common functions and data structures which are shared
    by the programs which generate (e.g. random) formulae
    and/or run tests or benchmarks on them.
    @author Florian Widmann
 *)


(** Tests whether a string is "almost" empty.
    @param s A string.
    @return True iff the string is empty
    or contains only whitespaces.
 *)
let isEmptyString s =
  let rec empty i =
    if i < 0 then true
    else
      let c = String.get s i in
      if c = ' ' || c = '\009' then empty (pred i)
      else false
  in
  empty (pred (String.length s))


(** This exception is raised when the Unix signal "sigalrm" is received.
    It should not be used for anything else.
 *)
exception Timeout

(** Evaluates a function on an argument
    but aborts the evaluation if it takes longer than a given timeout.
    If the timeout is less then infinity,
    it is required that the Unix signal "sigalrm" is handled and
    that the handler raises the exception Timeout.
    This can for example be achieved via the following code:
      let alarmHandler (n : int) = raise Timeout in
      let oldHandler = Sys.signal Sys.sigalrm (Sys.Signal_handle alarmHandler) in
      ... // do something, e.g. invoke evaluate
      Sys.set_signal Sys.sigalrm oldHandler;
    @param f A function accepting v as an argument.
    The function must not raise the exception Timeout.
    All other exceptions are propagated through this function.
    @param v The argument for f.
    @param timeout The maximal time in seconds
    that the evaluation of f v is allowed to take.
    A non-positive number is interpreted as infinity.
    @return (Some (f v, t), 0) if the evaluation of f v takes t <= timeout seconds;
    (None, 0) otherwise. The superflous 0 is a bogus value for the memory usage
    which is not measured by this function.
    PROBLEM: If f is a "busy" function, it may happen
    that the alarm handler is executed after this function,
    even when the evaluation of f v takes far longer than timeout seconds.
    In this case this function takes longer than timeout and
    the exception Timeout will be raised outside the scope of this function.
 *)
let evaluateFkt f v timeout = 
  let noto = timeout <= 0 in
  try begin
    try
      if noto then () else ignore (Unix.alarm timeout);
      let start = Unix.gettimeofday () in
      let res = f v in
      let stop = Unix.gettimeofday () in
      if noto then () else ignore (Unix.alarm 0);
      let time = stop -. start in
      (Some (res, time), 0)
    with e ->
      if noto then () else ignore (Unix.alarm 0);
      raise e
  end
  with Timeout -> assert (not noto); (None, 0)

(** Evaluates a function with a boolean result on an argument in a child process
    but aborts the evaluation if it takes longer than a given timeout.
    If the timeout is less then infinity,
    it is required that the Unix signal "sigalrm" is handled and
    that the handler raises the exception Timeout (see function "evaluateFkt").
    @param f A function accepting v as an argument and returning a boolean value.
    If f v raises an exception, this function raises the exception Failure.
    That is, the original exception is lost.
    @param v The argument for f.
    @param timeout The maximal time in seconds
    that the evaluation of f v is allowed to take.
    A non-positive number is interpreted as infinity.
    @return Some (f v, t) if the evaluation of f v takes t <= timeout seconds;
    None otherwise.
    @raise Failure if something goes wrong while invoking the child process
    (e.g. it throws an exception) and this function notices it.
    COMMENT: Since the exit codes 0 and 1 are used to return the result,
    the child process must not fail with exit code 1 for other reasons.
    A more secure way to transmit the result would be to use a pipe.
 *)
let evaluateFktProc f v timeout = 
  let noto = timeout <= 0 in
  match Unix.fork () with
  | 0 ->
      let res = f v in
      if res then exit 0 else exit 1
  | id ->
      try
        if noto then () else ignore (Unix.alarm timeout);
        let start = Unix.gettimeofday () in
        let status = snd (Unix.waitpid [] id) in
        let stop = Unix.gettimeofday () in
        if noto then () else ignore (Unix.alarm 0);
        let time = stop -. start in
        let res =
          match status with
          | Unix.WEXITED n when n = 0 || n = 1 -> n = 0
          | _ -> failwith "function \"evaluateProc\" failed"
        in
        Some (res, time)
      with Timeout ->
        assert (not noto);
        let () =
          try
            Unix.kill id Sys.sigkill;
            ignore (Unix.waitpid [] id)
          with Unix.Unix_error _ -> ()
        in
        None


(** Generates a list of atomic "formulae"
    that are assigned a priority.
    @param litlst A list of "literals" (e.g. True and False).
    They are assigned the priority 1.
    @param neg A function that negates a formula.
    @param prio The priority of the generated atomic "formulae".
    @param const A function that converts a string into an atomic "formula".
    @param name A prefix of the names of the generated atomic "formulae".
    @param nr The number of different atomic "formula".
    It is taken at least to be 1 (0 if litlst is non-empty).
    @return A list of pairs (f, p) where f is a formula and p a priority.
*)
let genLiterals ?litlst ?neg ?(prio = 1) const name nr =
  let rec genLit acc = function
    | 0 -> acc
    | n -> 
        let n = pred n in
        let s = name ^ (string_of_int n) in
        let af = const s in
        let acc1 = (af, prio)::acc in
        let acc2 =
          match neg with
          | None -> acc1
          | Some f -> (f af, prio)::acc1
        in
        genLit acc2 n
  in
  let acc = 
    match litlst with
    | None -> []
    | Some l -> List.map (fun f -> (f, 1)) l
  in
  let nr = if acc = [] then max 1 nr else max 0 nr in
  genLit acc nr


(** Sums up the priorities in a list.
    @param lst A list of pairs (f, n) where n is a priority.
    @return The sum of all priorities in lst.
 *)
let addPrios lst = List.fold_left (fun s (_, n) -> s + n) 0 lst

(** Chooses the element in a list that corresponds to a value
    @param n An int value.
    @param lst A list of pairs (f, n) where n is a priority.
    @return The first element e in a list 
    such that the sum of all priorities of elements up to e
    is greater than n.
    @raise Failure if there is no such element.
 *)
let getConst n lst =
  let rec getC sum = function
    | [] -> raise (Failure "Should not happen. It's a bug.")
    | (f, p)::t ->
        let sum1 = sum + p in
        if n < sum1 then f
        else getC sum1 t
  in
  getC 0 lst

(** Chooses k distinct elements from a list.
    @param k The number of elements to be chosen.
    @param ls A list.
    @return A sublist of ls of length k.
 *)
let rec chooseK k ls =
  let len = List.length ls in
  assert (k >= 0 && k <= len);
  if k = len then ls
  else
    let rand = Random.int len in
    let fld (acc, i) e =
      if i = rand then (acc, succ i) else (e::acc, succ i)
    in
    let (nls, _) = List.fold_left fld ([], 0) ls in
    chooseK k nls

(** Creates a formula (program) generator, i.e. a function which takes a size
    and produces a randomly generated formula (program) of that size.
    In the following, f stands for formula, p stands for program,
    and n stand for a priority which must be positive.
    @param lF A list of pairs (f, n), e.g. (p, 1).
    The list must not be empty.
    @param lFF A list of pairs (f->f, n), e.g. (~., 1).
    The list must not be empty.
    @param lFFF A list of pairs (f->f->f, n), e.g. (.&., 1).
    @param lPFF A list of pairs (p->f->f, n), e.g. (<.>., 1).
    @param lP A list of pairs (p, n), e.g. (a, 1).
    The list must not be empty unless lPFF is also empty.
    @param lPP A list of pairs (p->p, n), e.g. ( *., 1).
    @param lFP A list of pairs (f->p, n), e.g. (?., 1).
    @param lPPP A list of pairs (p->p->p, n), e.g. (.+., 1).
    @return A pair (fktF, fktP) where
    fktF is a function that randomly generates a formula of a given size, and
    fktP is a function that randomly generates a program of a given size.
    Both functions use the constructors lF, ..., lPPP.
    The size of the formula/program is the number of constructors.
    Note that each formula (program) in lF (lP) counts as one symbol,
    even when it is a complex formula (program).
    If lP is empty then fktP must not be invoked.
    If lP is not empty, but lPP and lFP are both empty,
    then fktP can only be invoked with size one.
 *)
let mk_generator lF lFF lFFF lPFF lP lPP lFP lPPP =
  let simpleP = lPP = [] && lFP = [] in
  let rec genRF = function
    | n when n <= 0 -> raise (Failure "size of formula must be positive")
    | 1 -> 
        let prios = addPrios lF in
        let rand = Random.int prios in
        getConst rand lF
    | n ->
        let prios1 = addPrios lFF in
        let prios2 = if n = 2 then 0 else addPrios lFFF in
        let prios3 = if n = 2 then 0 else addPrios lPFF in
        let rand = Random.int (prios1 + prios2 + prios3) in
        if rand < prios1 then
          let const = getConst rand lFF in
          let subf = genRF (pred n) in
          const subf
        else if rand < prios1 + prios2 then
          let const = getConst (rand-prios1) lFFF in
          let part = (Random.int (n - 2)) + 1 in
          let subf1 = genRF part in
          let subf2 = genRF (n-1-part) in
          const subf1 subf2
        else
          let const = getConst (rand-prios1-prios2) lPFF in
          let part = if simpleP then 1 else (Random.int (n - 2)) + 1 in
          let subp1 = genRP part in
          let subf2 = genRF (n-1-part) in
          const subp1 subf2
  and genRP = function
    | n when n <= 0 -> raise (Failure "size of formula must be positive")
    | 1 -> 
        let prios = addPrios lP in
        let rand = Random.int prios in
        getConst rand lP
    | n ->
        let prios1 = addPrios lPP in
        let prios2 = addPrios lFP in
        let prios3 = if n = 2 then 0 else addPrios lPPP in
        let rand = Random.int (prios1 + prios2 + prios3) in
        if rand < prios1 then
          let const = getConst rand lPP in
          let subp = genRP (pred n) in
          const subp
        else if rand < prios1 + prios2 then
          let const = getConst (rand-prios1) lFP in
          let subf = genRF (pred n) in
          const subf
        else
          let const = getConst (rand-prios1-prios2) lPPP in
          let part = (Random.int (n - 2)) + 1 in
          let subp1 = genRP part in
          let subp2 = genRP (n-1-part) in
          const subp1 subp2
  in
  (genRF, genRP)

(** Creates a formula (program) generator, i.e. a function which takes a depth
    and produces a randomly generated formula (program) with the given nesting depth.
    In the following, f stands for formula, p stands for program,
    and n stand for a priority which must be positive.
    @param lF A list of pairs (f, n), e.g. (p, 1).
    The list must not be empty.
    @param lFF A list of pairs (f->f, n), e.g. (~., 1).
    @param lFFF A list of pairs (f->f->f, n), e.g. (.&., 1).
    @param lPFF A list of pairs (p->f->f, n), e.g. (<.>., 1).
    At least one of lFF, lFFF, and lPFF must be non-empty.
    @param lP A list of pairs (p, n), e.g. (a, 1).
    The list must not be empty unless lPFF is also empty.
    @param lPP A list of pairs (p->p, n), e.g. ( *., 1).
    @param lFP A list of pairs (f->p, n), e.g. (?., 1).
    @param lPPP A list of pairs (p->p->p, n), e.g. (.+., 1).
    @return A pair (fktF, fktP) where
    fktF is a function that randomly generates a formula of a given depth, and
    fktP is a function that randomly generates a program of a given depth.
    Both functions use the constructors lF, ..., lPPP.
    Note that the size of the formula/program is not fixed.
    If lP is empty then fktP must not be invoked.
    If lP is not empty, but lPP, lFP, and LPPP are all empty,
    then fktP can only be invoked with depth naught.
 *)
let mk_generatorDepth lF lFF lFFF lPFF lP lPP lFP lPPP =
  let simpleP = lPP = [] && lFP = [] && lPPP = [] in
  let rec genRF = function
    | n when n <= 0 -> 
        let prios = addPrios lF in
        let rand = Random.int prios in
        getConst rand lF
    | n ->
        let prios1 = addPrios lFF in
        let prios2 = addPrios lFFF in
        let prios3 = addPrios lPFF in
        let rand = Random.int (prios1 + prios2 + prios3) in
        if rand < prios1 then
          let const = getConst rand lFF in
          let subf = genRF (pred n) in
          const subf
        else if rand < prios1 + prios2 then
          let const = getConst (rand-prios1) lFFF in
          let subf1 = genRF (pred n) in
          let subf2 = genRF (pred n) in
          const subf1 subf2
        else
          let const = getConst (rand-prios1-prios2) lPFF in
          let subp1 = genRP (if simpleP then 0 else pred n) in
          let subf2 = genRF (pred n) in
          const subp1 subf2
  and genRP = function
    | n when n <= 0 ->
        let prios = addPrios lP in
        let rand = Random.int prios in
        getConst rand lP
    | n ->
        let prios1 = addPrios lPP in
        let prios2 = addPrios lFP in
        let prios3 = addPrios lPPP in
        let rand = Random.int (prios1 + prios2 + prios3) in
        if rand < prios1 then
          let const = getConst rand lPP in
          let subp = genRP (pred n) in
          const subp
        else if rand < prios1 + prios2 then
          let const = getConst (rand-prios1) lFP in
          let subf = genRF (pred n) in
          const subf
        else
          let const = getConst (rand-prios1-prios2) lPPP in
          let subp1 = genRP (pred n) in
          let subp2 = genRP (pred n) in
          const subp1 subp2
  in
  (genRF, genRP)


(** Runs a list of solvers on a formula and records for each solver
    how long it took and whether it timed out.
    If a solver fails (i.e. throws an exception), it is handled
    as if it had timed out. Additionally, an error message is printed.
    If the solvers produce contradicting results, an error message is printed.
    @param ptime If a solver takes longer than ptime seconds for a formula,
    this formula and the running number of the solver are printed.
    @param timeout A timeout in seconds for each formula.
    A non-positive number is interpreted as infinity.
    @param tos If tos is non-empty, it must have the same length as solvl.
    In this case, each prover is only invoked
    if the corresponding tos entry is false;
    otherwise the prover is assumed to have timed out.
    @param expF Converts the formulae into a string representation.
    @param solvl A list of solvers. Each solver is a function
    which accepts a formula and a timeout as input,
    and returns a pair (resopt, rss) where
    resopt is the result and the needed time, or None iff the solver timed out; and
    rss is an approximation of the maximum amount of memory in kB
    which was used by the solver at some time during its runtime.
    This function does not check that the provers time out correctly.
    @param f A formulae.
    @return A tuple (res, tl) where:
    res is true if at least one solver returned that f is satisfiable,
    false if at least one solver returned that f is unsatisfiable, and
    undefined if all solvers timed out or failed for f; and
    tl is a list which contains for each solver s a triple (tm, dnf, rss) where:
    tm is the time needed by s to solve f (or the timeout); and
    dnf is true iff s timed out or failed for f; and
    rss is an approximation of the maximum amount of memory in kB
    which was used by s at some time during its runtime.
 *)
let runSolvers ?ptime ?timeout ?(tos = [| |]) expF solvl f = 
  let timeout =
    match timeout with
    | Some tout when tout > 0 -> tout
    | _ -> 0
  in
  let runS (fstres, idx, acc) solv =
    let ((resopt, rss), failed) =
      try
        if Array.length tos > 0 && tos.(pred idx) then ((None, 0), false)
        else (solv f timeout, false)
      with _ ->
        prerr_endline ("\nSolver " ^ (string_of_int idx) ^ " failed on formula: ");
        prerr_endline (expF f);
        ((None, 0), true)
    in
    if not failed && Array.length tos > 0 && resopt = None then tos.(pred idx) <- true else ();
    let (nfstres, time, dnf) =
      match resopt with
      | None -> (fstres, float_of_int timeout, true)
      | Some (res, time) ->
          let fstres1 =
            match fstres with
            | None -> Some res
            | Some fres ->
                if res = fres then ()
                else begin
                  prerr_endline ("\nSolver " ^ (string_of_int idx) ^ " returned different result for formula: ");
                  prerr_endline (expF f) (*;
                  failwith "results do not match" *)
                end;
                fstres
          in
          (fstres1, time, false)
    in
    let _ =
      if failed then () else
        match ptime with
        | Some pt when time >= pt ->
            let s = if dnf then " seconds (timed out) on formula: " else " seconds on formula: " in
            print_endline ("\nSolver " ^ (string_of_int idx) ^ " took " ^ (string_of_float time) ^ s);
            print_endline (expF f)
        | _ -> ()
    in
    (nfstres, succ idx, (time, dnf, rss)::acc)
  in
  let (resopt, _, tmsl) = List.fold_left runS (None, 1, []) solvl in
  (resopt, List.rev tmsl)

(** Runs a solver for different complexities of formulae.
    @param inter An optional function which accepts as argument
    the result of this function. It is called once for each complexity (after its completion)
    and passed as argument the intermediate result of this function.
    @param dots The number of dots in the progress bar for every complexity.
    @param tos Each element of this array is set to false
    at the beginning of the function.
    If defined then tos is used elsewhere to determine
    whether the provers have already timed out during the invocation of this function.
    @param genF A formula generator that takes a complexity as argument.
    @param comb A function combining the nr individual results within each complexity.
    @param init An initial value for comb.
    @param solver A solver which accepts a formula and produces a result.
    For example, it might be a function which invokes several "real" solvers.
    @param nr The number of formula that is generated for each complexity.
    @param start The initial complexity.
    @param stop The final complexity.
    @param step A function that produces the next complexity
    when given the current one.
    @return A list of pairs (c, r) where c is the complexity
    and r is the (combined) result returned by the solver for c.
 *)
let iterSolver ?inter ?dots ?(tos = [| |]) genF comb init solver nr start stop step =
  let pcstep =
    match dots with
    | Some n when n > 0 -> 1. /. (float n)
    | _ -> 0.
  in
  let fnr = float nr in
  let rec iterS2 compl pc i acc =
    if i <= nr then
      let f = genF compl in
      let res = solver f in
      let acc1 = comb res acc in
      let ratio = (float i) /. fnr in
      let npc =
        if pc > 0. && ratio >= pc then begin
          print_string "."; flush stdout;
          pc +. pcstep;
        end
        else pc
      in
      iterS2 compl npc (succ i) acc1
    else begin
      print_newline ();
      acc
    end
  in
  let rec iterS1 compl acc =
    if compl <= stop then begin
      print_endline (string_of_int compl);
      let res = iterS2 compl pcstep 1 init in
      let nacc = (compl, res)::acc in
      let _ =
        match inter with
        | None -> ()
        | Some fkt -> fkt (List.rev nacc)
      in
      iterS1 (step compl) nacc
    end
    else List.rev acc
  in
  let _ =
    for i = 0 to pred (Array.length tos) do
      tos.(i) <- false
    done
  in
  iterS1 start []

(** Writes data into a file which will then be displayed by a Gnuplot file.
    @param filenameD The filename of the file into which the data is written.
    @param nr The number of formula which is generated for each complexity.
    @param res The result of function "enumSolver".
 *)
let outputData filenameD nr res =
  let dout = open_out filenameD in
  let out2 (tmS, dnfS, rssS, tmU, dnfU, rssU, tmN, dnfN, rssN) = 
    output_string dout (string_of_float tmS);
    output_string dout " ";
    output_string dout (string_of_int dnfS);
    output_string dout " ";
    output_string dout (string_of_int rssS);
    output_string dout " ";
    output_string dout (string_of_float tmU);
    output_string dout " ";
    output_string dout (string_of_int dnfU);
    output_string dout " ";
    output_string dout (string_of_int rssU);
    output_string dout " ";
    output_string dout (string_of_float tmN);
    output_string dout " ";
    output_string dout (string_of_int dnfN);
    output_string dout " ";
    output_string dout (string_of_int rssN);
    output_string dout " "
  in
  let out1 (comp, (noS, noU, noN, tml)) =
    output_string dout (string_of_int comp);
    output_string dout (" " ^ (string_of_int nr) ^ " " ^ (string_of_int noS) ^ " " ^
                        (string_of_int noU) ^ " " ^ (string_of_int noN) ^ " ");
    List.iter out2 tml;
    output_string dout "\n"
  in
  List.iter out1 res;
  close_out dout

(** Generates a GnuPlot file which displays the information
    which is produced by the function "outputData".
    @param term The GnuPlot terminal which is used by filenameG.
    Some useful values are jpeg, gif, or postscript [eps].
    @param filenameG The filename of the GnuPlot file.
    @param filenameD The filename of the file which contains the data.
    @param labels A label for each solver.
 *)
let toGnuplot ?term filenameG filenameD labels =
  let gout = open_out filenameG in
  let rec plotout mul n = function
    | [] -> ()
    | h::tl ->
        let s6 = string_of_int (n*mul + 6) in
        let s9 = string_of_int (n*mul + 9) in
        let s12 = string_of_int (n*mul + 12) in
        let str = "\"" ^ filenameD ^ "\" using 1:(($" ^ s6 ^ "+$" ^ s9 ^ "+$" ^ s12 ^ ")/($3+$4+$5))" ^
          " with linespoints title \"" ^ h ^ " (time)\",\\\n     "
        in
        output_string gout str;
(*        
        let s7 = string_of_int (n*mul + 7) in
        let s10 = string_of_int (n*mul + 10) in
        let s13 = string_of_int (n*mul + 13) in
        let str = "\"" ^ filenameD ^ "\" using 1:($" ^ s7 ^ "+$" ^ s10 ^ "+$" ^ s13 ^ ")" ^
          " axes x1y2 with linespoints title \"" ^ h ^ " (timeouts))\",\\\n     "
        in
        output_string gout str;
 *)      
        let s8 = string_of_int (n*mul + 8) in
        let s11 = string_of_int (n*mul + 11) in
        let s14 = string_of_int (n*mul + 14) in
        let str = "\"" ^ filenameD ^ "\" using 1:(($" ^ s8 ^ "+$" ^ s11 ^ "+$" ^ s14 ^ ")/($3+$4+$5))" ^
          " axes x1y2 with linespoints title \"" ^ h ^ " (memory))\"" ^
          (if tl <> [] then ",\\\n     " else "\n")
        in
        output_string gout str;

        plotout mul (succ n) tl
  in
  let _ =
    match term with
    | Some str ->
        output_string gout ("set terminal " ^ str ^ "\n")
    | None -> ()
  in
  output_string gout ("set key top left\n");
  output_string gout ("set xlabel \"size of formulae\"\n");
  output_string gout ("set xtics nomirror\n");
  output_string gout ("set ylabel \"time per formula in seconds\"\n");
  output_string gout ("set ytics nomirror\n");
(*  output_string gout ("set y2label \"number of timeouts\"\n"); *)
  output_string gout ("set y2label \"used memory\"\n");
(*
  output_string gout ("set y2label \"percentage of satisfiable formulae\"\n");
  output_string gout ("set y2range [0:100]\n");
 *)
  output_string gout ("set y2tics nomirror\n");
  output_string gout "plot ";
  plotout 9 0 labels;
(*
  let str = "\"" ^ filenameD ^ "\" using 1:(100*$3/$2)" ^
    " axes x1y2 with linespoints title \"satisfiable formulae\"\n"
  in
  output_string gout str;
 *)
  if term = None then output_string gout "pause -1\n" else ();
  close_out gout

(** Runs a list of solvers for formulae of different complexities
    and outputs some information (e.g. if solvers return different results).
    Additionally it creates a gnuplot file
    which prints the running times and the number of timeouts
    for each solver and complexity as two graphs.
    @param filenameG The filename of the GnuPlot file.
    @param filenameD The filename of the file
    which will store the data used by filenameG.
    @param term The GnuPlot terminal which is used by filenameG.
    Some useful options are jpeg, gif, or postscript [eps].
    @param dots The number of dots in the progress bar for every complexity.
    @param ptime If a solver takes longer than ptime seconds for a formula,
    this formula and the running number of the solver are printed.
    @param ptime All formulae taking longer than ptime seconds are displayed.
    @param timeout A timeout in seconds for each formula.
    A non-positive number is interpreted as infinity.
    @param ko If set to true, a solver which timed out for the first time
    will not be invoked again, but is assumed to time out on all further formulae.
    @param expF Converts the formulae into a string representation.
    @param genF A formula generator that takes a complexity as argument.
    @param labsolvers A list of solvers together with their names.
    @param nr The number of formula that is generated for each complexity.
    @param start The initial complexity.
    @param stop The final complexity.
    @param step A function that produces the next complexity
    when given the current one.
    @return A list which contains for each complexity c a tuple (c, (ns, nu, tl)) where:
    ns is the number of satisfiable formulae for complexity c;
    nu is the number of unsatisfiable formulae for complexity c; and
    tl is a list which contains for each solver s a tuple (ts, tos, tu, tou) where:
    ts is the accumulated time needed by s to solve all satisfiable formulae;
    tos is the number of satisfiable formulae which s could not solve;
    tu is the accumulated time needed by s to solve all unsatisfiable formulae; and
    tou is the number of unsatisfiable formulae which s could not solve.
    Note that ns + nu < nr iff there are formulae which no prover could solve.
 *)
let enumSolver2 ?(filenameG = "plot") ?(filenameD = "data.dat") ?term
    ?dots ?ptime ?timeout ?(ko = false) expF genF labsolvers nr start stop step =
  assert (labsolvers <> []);
  let inter rl =
    let filename = filenameD ^ ".tmp" in
    outputData filename nr rl
  in
  let comb (resopt, tml) (accS, accU, accN, accT) =
    match resopt with
    | Some true ->
        let map2 (tm, dnf, rss) (tmS, noS, rssS, tmU, noU, rssU, tmN, noN, rssN) =
          let tmS1 = tm +. tmS in
          let noS1 = if dnf then succ noS else noS in
          let rssS1 = rss + rssS in
          (tmS1, noS1, rssS1, tmU, noU, rssU, tmN, noN, rssN)
        in
        let accT1 = List.map2 map2 tml accT in
        (succ accS, accU, accN, accT1)
    | Some false ->
        let map2 (tm, dnf, rss) (tmS, noS, rssS, tmU, noU, rssU, tmN, noN, rssN) =
          let tmU1 = tm +. tmU in
          let noU1 = if dnf then succ noU else noU in
          let rssU1 = rss + rssU in
          (tmS, noS, rssS, tmU1, noU1, rssU1, tmN, noN, rssN)
        in
        let accT1 = List.map2 map2 tml accT in
        (accS, succ accU, accN, accT1)
    | None ->
        let map2 (tm, dnf, rss) (tmS, noS, rssS, tmU, noU, rssU, tmN, noN, rssN) =
          let tmN1 = tm +. tmN in
          let noN1 = if dnf then succ noN else failwith "Bug in genAndComp.ml" in
          let rssN1 = rss + rssN in
          (tmS, noS, rssS, tmU, noU, rssU, tmN1, noN1, rssN1)
        in
        let accT1 = List.map2 map2 tml accT in
        (accS, accU, succ accN, accT1)
  in
  let init = (0, 0, 0, List.map (fun _ -> (0., 0, 0, 0., 0, 0, 0., 0, 0)) labsolvers) in
  let tos = if ko then Array.make (List.length labsolvers) false else [| |] in
  let solvers = List.map (fun (x, _) -> x) labsolvers in
  let solver f = runSolvers ?ptime ?timeout ~tos expF solvers f in
  let alarmHandler (n : int) = raise Timeout in
  let oldHandler = Sys.signal Sys.sigalrm (Sys.Signal_handle alarmHandler) in
  let res = iterSolver ~inter ?dots ~tos genF comb init solver nr start stop step in
  Sys.set_signal Sys.sigalrm oldHandler;
  outputData filenameD nr res;
  let labels = List.map (fun (_, y) -> y) labsolvers in
  toGnuplot ?term filenameG filenameD labels;
  res

(** Essentially the same as the funtion "enumSolver2".
    The only difference is the argument step
    which -- for this function -- is the difference
    between two consecutive complexities.
 *)
let enumSolver ?filenameG ?filenameD ?term
    ?dots ?ptime ?timeout ?ko expF genF labsolvers nr start stop step =
  let stp x = x + step in
  enumSolver2 ?filenameG ?filenameD ?term
    ?dots ?ptime ?timeout ?ko expF genF labsolvers nr start stop stp


(** Executes an external solver in a child process
    but aborts the execution if it takes longer than a given timeout.
    If the timeout is less then infinity,
    it is required that the Unix signal "sigalrm" is handled and
    that the handler raises the exception Timeout (see function "evaluateFkt").
    @param memtime The sampling interval in seconds
    for approximating the maximum amount of memory in kB
    which was used by the external solver at some time during its runtime.
    If the value is undefined or not positive, the memory usage is not determined.
    @param inpopt Some optional input
    which is passed to the external solver on the standard input.
    @param cmd The program name of the external solver.
    @param args Arguments for the external solver.
    @param isSat A regular expression which appears in the output of the external solver
    iff the input formula is satisfiable.
    More precisely, isSat has to match a substring of one of the output lines.
    @param timeout The maximal time in seconds
    that the external solver is allowed to take.
    A non-positive number is interpreted as infinity.
    @return (None, rss) if the external solver takes more than timeout seconds;
    (Some (res, t), rss) otherwise, where
    t (<= timeout) is the time needed by the external solver; and
    res is true iff isSat appears in the output of the external solver.
    In both cases, rss is an approximation of the maximum amount of memory in kB
    which was used by the external solver at some time during its runtime.
    If the memory usage is not sampled then 0 is returned.
    Note that res may be arbitrary if something goes wrong while invoking the external solver
    and this function does not notice it.
    @raise Failure if something goes wrong while invoking the external solver
    and this function does notice it.
 *)
let callExt ?memtime inpopt cmd args isSat timeout =
  let noto = timeout <= 0 in
  let (mmem, mtime) =
    match memtime with
    | Some n when n > 0 -> (true, n)
    | _ -> (false, 0)
  in
  let res = ref false in
  let argsA = Array.of_list (cmd :: args) in
  let (in_read, in_write) = Unix.pipe () in
  let (out_read, out_write) = Unix.pipe () in
  Unix.set_close_on_exec in_read;
  Unix.set_close_on_exec out_write;
  match Unix.fork () with
  | 0 -> begin
      Unix.dup2 in_write Unix.stdout;
      Unix.dup2 in_write Unix.stderr;
      Unix.close in_write; 
      Unix.dup2 out_read Unix.stdin;
      Unix.close out_read; 
      try
        Unix.execv cmd argsA
      with _ ->
        prerr_endline "function \"callExt\": external solver not found";
        exit 127
    end
  | id1 ->
      Unix.close in_write;
      Unix.close out_read;
      match Unix.fork () with
      | 0 ->
          Unix.close in_read;
          let _ =
            match inpopt with
            | None -> Unix.close out_write
            | Some inp ->
                let outchan = Unix.out_channel_of_descr out_write in
                output_string outchan inp;
                close_out outchan
          in
          exit 0
      | id2 ->
          Unix.close out_write;
          let (mem_read, mem_write) = if mmem then Unix.pipe () else (Unix.stdin, Unix.stdout) in
          match Unix.fork () with
          | 0 ->
              if not mmem then exit 0
              else begin
                Unix.close mem_read;
                let rss = ref 0 in
                let filename = "/proc/" ^ (string_of_int id1) ^ "/status" in
                let reg = Str.regexp "VmRSS:\t *\\([0-9]+\\) kB" in
                let _ =
                  try
                    while true do
                      let file = open_in filename in
                      try
                        while true do
                          let line = input_line file in
                          if Str.string_match reg line 0 then
                            let nrss = int_of_string (Str.matched_group 1 line) in
                            if nrss > !rss then rss := nrss else ()
                          else ()
                        done
                      with End_of_file ->
                        close_in file;
                        Unix.sleep mtime
                    done
                  with Sys_error _ -> ()
                in
                let memchan = Unix.out_channel_of_descr mem_write in
                output_string memchan (string_of_int !rss);
                close_out memchan;
                exit 0
              end
          | id3 ->
              if mmem then Unix.close mem_write else ();
              let inchan = Unix.in_channel_of_descr in_read in
              try
                if noto then () else ignore (Unix.alarm timeout);
                let start = Unix.gettimeofday () in
                let () =
                  try
                    while true do
                      let line = input_line inchan in
                      if !res then ()
                      else
                        try
                          let _ = Str.search_forward isSat line 0 in
                          res := true
                        with Not_found -> ()
                    done
                  with End_of_file -> ()
                in
                let stop = Unix.gettimeofday () in
                if noto then () else ignore (Unix.alarm 0);
                ignore (Unix.waitpid [] id2);
                let status = snd (Unix.waitpid [] id1) in
                let rss = 
                  if mmem then
                    let memchan = Unix.in_channel_of_descr mem_read in
                    let rss = int_of_string (input_line memchan) in
                    close_in memchan;
                    rss
                  else 0
                in
                ignore (Unix.waitpid [] id3);
                close_in inchan;
                match status with
                | Unix.WEXITED 0 -> 
                    let time = stop -. start in
                    (Some (!res, time), rss)
                | _ -> failwith "function \"callExt\": external solver failed"
              with Timeout ->
                assert (not noto);
                Unix.kill id1 Sys.sigkill;
                ignore (Unix.waitpid [] id1);
                Unix.kill id2 Sys.sigkill;
                ignore (Unix.waitpid [] id2);
                let rss = 
                  if mmem then
                    let memchan = Unix.in_channel_of_descr mem_read in
                    let rss = int_of_string (input_line memchan) in
                    close_in memchan;
                    rss
                  else 0
                in
                ignore (Unix.waitpid [] id3);
                let () =
                  try
                    Unix.close in_read;
                  with Unix.Unix_error _ -> ()
                in
                (None, rss)


(** Constructs a given number of elements
    and combines the result.
    @param op A binary function that combines
    the constructed elements. It should be associative.
    @param unit If zero elements are to be constructed
    then unit is returned.
    @param fkt This function constructs the elements.
    It accepts an integer as argument.
    @param n The number of elements that are to be constructed.
    @return If n <= 0 then unit,
    if n = 1 then f 0,
    else op (f 0) (op (f 1) (...))
 *)
let const_bigOp op unit fkt n =
  let rec intern_const i =
    let fi = fkt i in
    if i < pred n then
      let rest = intern_const (succ i) in
      op fi rest
    else fi
  in
  if n <= 0 then unit else intern_const 0

(** Combines the elements of a list.
    @param op A binary function that combines the elements of fl.
    It should be associative.
    @param unit If fl is the empty list then unit is returned.
    @param fl The list of elements.
    @return If fl = [] then unit,
    if fl = [f] then f,
    if fl = [f0; ...; fn] then op f0 (op f1 (...))
 *)
let rec const_bigOpL op unit fl =
  match fl with
  | [] -> unit
  | f::tl ->
      if tl = [] then f
      else
        let rest = const_bigOpL op unit tl in
        op f rest

(** Creates a list of ints in increasing order.
    @param n The size of the list
    @return A list of the form [0; 1; ...; n-1].
 *)
let mk_int_list n =
  let rec mk_lst acc = function
    | n when n <= 0 -> acc
    | n ->
        let pn = pred n in
        mk_lst (pn::acc) pn
  in
  mk_lst [] n


(** A record which provides all logical operations needed
    to generate the formulae below.
    It might, for example, be instantiated with constructors or
    string producing functions.
 *)
type ('a, 'b) logicFkts = {
    l_tt : 'a;
    l_ff : 'a;
    l_ap : string -> int -> 'a;
    l_not : 'a -> 'a;
    l_and : 'a -> 'a -> 'a;
    l_or : 'a -> 'a -> 'a;
    l_imp : 'a -> 'a -> 'a;
    l_aa : string -> int -> 'b;
    l_box : 'b -> 'a -> 'a;
    l_dia : 'b -> 'a -> 'a;
    l_aw : 'b list -> 'a -> 'a;
    l_ev : 'b list -> 'a -> 'a;
    l_until: 'a -> 'a -> 'a;
  }

(** An example of an instantiation
    which produces strings representing PDL formulae.
 *)
let exampleF = {
    l_tt = "True";
    l_ff = "False";
    l_ap = (fun s i -> s ^ (string_of_int i));
    l_not = (fun f1 -> "~" ^ f1);
    l_and = (fun f1 f2 -> "(" ^ f1 ^ " & " ^ f2 ^ ")");
    l_or = (fun f1 f2 -> "(" ^ f1 ^ " | " ^ f2 ^ ")");
    l_imp = (fun f1 f2 -> "(" ^ f1 ^ " => " ^ f2 ^ ")");
    l_aa = (fun s i -> s ^ (string_of_int i));
    l_box = (fun a f1 -> "[" ^ a ^ "]" ^ f1);
    l_dia = (fun a f1 -> "<" ^ a ^ ">" ^ f1);
    l_aw = (fun al f1 -> "[*(" ^ (List.hd al) ^ (List.fold_left (fun a s -> a ^ "+" ^ s) "" (List.tl al)) ^ ")]" ^ f1);
    l_ev = (fun al f1 -> "<*(" ^ (List.hd al) ^ (List.fold_left (fun a s -> a ^ "+" ^ s) "" (List.tl al)) ^ ")>" ^ f1);
    l_until = (fun f1 f2 -> failwith "Until not implemented")
  }

(** Generates a formula which forces a binary counter,
    represented by some propositional variables,
    to increase by one (modulo the bitlength) in all successor states.
    @param f All the logical operations needed.
    @param a The program which links to the successor states.
    @param p A prefix for the propositional variables.
    @param bs The bitsize of the counter.
    @return A formula f which forces the counter
    represented by the propositional variables p^"0", ..., p^(bs-1)
    to increase by one (modulo 2^bs) in all successor states
    which are related via a.
    If there are no such successor states then f is trivially true.
    The size of f is quadratic in bs.
 *)
let mk_counter f a p bs =
  let l_np p j = f.l_not (f.l_ap p j) in
  let fkt i =
    let f1 =
      let fkt1 j = f.l_and (f.l_ap p j) (f.l_box a (l_np p j)) in
      const_bigOp f.l_and f.l_tt fkt1 i
    in
    let f2 = if i < bs then f.l_and (l_np p i) (f.l_box a (f.l_ap p i)) else f.l_tt in
    let f3 =
      let fkt3 j =
        let pj = f.l_ap p (i+1+j) in
        let npj = l_np p (i+1+j) in
        f.l_and (f.l_imp pj (f.l_box a pj)) (f.l_imp npj (f.l_box a npj))
      in
      const_bigOp f.l_and f.l_tt fkt3 (bs-1-i)
    in
    const_bigOpL f.l_and f.l_tt [f1; f2; f3]
  in
  const_bigOp f.l_or f.l_ff fkt (succ bs)

(** Generates a formula so that every model which makes it true
    has a path of exponential length in the size of the formula.
    @param f All the logical operations needed.
    @param n A measure of the size which must be positive.
    @param unsat If unsat is true then the generated formula will be unsatisfiable.
    Of course, the model description does not make sense in this case,
    but the tableau procedure still has to build an exponential branch,
    before it can detect unsatisfiability.
    @return A formula f such that every model which makes f true
    has a path of length 2^n.
    The size of f is quadratic in n.
 *)
let mk_exptime_tbox f n unsat =
  let p = "p" in
  let a = f.l_aa "a" 0 in
  let l_np p j = f.l_not (f.l_ap p j) in
  let f0 = const_bigOp f.l_and f.l_tt (l_np p) n in
  let f1 = f.l_dia a f.l_tt in
  let f2 = mk_counter f a p n in
  let f3 = const_bigOp f.l_or f.l_ff (l_np p) n in
  let tbox = if unsat then [f1; f2; f3] else [f1; f2] in
  (f0, tbox)

let mk_exptime f n unsat =
  let (f0, tbox) = mk_exptime_tbox f n unsat in
  let ftbox = const_bigOpL f.l_and f.l_tt tbox in
  let a = f.l_aa "a" 0 in
  let ck = f.l_aw [a] ftbox in
  f.l_and f0 ck

(** Generates a formula that captures the fact
    that each person sees all the other persons
    (but not necessarily herself).
    @param f All the logical operations needed.
    @param p A prefix for the propositional variables.
    @param n The number of people involved.
    @return A formula f which says that
    any person can see whether a property, encoded by a^j, holds
    for any other person j.
    The size of f is quadratic in n.
 *)
let mk_know_it_all f p n =
  let fkt1 i =
    let pi = f.l_ap p i in
    let npi = f.l_not pi in
    let fkt2 j =
      if j = i then f.l_tt
      else
        let apj = f.l_aa p j in
        let f1 = f.l_imp pi (f.l_box apj pi) in
        let f2 = f.l_imp npi (f.l_box apj npi) in
        f.l_and f1 f2
    in
    const_bigOp f.l_and f.l_tt fkt2 n
  in
  const_bigOp f.l_and f.l_tt fkt1 n

(** Generates a formula that captures the wise men puzzle.
    @param f All the logical operations needed.
    @param n The number of wise men which must be positive.
    @param k The first k-1 wise men do not know
    whether they are wearing a black hat.
    The number must be positive and not greater than n.
    @return A formula ~f such that f says:
    If it is commonly known that at least one wise man is wearing a black hat,
    that each wise man can see all other wise men,
    and that the first k-1 wise men do not know whether they are wearing a black hat,
    then the k-th wise man knows that he is wearing a black hat.
    Note that f is a theorem iff n=k.
    The size of ~f is quadratic in n.
 *)
let mk_wisemen_tbox f n k =
  let p = "a" in
  let f1 = const_bigOp f.l_or f.l_ff (f.l_ap p) n in
  let f2 = mk_know_it_all f p n in
  let pk = pred k in
  let f3 =
    let fkt3 i = f.l_not (f.l_box (f.l_aa p i) (f.l_ap p i)) in
    const_bigOp f.l_and f.l_tt fkt3 pk
  in
  let concl = f.l_box (f.l_aa p pk) (f.l_ap p pk) in
  (concl, [f1; f2; f3])

let mk_wisemen f n k =
  let p = "a" in
  let (concl, tbox) = mk_wisemen_tbox f n k in
  let ftbox = const_bigOpL f.l_and f.l_tt tbox in
  let lst = mk_int_list n in
  let al = List.map (fun i -> f.l_aa p i) lst in
  let ck = f.l_aw al ftbox in
  f.l_not (f.l_imp ck concl)

(** Generates a formula that captures the muddy children puzzle.
    @param f All the logical operations needed.
    @param n The number of children which must be positive.
    @param k The number of muddy children
    which must be positive and not greater than n.
    @return A formula ~f such that f says:
    If it is commonly known that at least one child is muddy,
    that each child can see all other children,
    and that at least k children are muddy,
    then the fact that exactly k children are muddy implies
    that all muddy children know that they are muddy.
    Note that f is a theorem for all 1 <= k <= n.
    Depending on k, the size of ~f can be exponential in n.
 *)
let mk_muddychildren_tbox f n k =
  let p = "a" in
  let f1 = const_bigOp f.l_or f.l_ff (f.l_ap p) n in
  let f2 = mk_know_it_all f p n in
  let alpha nrl =
    assert (nrl <> []);
    let fkt i = if List.mem i nrl then f.l_ap p i else f.l_not (f.l_ap p i) in
    const_bigOp f.l_and f.l_tt fkt n
  in
  let nrl = mk_int_list k in
  let f3 =
    let rec mk_choose acc r n =
      if n <= 0 then [f.l_not (alpha acc)]
      else
        let pn = pred n in
        let l1 = if r > 0 then mk_choose (pn::acc) (pred r) pn else [] in
        let l2 = if n > r then mk_choose acc r pn else [] in
        l1 @ l2
    in
    let fkt3 i =
      let nll = mk_choose [] (succ i) n in
      const_bigOpL f.l_and f.l_tt nll
    in
    const_bigOp f.l_and f.l_tt fkt3 (pred k)
  in
  let concl =
    let c1 = alpha nrl in
    let cl = List.map (fun i -> f.l_box (f.l_aa p i) (f.l_ap p i)) nrl in
    let c2 = const_bigOpL f.l_and f.l_tt cl in
    f.l_imp c1 c2
  in
  (concl, [f1; f2; f3])

let mk_muddychildren f n k =
  let p = "a" in
  let (concl, tbox) = mk_muddychildren_tbox f n k in
  let ftbox = const_bigOpL f.l_and f.l_tt tbox in
  let lst = mk_int_list n in
  let al = List.map (fun i -> f.l_aa p i) lst in
  let ck = f.l_aw al ftbox in
  f.l_not (f.l_imp ck concl)


(** Encodes a Sudoku puzzle.
    The encoding is based on an initial version by Martin Lange.
    Note that a Sudoku can also be encoded as propositional formula.
    @param f All the logical operations needed.
    @param n The square root of the dimension of the Sudoku.
    That is, the Sudoku has n*n rows, columns, and blocks.
    @param unary Decides whether the encodings of the rows, columns, blocks,
    and input numbers are unary or binary.
    @param initV A list of tuples (x, y, r, c, i)
    where the first four numbers specify the position of an entry e
    and i specifies the value of that entry. More precisely:
    0 <= x < n is the row index of the block b in which e lies;
    0 <= y < n is the column index of b;
    0 <= r < n is the row index of e inside b;
    0 <= c < n is the column index of e inside b;
    0 <= i < n*n is the value of e.
    @return A formula f which encodes the Sudoku puzzle of dimension n*n
    with the given initial values.
    That is, f is satisfiable iff the Sudoku can be solved,
    and each model which makes f true gives rise to a solution of the Sudoku.
    The size of f is in O(n^4 * log n) in the binary case
    and O(n^4) in the unary case.
 *)
let mk_sudoku f n unary initV =
  let bits m = 
    let rec blog i = function
      | 0 -> raise (Failure "argument of function \"bits\" must be positive")
      | 1 -> i
      | m -> blog (i+1) (m/2)
    in
    blog 1 m
  in
  let bn = bits (pred n) in
  let nn = n*n in
  let bnn = bits (pred nn) in

  let a = f.l_aa "a" 0 in
  let l_box = f.l_box a in
  let l_dia = f.l_dia a in
  let l_aw = f.l_aw [a] in
  let mk_and_lst l = const_bigOpL f.l_and f.l_tt l in
  let propR i = f.l_ap "r" i in
  let propC i = f.l_ap "c" i in
  let propX i = f.l_ap "x" i in
  let propY i = f.l_ap "y" i in
  let propV i = f.l_ap "v" i in

  let eq_counter prop b m = 
    let fkt i = if m land (1 lsl i) <> 0 then prop i else f.l_not (prop i) in
    const_bigOp f.l_and f.l_tt fkt b
  in    
  let eq_coord prop m = if unary then prop m else eq_counter prop bn m in
  let eq_value m = if unary then propV m else eq_counter propV bnn m in

  let zeroR = eq_coord propR 0 in
  let zeroC = eq_coord propC 0 in
  let zeroX = eq_coord propX 0 in
  let zeroY = eq_coord propY 0 in
  let maxR = eq_coord propR (pred n) in
  let maxC = eq_coord propC (pred n) in
  let maxX = eq_coord propX (pred n) in
  let maxY = eq_coord propY (pred n) in

  let init = mk_and_lst [zeroR; zeroC; zeroX; zeroY] in

  let ax_initV =
    let setField (x, y, r, c, i) =
      let ante = mk_and_lst [eq_coord propR r; eq_coord propC c;
                             eq_coord propX x; eq_coord propY y] in
      f.l_imp ante (eq_value i)
    in
    mk_and_lst (List.map setField initV)
  in

  let is_unique prop m =
    let fkt1 i =
      let fkt2 j =
        let f2 = prop j in
        if i = j then f2 else f.l_not f2
      in
      const_bigOp f.l_and f.l_tt fkt2 m
    in
    const_bigOp f.l_or f.l_ff fkt1 m
  in
  let rec at_most_counter prop m bs =
    if bs = 0 then f.l_tt
    else
      let f1 = f.l_not (prop (pred bs)) in
      let f2 = at_most_counter prop m (pred bs) in
      if m land (1 lsl (pred bs)) <> 0 then f.l_or f1 f2 else f.l_and f1 f2
  in
  let valid_coord prop = if unary then is_unique prop n else at_most_counter prop (pred n) bn in
  let ax_validR = valid_coord propR in
  let ax_validC = valid_coord propC in
  let ax_validX = valid_coord propX in
  let ax_validY = valid_coord propY in
  let ax_validV = if unary then is_unique propV nn else at_most_counter propV (pred nn) bnn in

  let last = mk_and_lst [maxR; maxC; maxX; maxY] in
  let ax_nosuc = f.l_imp last (l_box f.l_ff) in
  let ax_suc = f.l_imp (f.l_not last) (l_dia f.l_tt) in

  let count_up prop x max null =
    if unary then
      let fkt i = f.l_imp (prop i) (l_box (prop ((succ i) mod n))) in
      const_bigOp f.l_and f.l_tt fkt n
    else
      let f1 = f.l_imp max (l_box null) in
      let f2 = f.l_imp (f.l_not max) (mk_counter f a x bn) in
      f.l_and f1 f2
  in
  let stay_same prop =
    let fkt i =
      let f1 = f.l_imp (prop i) (l_box (prop i)) in
      if unary then f1
      else
        let f2 = f.l_imp (f.l_not (prop i)) (l_box (f.l_not (prop i))) in
        f.l_and f1 f2
    in
    const_bigOp f.l_and f.l_tt fkt (if unary then n else bn)
  in
  let cond_count_up maxCondL prop x max null =
    let maxCond = mk_and_lst maxCondL in
    let f1 = f.l_imp maxCond (count_up prop x max null) in
    let f2 = f.l_imp (f.l_not maxCond) (stay_same prop) in
    f.l_and f1 f2
  in
  let ax_upR = count_up propR "r" maxR zeroR in
  let ax_upC = cond_count_up [maxR] propC "c" maxC zeroC in
  let ax_upX = cond_count_up [maxR; maxC] propX "x" maxX zeroX in
  let ax_upY = cond_count_up [maxR; maxC; maxX] propY "y" maxY zeroY in

  let no_doubles propA propB =
    let fkt1 i =
      let pAi = eq_coord propA i in
      let fkt2 j =
        let pBj = eq_coord propB j in
        let fkt3 k =
          let pVk = eq_value k in
          let ante = mk_and_lst [pAi; pBj; pVk] in
          let concl = l_box (l_aw (f.l_imp (f.l_and pAi pBj) (f.l_not pVk))) in
          f.l_imp ante concl
        in
        const_bigOp f.l_and f.l_tt fkt3 nn
      in
      const_bigOp f.l_and f.l_tt fkt2 n
    in
    const_bigOp f.l_and f.l_tt fkt1 n
  in
  let ax_no_doubles_block = no_doubles propX propY in
  let ax_no_doubles_row = no_doubles propX propR in
  let ax_no_doubles_col = no_doubles propY propC in

  let tbox = l_aw (mk_and_lst [ax_initV;
                               ax_validR; ax_validC; ax_validX; ax_validY; ax_validV;
                               ax_nosuc; ax_suc;
                               ax_upR; ax_upC; ax_upX; ax_upY;
                               ax_no_doubles_block; ax_no_doubles_row; ax_no_doubles_col])
  in
  f.l_and init tbox

(** An instance of a Sudoku which was considered easy.
 *)
let sudokuEasy = [(0,0,1,0,0);(0,0,0,1,2);(0,0,1,1,3);(0,0,2,2,5);
                  (0,1,0,0,4);(0,1,1,0,7);(0,1,0,1,8);
                  (0,2,2,0,0);(0,2,2,1,7);(0,2,1,2,6);(0,2,2,2,2);
                  (1,0,0,1,1);(1,0,1,1,7);(1,0,0,2,8);(1,0,2,2,4);
                  (1,1,1,0,3);(1,1,2,0,8);(1,1,0,1,4);(1,1,2,1,0);(1,1,0,2,2);(1,1,1,2,1);
                  (1,2,0,0,6);(1,2,2,0,2);(1,2,1,1,5);(1,2,2,1,3);
                  (2,0,0,0,1);(2,0,1,0,6);(2,0,0,1,4);(2,0,0,2,7);
                  (2,1,2,1,5);(2,1,1,2,4);(2,1,2,2,6);
                  (2,2,0,0,5);(2,2,1,1,8);(2,2,2,1,2);(2,2,1,2,3)]

(** An instance of a Sudoku which was considered tough.
 *)
let sudokuTough = [(0,0,1,0,5);
                   (0,1,1,0,6);(0,1,1,1,8);(0,1,0,2,7);(0,1,2,2,3);
                   (0,2,1,0,4);(0,2,1,2,1);(0,2,2,2,6);
                   (1,0,1,1,0);(1,0,0,2,4);(1,0,2,2,1);
                   (1,2,0,0,5);(1,2,2,0,8);(1,2,1,1,7);
                   (2,0,0,0,6);(2,0,1,0,3);(2,0,1,2,8);
                   (2,1,0,0,5);(2,1,2,0,4);(2,1,1,1,7);(2,1,1,2,6);
                   (2,2,1,2,2)]


(** Generates a satisfiable formula a la Goranko.
    @param f All the logical operations needed.
    @param n The size of the formulae.
    @return The formula "F p0 & ... & F pn-1"
 *)
let mk_eFormula f n =
  let a = f.l_aa "a" 0 in
  let fkt i = f.l_ev [a] (f.l_ap "p" i) in
  const_bigOp f.l_and f.l_tt fkt n

(** Generates a satisfiable formula a la Goranko.
    @param f All the logical operations needed.
    @param n The size of the formulae.
    @return The formula "G p0 & ... & G pn-1"
 *)
let mk_sFormula f n =
  let a = f.l_aa "a" 0 in
  let fkt i = f.l_aw [a] (f.l_ap "p" i) in
  const_bigOp f.l_and f.l_tt fkt n

(** Generates a satisfiable formula a la Goranko.
    @param f All the logical operations needed.
    @param n The size of the formulae.
    @return The formula "(((p0 U p2) U p3) U ...) U pn-1"
 *)
let rec mk_ulFormula f n =
  let n = pred n in
  if n <= 0 then f.l_ap "p" 0
  else
    let rest = mk_ulFormula f n in
    f.l_until rest (f.l_ap "p" n)

(** Generates a satisfiable formula a la Goranko.
    @param f All the logical operations needed.
    @param n The size of the formulae.
    @return The formula "p0 U (p1 U (... U pn-1))"
 *)
let rec mk_urFormula f n =
  const_bigOp f.l_until f.l_tt (fun i -> f.l_ap "p" i) n

(** Generates a satisfiable formula a la Goranko.
    @param f All the logical operations needed.
    @param n The size of the formulae.
    @return The formula "A F p_1 | ... | A F p_n"
 *)
let mk_c1Formula f n =
  let a = f.l_aa "a" 0 in
  let fkt i = f.l_aw [a] (f.l_ev [a] (f.l_ap "p" i)) in
  const_bigOp f.l_or f.l_ff fkt n

(** Generates a satisfiable formula a la Goranko.
    @param f All the logical operations needed.
    @param n The size of the formulae.
    @return The formula "A F p_1 & ... & A F p_n"
 *)
let mk_c2Formula f n =
  let a = f.l_aa "a" 0 in
  let fkt i = f.l_aw [a] (f.l_ev [a] (f.l_ap "p" i)) in
  const_bigOp f.l_and f.l_tt fkt n

(** Generates a formula which ensures seriality.
    @param f All the logical operations needed.
    @param al A list [a_0;...;a_n] of agents.
    @return The formula "AW (<a_0>True & ... & <a_n>True)"
 *)
let mk_serial f al =
  let exl = List.map (fun a -> f.l_dia a f.l_tt) al in
  let conj = const_bigOpL f.l_and f.l_tt exl in
  f.l_aw al conj

(** Generates a satisfiable formula a la Montali.
    @param f All the logical operations needed.
    @param n The number of propositional variables.
    @param d The nesting depth.
    @return A formula "F (p0 & AX F (p0 & AX F (... & AX F p0))) &
    G ((p0 => AX F p1) & ... & (pn-2 => AX F pn-1))"
 *)
let mk_montaliSat f n d =
  let a = f.l_aa "a" 0 in
  let n = max 1 n in
  let d = max 0 d in
  let rec fktD i =
    let p0 = f.l_ap "p" 0 in
    if i = d then p0
    else
      let f2 = fktD (succ i) in
      f.l_and p0 (f.l_box a (f.l_ev [a] f2))
  in
  let f1 = f.l_ev [a] (fktD 0) in
  if n = 1 then f1
  else
    let fktN i =
      let pi = f.l_ap "p" i in
      let pip = f.l_ap "p" (succ i) in
      f.l_imp pi (f.l_box a (f.l_ev [a] pip))
    in
    let f2 = const_bigOp f.l_and f.l_tt fktN (pred n) in
    f.l_and f1 (f.l_aw [a] f2)

(** Generates an unsatisfiable formula a la Montali.
    NOTE for CTL: formula is only unsatisfiable if AG/AU is taken for G/U.
    @param f All the logical operations needed.
    @param n The number of propositional variables.
    @param d The nesting depth.
    @return A formula "F (p0 & AX F (p0 & X F (... & X F p0))) &
    G ((p0 => AX (~p0 U p1)) & ... & (pn-2 => AX (~pn-2 U pn-1))) &
    ~(F (pn-1 & AX F (pn-1 & AX F (... & AX F pn-1))))"
 *)
let mk_montaliUnsat f n d =
  let a = f.l_aa "a" 0 in
  let n = max 1 n in
  let d = max 0 d in
  let p0 = f.l_ap "p" 0 in
  let rec fktD1 i =
    if i = d then p0
    else
      let f2 = fktD1 (succ i) in
      f.l_and p0 (f.l_box a (f.l_ev [a] f2))
  in
  let f1 = f.l_ev [a] (fktD1 0) in
  let pnm = f.l_ap "p" (pred n) in
  let rec fktD2 i =
    if i = d then pnm
    else
      let f2 = fktD2 (succ i) in
      f.l_and pnm (f.l_box a (f.l_ev [a] f2))
  in
  let f3 = f.l_not (f.l_ev [a] (fktD2 0)) in
  if n = 1 then f.l_and f1 f3
  else
    let fktN i =
      let pi = f.l_ap "p" i in
      let pip = f.l_ap "p" (succ i) in
      f.l_imp pi (f.l_box a (f.l_until (f.l_not pi) pip))
    in
    let f2 = const_bigOp f.l_and f.l_tt fktN (pred n) in
    f.l_and f1 (f.l_and (f.l_aw [a] f2) f3)

(** Generates an unsatisfiable formula a la Marrero.
    NOTE for CTL: formula is only unsatisfiable if AG/AF is taken for G/F.
    @param f All the logical operations needed.
    @param n The number of propositional variables.
    @return A formula "~(p0 & G (AND[0,n-1][pi => AX p(i+1modn)]) => G F p0)"
 *)
let mk_induction f n =
  assert (n > 0);
  let a = f.l_aa "a" 0 in
  let f1 =
    let fkt i = f.l_aw [a] (f.l_imp (f.l_ap "p" i) (f.l_box a (f.l_ap "p" ((succ i) mod n)))) in
    const_bigOp f.l_and f.l_tt fkt n
  in
  let p0 = f.l_ap "p" 0 in
  let f2 = f.l_and p0 f1 in
  let f3 = f.l_aw [a] (f.l_ev [a] p0) in
  f.l_not (f.l_imp f2 f3)

(** Generates an unsatisfiable formula a la Marrero.
    NOTE for CTL: formula is only unsatisfiable if AG/AF is taken for G/F.
    @param f All the logical operations needed.
    @param n The number of propositional variables.
    @return A formula "~(F pn & AND[0,n][~pi] & G (AND[0,n-1][~pi => AX ~pi+1]) => F p0)"
 *)
let mk_precede f n =
  assert (n > 0);
  let a = f.l_aa "a" 0 in
  let mkNF i = f.l_not (f.l_ap "p" i) in
  let f1 = const_bigOp f.l_and f.l_tt mkNF (n+1) in
  let f2 =
    let fkt i = f.l_aw [a] (f.l_imp (mkNF i) (f.l_box a (mkNF (succ i)))) in
    const_bigOp f.l_and f.l_tt fkt n
  in
  let f2 = f.l_and (f.l_ev [a] (f.l_ap "p" n)) (f.l_and f1 f2) in
  let f3 = f.l_ev [a] (f.l_ap "p" 0) in
  f.l_not (f.l_imp f2 f3)

(** Generates an unsatisfiable formula a la Marrero.
    NOTE for CTL: formula is only unsatisfiable if AG/AF is taken for G/F.
    @param f All the logical operations needed.
    @param n The number of propositional variables.
    @return A formula "~(G (F p0 & AND[0,n-1][pi => AX F p(i+1modn)]) => G F pn-1)"
 *)
let mk_fair f n =
  assert (n > 0);
  let a = f.l_aa "a" 0 in
  let f1 =
    let fkt i = f.l_aw [a] (f.l_imp (f.l_ap "p" i) (f.l_box a (f.l_ev [a] (f.l_ap "p" ((succ i) mod n))))) in
    const_bigOp f.l_and f.l_tt fkt n
  in
  let f2 =  f.l_and (f.l_aw [a] (f.l_ev [a] (f.l_ap "p" 0))) f1 in
  let f3 = f.l_aw [a] (f.l_ev [a] (f.l_ap "p" (pred n))) in
  f.l_not (f.l_imp f2 f3)

(** Generates a satisfiable formula a la Marrero.
    NOTE for CTL: formula is only unsatisfiable if AG/AF is taken for G/F.
    @param f All the logical operations needed.
    @param n The number of propositional variables.
    @return A formula "~(G (AND[0,n-1][pi => AX p(i+1modn)]) => G F p0)"
 *)
let mk_nobase f n =
  assert (n > 0);
  let a = f.l_aa "a" 0 in
  let f1 =
    let fkt i = f.l_aw [a] (f.l_imp (f.l_ap "p" i) (f.l_box a (f.l_ap "p" ((succ i) mod n)))) in
    const_bigOp f.l_and f.l_tt fkt n
  in
  let f2 = f.l_aw [a] (f.l_ev [a] (f.l_ap "p" 0)) in
  f.l_not (f.l_imp f1 f2)

(** Generates a formula a la Hustadt.
    @param f All the logical operations needed.
    @param k The number of "literals" in the clauses.
    @param l The number of clauses.
    @param n The number of propositional variables.
    @return A randomly generated formula as described in
    Hustadt and Konev: TRP++: A temporal resolution prover.
 *)
let gen_Cran1 f k l n =
  let a = f.l_aa "a" 0 in
  let lits = genLiterals (fun i -> f.l_ap "p" (int_of_string i)) "" n in
  let fktk (pi, _) =
    let li = if Random.bool () then pi else f.l_not pi in
    f.l_box a li
  in
  let fktl _ =
    let pls = chooseK k lits in
    let lls = List.map fktk pls in
    let cli = const_bigOpL f.l_or f.l_ff lls in
    f.l_aw [a] cli
  in
  let f1 = const_bigOp f.l_and f.l_tt fktl l in
  let fktp i =
    let npi = f.l_not (fst (List.nth lits i)) in
    let evip = f.l_ev [a] (fst (List.nth lits ((succ i) mod n))) in
    f.l_aw [a] (f.l_or npi evip)
  in
  let f2 = const_bigOp f.l_and f.l_tt fktp n in
  f.l_and f1 f2

(** Generates a formula a la Hustadt.
    @param f All the logical operations needed.
    @param k The number of "literals" in the clauses.
    @param l The number of clauses.
    @param n The number of propositional variables.
    @return A randomly generated formula as described in
    Hustadt and Konev: TRP++: A temporal resolution prover.
 *)
let gen_Cran2 f k l n =
  let a = f.l_aa "a" 0 in
  let lits = genLiterals (fun i -> f.l_ap "p" (int_of_string i)) "" n in
  let fktk (pi, _) = if Random.bool () then pi else f.l_not pi in
  let r0 = f.l_ap "r" 0 in
  let fktl _ =
    let pls = chooseK k lits in
    let lls = List.map fktk pls in
    const_bigOpL f.l_or f.l_ff (r0 :: lls)
  in
  let f1 = const_bigOp f.l_and f.l_tt fktl l in
  let fkt1 i =
    let l1 = f.l_not (f.l_ap "r" (n-1-i)) in
    let l2 = f.l_box a (f.l_ap "r" ((n-i) mod n)) in
    f.l_aw [a] (f.l_or l1 l2)
  in
  let f2 = const_bigOp f.l_and f.l_tt fkt1 n in
  let nqnm1 = f.l_not (f.l_ap "q" (n-1)) in
  let fkt2 i =
    let l1 = f.l_not (f.l_ap "r" (n-1-i)) in
    f.l_aw [a] (f.l_or l1 (f.l_box a nqnm1))
  in
  let f3 = const_bigOp f.l_and f.l_tt fkt2 n in
  let f4 = f.l_and (f.l_or (f.l_not r0) (f.l_ap "q" 0)) (f.l_or (f.l_not r0) nqnm1) in
  let fkt3 i =
    let g1 = f.l_or (f.l_not (f.l_ap "q" i)) (f.l_ev [a] (f.l_ap "s" (i+1))) in
    let h1 = f.l_or (f.l_not (f.l_ap "s" (i+1))) (f.l_ap "q" (i+1)) in
    let g2 =
      if i = n - 2 then h1
      else
        let fkt4 i = f.l_box a (f.l_ap "q" (n-1-i)) in
        let h2 = const_bigOp f.l_or f.l_ff fkt4 (n-2-i) in
        f.l_or h1 h2
    in
    f.l_and (f.l_aw [a] g1) (f.l_aw [a] g2)
  in
  let f5 = const_bigOp f.l_and f.l_tt fkt3 (n-1) in
  const_bigOpL f.l_and f.l_tt [f1; f2; f3; f4; f5]
