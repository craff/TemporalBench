

let pattern n =
  let rec lit i =
    "A G (E G (p"^string_of_int i^"))"
  in
  let rec nlit i =
    "A G (E G (~p"^string_of_int i^"))"
  in
  let rec left n =
    if n = 0 then [] else
      lit n :: left (n-1)
  in
  let rec right n =
    if n = 0 then [] else
      nlit n :: right (n - 1)
  in
  "(("
  ^ String.concat " & " (left n)
  ^ ") | ("
  ^ String.concat " & " (right n)
  ^ "))"


let out n =
  let ch = open_out ("pattern_" ^ string_of_int n ^ ".ctl") in
  Printf.fprintf ch "%s\n" (pattern n);
  close_out ch

let _ =
  let n = int_of_string Sys.argv.(1) in
  let i = ref 0 in
  while (!i < min 10 n) do
    i := !i + 1;
    out !i;
  done;
  while (!i < min 100 n) do
    i := !i + 5;
    out !i;
  done;
  while (!i < min 1000 n) do
    i := !i + 20;
    out !i;
  done
