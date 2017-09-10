(** A graph-multipass decision procedure for PLTL-satisfiability
    which blocks on all nodes,
    does not focus on a single formula, does not use annotated sets,
    It is optimal, that is EXPTIME.
	It can produce a model.
    @author Florian Widmann, Jimmy Thomson
 *)


module P = PLTLFormula

type formula = P.formula


open PLTLMisc
open MiscSolver

(** An instantiation of a hash table (of the standard library)
    for bitset-bset pairs.
 *)
module GHt = Hashtbl.Make(
  struct
    type t = bitset
    let equal bs1 bs2 = compareBS bs1 bs2 = 0
    let hash (bs1 : t)= hashBS bs1
  end
 )

module rec A :
    sig
      (** Indicates whether a node with defined status is an or-node or a state.
          For an or-node the following information is stored:
          (a) the principal formula of the or-node;
          (b) the children of the or-node
          For a state the following information is stored:
          (a) the children of the state
       *)
      type kindDef =
        | DOr of int * node list ref
        | DState of node

      (** Indicates whether a node with undefined status is an or-node or a state.
          For an or-node the following information is stored:
          (a) see kindDef;
          (b) see kindDef;
          (c) see kindDef;
          (d) the number of remaining decompositions of the principal formula
          of the or-node which still have to be processed.
          For a state the following information is stored:
          (a) see kindDef;
          (b) the EX-formulae of the state which still have to be processed;
          note that the first element of the list is the EX-formulae
          which is currently being processed.
       *)
      and kindUndef =
        | UOr of int * node list ref * int ref
        | UState of node

      (** The status of a node.
          Sat: The node is satisfiable.
          Unsat: The node is unsatisfiable.
          Undef: The node has not been fully processed yet.
          (a) the set of formulae of the node;
          (b) a singleton list containing the parent of the node,
          (if the node is the root node then the list is empty);
          (c) all relevant nodes which point to this node via bw- or upd-edges;
          (d) see kindUndef.
          Unknwn: The node has been fully processed
          but it is not known yet whether or not the node is satisfiable.
		  (a) The set of formulae
		  (b) The ordering on eventualities
		  (c) The focused formula
		  (d) The parent of the node as a singleton list
		  (e) The set of nodes pointing to this nod evia bw- or upd-edges
		  (f) The time this was first assigned
		  (g) A counter used for the mark and sweep phase
		  (h) See kindDef
       *)
      and status =
        | Sat
        | Unsat
        | Undef of  bitset * node list * NSet.t ref * int ref * kindUndef
        | Unknwn of bitset * node list * NSet.t ref * int * int array * kindDef

      (** Some information about a node which is stored in the graph:
          (a) a unique id number for each node; and
          (b) the current status of the node.
       *)
      and node = { id : int; mutable status : status }

      type t = node
      val compare: t -> t -> int
    end
    = struct
      type kindDef =
        | DOr of int * node list ref
        | DState of node

      and kindUndef =
        | UOr of int * node list ref * int ref
        | UState of node

      and status =
        | Sat
        | Unsat
        | Undef of bitset * node list * NSet.t ref * int ref * kindUndef
        | Unknwn of bitset * node list * NSet.t ref * int * int array * kindDef

      and node = { id : int; mutable status : status }

      type t = node

        let compareNode (n1 : node) n2 =
          let id1 = n1.id in
          let id2 = n2.id in
          if id1 < id2 then (-1)
          else if id1 > id2 then 1
          else 0

        let compare: t -> t -> int = compareNode
    end
and NSet : Set.S with type elt = A.t = Set.Make(A)

open A




(** A prototype unsatisfiable node.
 *)
let unsatNode = { id = 0; status = Unsat }

(** A prototype satisfiable node.
 *)
let satNode = { id = 0; status = Sat }



(** Represents a graph. The nodes are indexed by two sets of formulae.
    The first set contains the formulae of the node and the second set
    contains the [*]-formulae which have already been expanded.
 *)
type graph = node GHt.t

(** Empties a graph.
    @param grph A graph.
 *)
let emptyGraph (grph : graph) = GHt.clear grph

(** Returns the node which is assigned to a pair of sets of formulae
    in a graph if it exists.
    @param grph A graph.
    @param fs1 A first bitset of formulae.
    @param fs2 A second bitset of formulae.
    @return None if no node with (fs1, fs2) is contained in grph,
    Some n otherwise where n is the corresponding node.
 *)
let memGraph (grph : graph) fs1  = 
  try
    Some (GHt.find grph fs1)
  with Not_found -> None

(** Adds a pair of sets of formula and its node to a graph.
    @param grph A graph.
    @param fs1 A first bitset of formulae.
    @param fs2 A second bitset of formulae.
    @param nde The node with fs1 and fs2.
 *)
let addGraph (grph : graph) fs1 nde = GHt.add grph fs1 nde

(** Returns the size of a graph.
    @param grph A graph.
    @return The number of nodes in grph.
 *)
let sizeGraph (grph : graph) = GHt.length grph

let printBS bs oc =
  output_string oc "{";
  for i = 0 to !nrFormulae-1 do
	if memBS bs i then begin
		output_string oc (P.exportFormula !arrayFormula.(i));
		output_string oc ", "
	  end
  done;
  output_string oc "}"


let printList ls oc =
  output_string oc "[";
  let f x = output_string oc (string_of_int x); output_string oc ", " in
	List.iter f ls;
	output_string oc "]"

let printBSNde stat oc =
  match stat with
	| Unknwn (fs,_,_,_,_,kind) ->
		begin
		  match kind with
			| DOr (pf, _) -> output_string oc (P.exportFormula !arrayFormula.(pf))
			| DState _ ->
				for i = !lposEX to !nrFormulae-1 do
				  if memBS fs i then
					output_string oc ((P.exportFormula !arrayFormula.(i)) ^ ", ")
				done
		end;
	| _ -> ()
		

let satAny fs =
  let i = ref !lposUN in
  let ret = ref false in
	while not !ret && !i <= !hposUN do
	  if containsFormula fs !arrayDest1.(!i) then
		ret := true;
	  incr i
	done;
	!ret


(** This prints the graph as constructed by the decision procedure: It is a pseudomodel, not a model. *)		
let printGraph grph oc = 
  output_string oc "digraph grph {"; output_char oc '\n';
  let initPrintNode fs nde =
	match nde.status with
	  | Unknwn _->
		  output_string oc ("n" ^ (string_of_int nde.id));
		  output_string oc " [URL=\"javascript:alert('";
		  printBSNde nde.status oc;
		  output_string oc "')\""; 
		  if satAny fs then output_string oc ",color=red";
		  output_string oc "]"; output_char oc '\n' ;
	  | Sat ->
		  output_string oc ("n" ^ (string_of_int nde.id));
		  output_string oc " [style=filled,color=\"yellow\"]"; output_char oc '\n';
	  | Unsat ->
		  ()
(*		  output_string oc ("//n" ^ (string_of_int nde.id));
		  output_string oc " [style=filled,color=\"red\"]"; output_char oc '\n';*)
	  | _ -> ()
  in
  let printEdges _ nde =
	match nde.status with
	  | Sat | Unsat -> ()
	  | Unknwn (_,_,_,_,_,kind) ->
		  begin
			match kind with
			  | DOr (_,children) ->
				  let printEdge h =
					match h.status with
					  | Unsat -> ();
					  | _ ->
						  output_string oc ("n" ^ (string_of_int nde.id) ^ " -> n" ^ (string_of_int h.id) ^ " [style=dashed]");
						  output_char oc '\n'
				  in
					List.iter printEdge !children
			  | DState child ->
				  output_string oc ("n" ^ (string_of_int nde.id) ^ " -> n" ^ (string_of_int child.id) ^ " [style=solid]");
				  output_char oc '\n'
		  end
	  | _ -> output_string oc (" // n" ^ (string_of_int nde.id) ^ "Undef"); output_char oc '\n'
  in
	GHt.iter initPrintNode grph;
	GHt.iter printEdges grph;
	output_string oc "}";
	output_char oc '\n'


(** This is used to convert from the binary-or tree to an and/or graph with variable branching factor

	ANode (id, formulae, distance to satisfying eventualities, or-children)
	ONode (id, distance, and-children)
*)
type aonode = ANode of int * bitset * (int array) * int
			| ONode of int * (int array) * (int list)

module IHt = Hashtbl.Make(
  struct
    type t = int
    let equal a b = a =b
    let hash (a : t)= a
  end
 )


type aograph = aonode IHt.t


(** 
	Functions used to convert from the original graph to an and/or tree with n-ary or branches,
	where each node tracks how far before an eventuality is satisfied
*)

let rec insertState id = function
  | [] -> [id]
  | h::t ->
	  if h = id then h::t
	  else if h < id then h::(insertState id t)
	  else (* h > id*) id :: (h::t)

let rec follow acc node = 
  match node.status with
	| Unknwn (fs,_,_,_,_,kind) ->
		begin
		  match kind with
			| DOr (_,children) ->
				let rec f acc = function
				  | [] -> acc
				  | h::t -> f (follow acc h) t
				in
				f acc !children
			| DState _ ->
				insertState node.id acc
		end
	| _ -> acc


let rec findParents fromgraph tograph distances queue start =
  match start.status with
	| Unknwn (_,_,_,_,_,DState _ ) ->
		begin
		  let node = IHt.find tograph start.id in
			match node with
			  | ANode (id,fs,dist,_) ->
				  let changed = ref false in
					for i = 0 to !hposUN - !lposUN do
					  if containsFormula fs !arrayDest2.(i+ !lposUN) then (* Only calculate length for paths required to satisfy it *)
						if distances.(i) >= 0 && (distances.(i) + 2 < dist.(i) || dist.(i) = -1) then begin
							dist.(i) <- distances.(i) +2;
							changed := true
						  end
					done;
					let f b x =
					  b || x = id
					in
					  if !changed  && not (Queue.fold f false queue) then begin
						  Queue.add id queue
						end
			  | _ -> ()
		end
	| Unknwn (_,parent,dependents,_,_,DOr _) ->
		List.iter (findParents fromgraph tograph distances queue) parent;
		NSet.iter (findParents fromgraph tograph distances queue) !dependents
	| _ -> ()
  

let setDistance fromgraph tograph queue =
  while not (Queue.is_empty queue) do
	let nodeid = Queue.pop queue in
	let node = IHt.find tograph nodeid in
	  match node with
		| ANode (id,fs,distances,_) ->
			begin
			  let nde = GHt.find fromgraph fs in
				match nde.status with
				  | Unknwn (_,parent,dependents,_,_,kind) ->
					  List.iter (findParents fromgraph tograph distances queue) parent;
					  NSet.iter (findParents fromgraph tograph distances queue) !dependents
				  | _ -> ()
			  (* Find all immediate ancestor states *)
			  (* update all distances where appropriate *)
			  (* add updated ancestors to the queue*)
			end
		| _ -> ()
  done;
  (* update all or-nodes*)
  let setOr _ node =
	match node with
	  | ONode (id,distances,children) ->
		  begin
			let rec f = function
			  | [] -> ()
			  | h::t ->
				  (try
					   let node = IHt.find tograph h in
						 match node with
						   | ANode(_,_,subdist,_) ->
							   for i = 0 to !hposUN - !lposUN do
								 if distances.(i) = -1 || subdist.(i) +1< distances.(i) then
								   distances.(i) <- subdist.(i)+1
							   done
						   | _ -> ()
				   with Not_found -> ());
				  f t
			in
			  f children
		  end
	  | _ -> ()
  in
	IHt.iter setOr tograph

(** Given the pseudomodel and the seed for satisfied eventualities, construct the and/or graph, including the distance to eventualities *)
let collapse grph goodNodes =
  let cores = ref [] in
  let size = if (!hposUN - !lposUN) < 0 then 0 else (!hposUN - !lposUN) +1 in
  let andor = (IHt.create 1024 : aograph) in
  let getCore l =
	let rec searchCores l = function
	  | [] -> None
	  | (lst,oid)::t ->
		  if lst = l then
			Some oid
		  else
			searchCores l t
	in
	  match searchCores l !cores with
		| Some n -> n
		| None ->
			let id = getNewId () in
			let nde = ONode (id,Array.make size (-1),l) in
			  IHt.add andor id nde;
			  cores := (l,id)::!cores;
			  id
  in
  (* Construct And/Or graph*)
  let constructandfn _ node =
	match node.status with
	  | Unknwn (fs,_,_,_,_,kind) ->
		  begin
			match kind with
			  | DState child ->
				  let id = node.id in
				  let ochild = getCore (follow [] child) in
				  let nde = ANode (id,fs,Array.make size (-1),ochild) in
					IHt.add andor id nde
			  | _ -> ()
		  end
	  | _ -> ()
  in
	GHt.iter constructandfn grph;
	(* andor now contains the and/or graph, without distance information*)
	let toExamine = Queue.create () in
	let initDistance node =
	  match node.status with
		| Unknwn (fs,_,_,_,_,DState _) ->
			begin
			  let isAny = ref false in
				try 
				  let nde = IHt.find andor node.id in
					match nde with 
					  | ANode (_,_,distance,_) ->
						  for i = !lposUN to !hposUN do
							if containsFormula fs !arrayDest1.(i) then begin
								distance.(i - !lposUN) <- 0;
								isAny := true
							  end
						  done;
						  if !isAny then 
							Queue.add node.id toExamine
					  | _ -> ()
				with Not_found -> ()
			end
		| _ -> ()
	in
	  NSet.iter initDistance goodNodes;
	  (* andor now has 0 distance where eventualities are satisfied*)
	  setDistance grph andor toExamine;
	  (* andor is now complete *)
	  andor


let printAndOr graph ograph root oc =
  output_string oc "digraph G {\n";
  output_string oc ("ROOT [stlye=dashed, color=red]\n");
  let roots =
	let rec f acc n = 
	  match n.status with
		| Unknwn(_,_,_,_,_,kind) ->
			begin
			  match kind with
				| DState _->
					if not (List.mem n.id acc) then
					  n.id::acc
					else
					  acc
				| DOr (_,children)-> 
					let rec g acc = function
					  | [] -> acc
					  | h::t -> g (f acc h) t
					in
					g acc !children
			end
		| _ -> acc
	in
	  f [] root
  in
  List.iter (fun id -> output_string oc ("ROOT -> n" ^ (string_of_int id) ^ " [style=dashed]\n")) roots;
  let printNode id node = 
	match node with
	  | ANode (_,fs,_,_) ->
		  begin
			output_string oc ("n"^(string_of_int id));
			output_string oc (" [URL=\"javascript:alert('");
			for i = !lposEX to !nrFormulae-1 do
			  if memBS fs i then
				output_string oc ((P.exportFormula !arrayFormula.(i)) ^", ")
			done;
			output_string oc ("')\"");
			output_string oc ("]\n");
		  end
	  | ONode (_,_,_) ->
		  output_string oc ("n"^(string_of_int id));
		  output_string oc (" [style=dashed]\n");
  in
  let printEdge id node =
	match node with
	  | ANode (_,_,_,child) ->
		  output_string oc ("n"^(string_of_int id));
		  output_string oc (" -> ");
		  output_string oc ("n"^(string_of_int (child)));
		  output_string oc (" [style=solid]");
		  output_char oc '\n'
	  | ONode (_,_,children) ->
		  let anEdge child = 
			output_string oc ("n"^(string_of_int id));
			output_string oc (" -> ");
			output_string oc ("n"^(string_of_int (child)));
			output_string oc (" [style=dashed]");
			output_char oc '\n'
		  in
			List.iter anEdge children

  in
	IHt.iter printNode graph;
	IHt.iter printEdge graph;
  output_string oc "}\n"



(** 
	find a DAG given a root which satisfies a given eventuality
*)

(* unique id, original id, children *)
type modelnode = MNode of int * int * int
			   | MFringe of int * int
			   | MRedir of int (* Redirect instead *)

type model = modelnode IHt.t


(* Given a model (and the and/or graph for formula lookup) print the model*)
let printModel graph model root oc =
  output_string oc "digraph G {\n";
  let printNode id node = 
	match node with
	  | MNode (_,oid,_) ->
		  begin
			match IHt.find graph oid with
			  | ANode (_,fs,_,_) ->
				  output_string oc ("n"^(string_of_int id));
				  output_string oc (" [URL=\"javascript:alert('");
				  for i = !lposEX to !nrFormulae-1 do
					if memBS fs i then
					  output_string oc ((P.exportFormula !arrayFormula.(i)) ^", ")
				  done;
				  output_string oc ("')\"");
				  if root = id then output_string oc ",color=red";
				  output_string oc ("]\n");
			  | _ -> ()
		  end
	  | MRedir _ -> ()
	  | MFringe (_,oid) ->
		  match IHt.find graph oid with
			| ANode (_,fs,_,_) ->
				output_string oc ("n"^(string_of_int id));
				output_string oc (" [URL=\"javascript:alert('");
				for i = !lposEX to !nrFormulae-1 do
				  if memBS fs i then
					output_string oc ((P.exportFormula !arrayFormula.(i)) ^", ")
				done;
				output_string oc ("')\"");
				output_string oc ",style=filled,color=yellow";
				output_string oc ("]\n");
			| _ -> ()
		  
  in
  let printEdge id node =
	match node with
	  | MNode (_,_,child) ->
		  let rec getChild c =
			try
			  match IHt.find model c with
				| MNode (id,oid,_) -> id
				| MRedir oid -> getChild oid
				| MFringe (id,oid) ->  id
			with Not_found -> c
		  in
		  let anEdge child = 
			output_string oc ("n"^(string_of_int id));
			output_string oc (" -> ");
			output_string oc ("n"^(string_of_int (getChild child)));
			output_char oc '\n'
		  in
			anEdge child
	  | _ -> ()
  in
	IHt.iter printNode model;
	IHt.iter printEdge model;
  output_string oc "}\n"

let debugoc = ref None


let makeFringeNode fringe model node =
  (* Search fringe for node*)
  (* if found : return that node *)
  (* if not   : add node to fringe, return that node *)
  try
	let id = IHt.find fringe node in
	  id
  with Not_found ->
	let id = getNewId () in
	let nde = MFringe (id, node) in
	IHt.add model id nde;
	IHt.add fringe node id;
	id

let rec dagU graph model fringe node eventuality =
  match IHt.find graph node with 
	| ANode (id, fs, dist, child) ->
		let idx = eventuality - !lposUN in
		let d = dist.(idx) in
		  if d = 0 then begin
 			  (* satisfied here*)
			  makeFringeNode fringe model id
			end
		  else if d < 0 then begin
			  print_endline "U on wrong path!";
			  raise Not_found
			end
		  else begin
			  (* For each child, pick the one with lowest distance *)
			  let rec findandchild d = function
				| [] -> 
					print_endline "dagAU findandchild";
					raise Not_found
				| h::t ->
					if (h = node) then
					  findandchild d t
					else
					  match IHt.find graph h with
						| ANode (_,fs,dist,_) ->
							if dist.(idx) = d-1 then
							  dagU graph model fringe h eventuality
							else
							  findandchild d t
						| _ -> findandchild d t
			  in
			  let mchild = match IHt.find graph child with
				| ONode (_,dist, children) ->
					let d = dist.(idx) in
					  (findandchild d children)
				| _ ->
					print_endline "dagAU getChildren";
					raise Not_found
			  in
			  let myid = getNewId() in
				IHt.add model myid (MNode(myid, id, mchild));
				myid
			end
	| _ -> -1


(* Plan to attempt to reduce number of nodes:
   Step 1) Deal with EU formulae
   Step 2) Add any remaining EX formulae -- checking to see if they are already accounted for
   Step 3) Extend to include AU formulae
   Step 4) the fragment is now complete. All nodes on the fringe now qualify to have fragments made of them (change from high id to original ID, for easy linkage)
*)

let rec walkU graph model fringe node eventuality =
  match IHt.find model node with
	| MNode (id,oid,child) ->
		begin
		  match IHt.find graph oid with
			| ANode (id,fs,dist,_) ->
			  let idx = eventuality - !lposUN in
				let d = dist.(idx) in
				  if d = 0 then begin
					  (* satisfied here*)
					  ()
					end
				  else if d < 0 then
					(* ERROR *)
					print_endline "Error! AU Eventuality not found!"
				  else
					walkU graph model fringe child eventuality
			| _ -> ()
		end
	| MFringe (id,oid) ->
		IHt.remove fringe oid;
		IHt.remove model id;
		IHt.add model id (MRedir (dagU graph model fringe oid eventuality))
	| MRedir id ->
		walkU graph model fringe id eventuality

let getFrag graph model node (queue : int Queue.t) = 
  let fringe = IHt.create 1024 in
	if not (IHt.mem model node) then
	  (* A new frag has to be created in the model*)
	  match IHt.find graph node with
		| ANode (id,fs,dist,child) ->
			let mchild = 
			  match IHt.find graph child with
				| ONode (_,_,children) ->
					begin
					match IHt.find graph (List.hd children) with
					  | ANode (oid,fs,_,_) ->
						  makeFringeNode fringe model oid
					  | _ -> raise (Failure "Error finding AND-child")
					end
				| _ -> raise (Failure "Error finding OR-child")
			in
			let nde = MNode (node,node,mchild) in
			  IHt.add model node nde;
			  for i = !lposUN to !hposUN do
				if containsFormula fs i then
				  walkU graph model fringe node i
			  done;
			  (* Now the fragment is complete, and the fringe nodes are "important" *)
			  let finishFringe _ id =
				match IHt.find model id with
				  | MFringe (_,oid) ->
					  IHt.replace model id (MRedir oid);
					  Queue.add oid queue
				  | _ ->
					  print_endline "ERROR! Fringe nodes not fringe?";
					  raise Not_found
			  in
				IHt.iter finishFringe fringe
		| _ -> ()
			


let emersonUnwind graph (root:int) =
  let queue = Queue.create () in
  let model = IHt.create 1024 in
	Queue.add root queue;
	while not (Queue.is_empty queue) do
	  let n = Queue.pop queue in
		getFrag graph model n queue;
		match !debugoc with
		  | None -> ()
		  | Some oc -> printModel graph model n oc
	done;
	model




(*type aonode = ANode of int * bitset * (int array) * int
			| ONode of int * (int array) * (int list)*)

let printTraces andor nde oc =
  let printLookup id node =
	match node with
	  | ANode (_,fs,_,_) ->
		  output_string oc ((string_of_int id) ^" = {");
		  for i = 0 to !nrFormulae-1 do
			if memBS fs i && (!arrayType.(i) = 2 || !arrayType.(i) = 3) then begin
				output_string oc (P.exportFormula (!arrayFormula.(i)));
				output_string oc ", ";
			  end
		  done;
		  output_string oc "};\n"
	  | _ -> ()
  in
	  IHt.iter printLookup andor;
  let rec iterTraces hist ni n =
	if List.mem ni hist then
	  let rec pTrace = function
		| [] -> output_string oc ((string_of_int ni)^"];\n")
		| h::t -> output_string oc ((string_of_int h) ^ ",");
			pTrace t
	  in
		output_string oc "[";
		pTrace (List.rev hist);
	else
	  match n with
		| ANode(_,_,_,child) ->
			iterTraces (ni::hist) child (IHt.find andor child)
		| ONode (_,_,children) ->
			List.iter (fun child -> iterTraces hist child (IHt.find andor child)) children
  in
  let roots =
	let rec f acc n = 
	  match n.status with
		| Unknwn(_,_,_,_,_,kind) ->
			begin
			  match kind with
				| DState _->
					if not (List.mem n.id acc) then
					  n.id::acc
					else
					  acc
				| DOr (_,children)-> 
					let rec g acc = function
					  | [] -> acc
					  | h::t -> g (f acc h) t
					in
					g acc !children
			end
		| _ -> acc
	in
	  f [] nde
  in
  let startTrace root =
	let aonode = IHt.find andor root in
	  iterTraces [] root aonode
  in
	List.iter startTrace roots
  

let rec getRoot node =
  match node.status with
	| Unknwn (_,_,_,_,_,kind) ->
		begin
		  match kind with
			| DState _ -> node.id
			| DOr (_,children)-> 
				let rec f = function
				  | [] -> -1
				  | h::t ->
					  let v = getRoot h in
						if v < 0 then f t
						else v
				in
				  f !children
		end
	| _ -> -1
	  
	  
(** The graph of the decision procedure.
*)
let grph = (GHt.create 1024 : graph)
  
let goodEdges = ref NSet.empty
let markPass = ref 0
let tEvent = ref 0.

let mkArr () =
  let size = if (!hposUN - !lposUN) < 0 then 0 else (!hposUN - !lposUN) +1 in
	Array.make size !markPass

let markOr fs mark other =
  let changed = ref false in
	for i = 0 to (!hposUN - !lposUN) do
	  let init = mark.(i) in
		if mark.(i) < other.(i) then begin
			mark.(i) <- other.(i);
		  end;
		if containsFormula fs !arrayDest1.(i + !lposUN) then
		  mark.(i) <- !markPass;
		if init <> mark.(i) then changed := true;
	done;
	!changed

let markAnd fs mark child =
  let changed = ref false in
	for i = 0 to (!hposUN - !lposUN) do
	  let init = mark.(i) in
	  let v = match child.status with
		| Unknwn(_,_,_,_,mrk,_) ->
			mrk.(i)
		| Unsat -> (-1)
		| _ -> print_endline "ERROR in markAnd"; (-1)
	  in
		mark.(i) <- v;
		if containsFormula fs !arrayDest1.(i + !lposUN) then
		  mark.(i) <- !markPass;
		if init <> mark.(i) then changed := true
	done;
	!changed

let checkMark fs mark =
  let ret = ref false in
  for i = 0 to !hposUN - !lposUN do
	if memBS fs (i + !lposUN) && mark.(i) <> !markPass then
	  ret := true
  done;
  !ret
		
(* Determines regions of unfulfilled eventualities *)
let findSatisfyingRegion nodes =
  let same = ref false in
  let start = Unix.gettimeofday () in
  let queue = Queue.create () in
  let fn x = Queue.add x queue in
	while not !same do
	  same := true;
	  incr markPass;
	  Queue.clear queue;
      NSet.iter fn !nodes;
	  (* mark *)
	  while not (Queue.is_empty queue) do
		let nde = Queue.pop queue; in
		  match nde.status with
			| Sat | Unsat -> () 
			| Unknwn (fs,parent,dependents,_,marks,kind)
			  ->
				let changed = 
				  match kind with
					| DOr (_,children) ->
						let rec markFn changed = function
						  | [] -> changed
						  | h::t ->
							  match h.status with
								| Unknwn(_,_,_,_,mrk,_) ->
									markFn ((markOr fs marks mrk) || changed) t
								| Sat ->
									let chng = ref false in
									  for i = 0 to (!hposUN - !lposUN) do
										if marks.(i) <> !markPass then begin
											marks.(i) <- !markPass;
											chng := true
										  end
									  done;
									  changed || !chng
								| Unsat -> markFn changed t
								| _ -> print_endline "Error: undef at mark time"; false
						in
						  markFn false !children
					| DState child ->
						markAnd fs marks child
				in
				  if changed then begin
					  NSet.iter fn !dependents;
					  List.iter fn parent
					end
			| Undef (_,parent,dependents,mrk,kind) ->
				if !mrk <> !markPass then begin
					mrk := !markPass;
					NSet.iter fn !dependents;
					List.iter fn parent;
				  end
				
	  done;
	  (* sweep *)
	  let removeFailed fs nde =
		match nde.status with
		  | Unknwn (fs,_,_,_,mrks,kind) ->
			  let unsat = checkMark fs mrks || 
				match kind with
				  | DOr (_,children) ->
					  let rec fn = function
						| [] -> true
						| h::t ->
							if h.status = Unsat then fn t
							else false
					  in
						fn !children
				  | DState child ->
					  child.status = Unsat
			  in
				if unsat then begin
					nde.status <- Unsat;
					same := false
				  end
		  | _ -> ()
	  in
		GHt.iter removeFailed grph;
	  done;
				tEvent := !tEvent +. (Unix.gettimeofday() -. start)
					
					
(** The result type for the two following functions.
*)
type result = RSat | RUnsat | RPrs

(** Determines the status of an or-node.
    @param crun The current value of cacherun.
    @param nde A node.
    @param fs The set of formulae belonging to nde.
    @param ts The time stamp of nde.
    @param pfopt The principal formula of nde if it is an eventuality (else -1).
    @param allUnsat True iff all children examined so far were unsatisfiable.
    @param prs The (preliminary) Prs of nde.
    It is only used if allUnsat is false.
    @param nel A list of pairs (c, evopt) where c is a child of nde and
    evopt is the successor eventuality of pfopt in chld
    if pf is an eventuality and chld does not fulfil it directly (else -1).
    @return RSat if the node is satisfiable;
    RUnsat if the node is unsatisfiable; and
    RPrs prs if the status of the node is unknown
    and the Prs of the node is prs.
 *)
let rec intern_detStatusOr nde allUnsat nel =
  match nel with
  | chldi::tl -> begin
      match chldi.status with
      | Unknwn _
      | Undef _ ->
          intern_detStatusOr nde false tl
      | Unsat -> intern_detStatusOr nde allUnsat tl
      | Sat -> RSat
  end
  | [] ->
      if allUnsat then RUnsat 
      else RPrs

let detStatusOr nde nel =
  intern_detStatusOr nde true nel

(** Determines the status of a state.
    @param crun The current value of cacherun.
    @param nde A node.
    @param ts The time stamp of nde.
    @param allSat True iff all children examined so far were satisfiable.
    @param prs The (preliminary) Prs of nde.
    @param nel A list of pairs (n, ev) where n is a child of nde
    and ev is the corresponding <a>-formulae if it is an eventuality (else -1).
    @return RSat if the node is satisfiable;
    RUnsat if the node is unsatisfiable; and
    RPrs prs if the status of the node is unknown
    and the Prs of the node is prs.
 *)
let rec intern_detStatusState nde child =
  match child.status with
    | Unknwn _
    | Undef _ -> RPrs
    | Unsat -> RUnsat
    | Sat -> RSat

let detStatusState nde child =
  intern_detStatusState nde child



(** Propagates the status of nodes in a graph.
    @param queue A list of nodes in the graph which must be updated.
    @raise Queue.Empty if queue is empty.
 *)
let rec propagate queue =
  let nde = Queue.take queue in
  match nde.status with
  | Unknwn (fs,prntl, bwupdr, ts, mrks, kind) ->
      let res =
        match kind with
        | DState child -> detStatusState nde child
        | DOr (pf, nelr) ->
            let rsts = detStatusOr nde !nelr in
            let notExpandOr =
              match rsts with
                | RUnsat -> false
                | RPrs -> false
                | _ -> true
            in
              if notExpandOr then rsts
              else
                let fseti = copyBS fs in
                remBS fseti pf;
                let cntri = insertFormulaNS fseti !arrayDest2.(pf) in
                if not cntri then ignore (isSat_create [nde] fseti ) else ();
                detStatusOr nde !nelr
      in
      let prop =
        match res with
        | RPrs -> false
        | RUnsat ->
            nde.status <- Unsat;
            true
        | RSat ->
            nde.status <- Sat;
            true
      in
      if prop then begin
        assert (prntl <> []);
        Queue.add (List.hd prntl) queue;
        let bwupd = !bwupdr in
        if not (NSet.is_empty bwupd) then
          NSet.iter (fun x -> Queue.add x queue) bwupd
        else ()
      end
      else ();
      propagate queue
  | _ -> propagate queue (* Must be Sat or Unsat *)


(** Sets the initial status of a node and propagates accordingly.
    @param nde A node whose current status is undefined.
    @param prntl A singleton list containing the parent of nde.
    If nde is the root node then prntl is empty.
    @param bwupdr All relevant nodes which point to nde via bw- or upd-edges.
    @param sts The initial status of nde.
    @return True iff the initial formula is satisfiable.
 *)
and contSetStatus nde prntl bwupdr sts =
  nde.status <- sts;
  if prntl <> [] then
    let () =
      match sts with
      | Sat
      | Unsat ->
          let bwupd = !bwupdr in
          if not (NSet.is_empty bwupd) then
            let queue = Queue.create () in
            NSet.iter (fun x -> Queue.add x queue) bwupd;
            try
              propagate queue
            with Queue.Empty -> ()
          else ()
      | _ -> ()
    in
    isSat_continue (List.hd prntl) nde
  else sts <> Unsat

(** Sets up information about the current child of an or-node
    and invokes the creation of the child
    (unless there is an immediate contradiction).
    @param nde The or-node which is partly processed.
    @param fs The set of formulae belonging to nde.
    @param rbfs The set of [*]-formulae which have already been expanded in nde.
    @param prntl A singleton list containing the parent of nde.
    If nde is the root node then prntl is empty.
    @param bwupdr All relevant nodes which point to nde via bw- or upd-edges.
    @param pf The principal formula of nde.
    @param nelr A list of pairs (c, evopt) where c is a child of nde and
    evopt is the successor eventuality of pfopt in chld
    if pf is an eventuality and chld does not fulfil it directly (else -1).
    @param nor The number of remaining decompositions
    of the principal formula of nde which still have to be processed.
    @return True iff the initial formula is satisfiable.
 *)
and contOr nde fs prntl bwupdr pf nelr nor =
  match !nor with
  | 0 -> begin
      let res = detStatusOr nde !nelr in
      match res with
      | RPrs ->
          let sts =
            incr postfixcount;
            Unknwn (fs, prntl, bwupdr, !postfixcount, mkArr (), DOr (pf, nelr))
          in
          contSetStatus nde prntl bwupdr sts
      | RUnsat -> contSetStatus nde prntl bwupdr Unsat
      | RSat -> assert (1 = 0); contSetStatus nde prntl bwupdr Sat
  end
  | n ->
      decr nor;
      let fseti = copyBS fs in
      remBS fseti pf;
      let fi = if n = 2 then !arrayDest1.(pf) else !arrayDest2.(pf) in
      let cntri = insertFormulaNS fseti fi in
      if not cntri then isSat_create [nde] fseti
      else isSat_continue nde unsatNode

(** Sets up information about the current child of a state
    and invokes the creation of the child
    (unless there is an immediate contradiction).
    @param nde The state which is partly processed.
    @param fs The set of formulae belonging to nde.
    @param prntl A singleton list containing the parent of nde.
    If nde is the root node then prntl is empty.
    @param bwupdr All relevant nodes which point to nde via bw- or upd-edges.
    @param nelr A list of pairs (c, evopt) where c is a child of nde an
    and evopt is the corresponding <a>-formulae if it is an eventuality (else -1).
    @param flr The EX-formulae which still have to be processed.
    @return True iff the initial formula is satisfiable.
 *)
and contState nde fs prntl bwupdr flr =
  let fseti = makeBS () in
  let rec f bs = function
	| [] -> false
	| h::t -> 
		if insertFormulaNS bs !arrayDest1.(h) then
		  true
		else f bs t
  in
  let cntri = f fseti flr
  in
    if not cntri then isSat_create [nde] fseti
    else contSetStatus nde prntl bwupdr Unsat

(** Gets a node which has been partly processed and a child of the node
    which has been fully processed and updates the node status accordingly.
    It then starts processing the next child or
    - if there is none or the status of the node is already determined -
    sets the status of the node and continues processing its parent.
    @param nde The node which is partly processed.
    @param chld The child which just has been finished processing.
    @return True iff the initial formula is satisfiable.
 *)
and isSat_continue nde chld =
(*
  printGraph ("continue graph: " ^ (exportN nde) ^ " " ^ (exportN chld)) grph;
 *)
  match nde.status with
  | Undef (fs, prntl, bwupdr, mrks, kind) -> begin
      match kind with
      | UOr (pf, nelr, nor) -> begin
          match chld.status with
          | Unknwn _
          | Undef _ ->
              nelr := chld::!nelr;
              contOr nde fs prntl bwupdr pf nelr nor
          | Unsat -> contOr nde fs prntl bwupdr pf nelr nor
          | Sat -> contSetStatus nde prntl bwupdr Sat
      end
      | UState child -> begin
			match chld.status with
			  | Unknwn _ | Undef _ ->
				  incr postfixcount;
				  let sts = Unknwn (fs, prntl, bwupdr, !postfixcount, mkArr (), DState chld) in
					contSetStatus nde prntl bwupdr sts
			  | Unsat -> contSetStatus nde prntl bwupdr Unsat
			  | Sat -> contSetStatus nde prntl bwupdr Sat
		end
  end
  | Unknwn (_, _, _, _, _, DOr (_, nelr)) ->
      nelr := chld::!nelr;
      false
  | _ -> raise (P.PLTLException "This should not happen. It is a bug in \"isSat_continue\"!")

(** Creates a new node if it does not already exist
    and initialises the creation of its first child
    (unless there is an immediate contradiction).
    @param prntl A singleton list containing the parent of the new node
    Iff the new node is the root node then the list is empty.
    @param fset The bitset of formulae of the new node.
    It is assumed that only this invocation can modify it.
    @param rbfs The set of [*]-formulae which have already been expanded in nde.
    It is assumed that only this invocation can modify it.
    @return True iff the initial formula is satisfiable.
 *)
and isSat_create prntl fset  =
(*
  printGraph "create graph: " grph;
 *)
  match memGraph grph fset with
  | None ->
      let pf = getPFinclEX fset in
      if pf >= 0 then
        match !arrayType.(pf) with
        | 4 (* X *) ->
            let flr = mkEXList fset in
            let bwupdr = ref NSet.empty in
            let sts = Undef (fset, prntl, bwupdr, ref 0, UState unsatNode) in
            let nde = { id = getNewId (); status = sts } in
              addGraph grph fset nde;
			  if satAny fset then goodEdges := NSet.add nde !goodEdges;
              contState nde fset prntl bwupdr flr
        | _ -> (* Must be OR, U *)
            let f1 = !arrayDest1.(pf) in
            if
              containsFormula fset f1
			|| (!arrayType.(pf) = 6 (* OR *) && containsFormula fset !arrayDest2.(pf))
            then begin
				remBS fset pf;
				isSat_create prntl fset
            end
            else
              let nelr = ref [] in
              let nor = ref 2 in
              let bwupdr = ref NSet.empty in
              let sts = Undef (fset, prntl, bwupdr, ref 0, UOr (pf, nelr, nor)) in
              let nde = { id = getNewId (); status = sts } in
              addGraph grph fset nde;
				if satAny fset then goodEdges := NSet.add nde !goodEdges;
              contOr nde fset prntl bwupdr pf nelr nor
      else
		let cntr = insertFormulaNS fset !fxtrue in
		  if cntr then false
		  else isSat_create prntl fset
  | Some nde ->
      let prnt = List.hd prntl in
      let _ =
        match nde.status with
        | Undef (_, _, bwupdr, _, _)
        | Unknwn (_, _, bwupdr, _, _, _) -> bwupdr := NSet.add prnt !bwupdr;
        | _ -> ()
      in
      isSat_continue prnt nde


(** An on-the-fly graph-tableau-based decision procedure for PLTL-satisfiability
    which blocks on all nodes,
    does not focus on a single formula, does not use annotated sets,
    and uses variables to track unfulfilled eventualties on-the-fly.
    It is optimal, that is EXPTIME.
    @param verbose An optional switch which determines
    whether the procedure shall print some information on the standard output.
    The default is false.
    @param f The initial formula that is to be tested for satisfiability.
    @return True if f is satisfiable, false otherwise.
 *)
let isSat ?(verbose = 0) ?(print = None) f = 
  let start = if verbose >0 then Unix.gettimeofday () else 0. in
  let (nnf, fi) = ppFormula f rankingNoAnd notyNoAnd in
  let fset = makeBS () in
  let cntr = insertFormulaNS fset fi in
  emptyGraph grph;
  goodEdges := NSet.empty;
  markPass := 0;
  let sat = 
    if cntr then false
    else
	  let ret = isSat_create [] fset in
		if not ret then false
		else begin
			findSatisfyingRegion goodEdges;
			(* Is the root marked?*)
			match memGraph grph fset with
			  | None -> print_endline "Error! Root not in graph?"; false
			  | Some nde ->
				  (match print with
					 | Some filename ->
						 let oc = open_out filename in
						   if verbose = 2 then
							 printGraph grph oc
						   else
							 begin
							   let andor = collapse grph !goodEdges in
								 if verbose = 3 then
								 printAndOr andor grph nde oc
								 else if verbose = 4 then
								   printTraces andor nde oc
								 else
								   let root = getRoot nde in
								   let model = emersonUnwind andor root in
									 if verbose = 6 then debugoc := Some oc
									 else debugoc := None;
									 printModel andor model root oc
							 end;
						   close_out oc
					 | None -> ());
				  match nde.status with
					| Unsat -> false
					| Sat -> true
					| Unknwn (_,_,_,_,mrks,_) -> true
					| _ -> print_endline "ERROR"; false
		  end
  in
(*
  printGraph "final graph: " grph;
 *)
  if verbose >0 then begin
    let stop = Unix.gettimeofday () in
    print_newline ();
    print_endline ("Input formula: " ^ (P.exportFormula f));
    print_endline ("Size: " ^ (string_of_int (P.sizeFormula f)));
    print_endline ("Negation Normal Form: " ^ (P.exportFormula nnf));
    print_endline ("Size: " ^ (string_of_int (P.sizeFormula nnf)));
    print_endline ("Result: Formula is " ^ (if not sat then "not " else "") ^ "satisfiable.");
    print_endline ("Time: " ^ (string_of_float (stop -. start)));
	print_endline ("Time checking eventualities: " ^ (string_of_float !tEvent));
    print_endline ("Generated nodes: " ^ (string_of_int (sizeGraph grph)));
    print_newline ();
  end else ();
  sat
