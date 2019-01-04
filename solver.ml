open ExtLib
open Instance
open Util

type valuation = bool option array

let val_of_lit valn (id, pos) =
  match valn.(id) with
  | Some v -> Some (v = pos)
  | None -> None

(* a clause is unsatisfiable under given valuation *)
let rec all_false valn cls =
  List.for_all (fun l -> val_of_lit valn l = Some false) cls

type clause_status =
  | Unit of lit_i
  | Satisfied
  | Unsat
  | Other

let rec clause_status valn = function
  | [] -> Unsat
  | l :: cls ->
    begin match val_of_lit valn l with
      | Some true -> Satisfied
      | Some false -> clause_status valn cls
      | None -> if all_false valn cls then Unit l else Other
    end

module Int = struct
  type t = int
  let compare = compare
end

module S = Set.Make(Int)

type decision_level = {
  guess : (int * bool) option; (* None for top-level *)
  mutable inferred_vars : int list;
  mutable active_clauses : S.t
}

type solver = {
  clauses : clause DynArray.t;
  valn : valuation;
  pos_set : S.t array;
  neg_set : S.t array;
  name_table : string array;
  mutable trail : decision_level list
}

let pp_lit name_table f (i, pos) =
  let name = name_table.(i) in
  if not pos then Format.pp_print_string f "¬";
  Format.pp_print_string f name

let rec pp_clause name_table f = function
  | [] -> Format.pp_print_string f "⊥"
  | [l] -> pp_lit name_table f l
  | l :: cls ->
    Format.fprintf f "%a ∨ %a" (pp_lit name_table) l (pp_clause name_table) cls

let pp_valuation name_table f valn =
  Format.pp_print_char f '{';
  valn |> Array.iteri begin fun i v_opt ->
    match v_opt with
    | Some v ->
      let name = name_table.(i) in
      if v then
        Format.fprintf f " %s" name
      else
        Format.fprintf f " ¬%s" name
    | None -> ()
  end;
  Format.pp_print_string f " }"

let add_to_watch_sets s cls_id cls =
  let see_lit cls_id (i, pos) =
    let watch_set = if pos then s.pos_set else s.neg_set in
    watch_set.(i) <- S.add cls_id watch_set.(i)
  in
  List.iter (see_lit cls_id) cls

let add_clause s cls =
  Format.printf "add clause: %a@." (pp_clause s.name_table) cls;
  let cls_id = DynArray.length s.clauses in
  DynArray.add s.clauses cls;
  add_to_watch_sets s cls_id cls;
  s.trail |> List.iter begin fun dec ->
    dec.active_clauses <- S.add cls_id dec.active_clauses;
  end;
  cls_id

let add_conflict_clause s =
  let guesses = List.filter_map (fun { guess; _ } -> guess) s.trail in
  (* if assumption "a ∧ ¬b" is contradictory, then we have "¬a ∨ b" *)
  let cls = List.map (fun (i, pos) -> (i, not pos)) guesses in
  (add_clause s cls, cls)

let get_clause s cls_id =
  DynArray.get s.clauses cls_id

let cancel_val s i =
  Format.printf "unset %s@." s.name_table.(i);
  s.valn.(i) <- None

let print_valn s =
  Format.printf "%a@." (pp_valuation s.name_table) s.valn

exception Exn_Conflict
exception Bug

type infer_result =
  | No_Conflict
  | Conflict

(* called after adding conflict clause *)
let rec backtrack s confl_cls =
  Format.printf "backtrack!@.";
  assert (s.trail <> []);
  let head = List.hd s.trail in
  assert (head.guess <> None);
  let trail' = List.tl s.trail in
  assert (trail' <> []);
  List.iter (cancel_val s) head.inferred_vars;
  cancel_val s (fst (Option.get head.guess));
  if clause_status s.valn confl_cls = Unsat then
    backtrack s confl_cls
  else
    s.trail <- trail'

let all_sat s =
  s.clauses |> DynArray.to_list |> List.for_all begin fun cls ->
    match clause_status s.valn cls with Satisfied -> true | _ -> false
  end

let no_unit_clauses s =
  s.clauses |> DynArray.to_list |> List.for_all begin fun cls ->
    match clause_status s.valn cls with Unit _ -> false | _ -> true
  end

(* after calling infer there should be no variable setting whose value will
   immediately cause a clause to be unsat *)
let infer s =
  let head = List.hd s.trail in
  let q = Queue.create () in (* literals in unit clauses *)
  let sat = Queue.create () in (* satisfied clauses *)
  let rec loop w =
    if S.is_empty w then No_Conflict
    else begin
      assert (s.trail <> []);
      let w' = ref S.empty in
      w |> S.iter begin fun cls_id ->
        let cls = get_clause s cls_id in
        match clause_status s.valn cls with
        | Unit (i, pos as l) ->
          (* Format.printf "under %a clause (%a) is unit clause of %a@."
             (pp_valuation s.name_table) s.valn
             (pp_clause s.name_table) cls
             (pp_lit s.name_table) l; *)
          assert (s.valn.(i) = None);
          Queue.push l q;
          Queue.push cls_id sat;
          let watch_set = if pos then s.neg_set else s.pos_set in
          w' := S.union watch_set.(i) !w'
        | Satisfied -> Queue.push cls_id sat
        (* Format.printf "clause (%a) is satisfied@." (pp_clause s.name_table) cls *)
        | Unsat -> raise Exn_Conflict
        | Other -> ()
      end;
      head.active_clauses <-
        S.diff head.active_clauses (sat |> Queue.to_seq |> S.of_seq);
      if Queue.is_empty q then No_Conflict
      else begin
        while not (Queue.is_empty q) do
          let (i, pos) = Queue.pop q in
          Format.printf "setting %s to %b (infer)@."
            s.name_table.(i) pos;
          assert (s.valn.(i) <> Some pos);
          if s.valn.(i) <> None then raise Exn_Conflict;
          s.valn.(i) <- Some pos;
          head.inferred_vars <- i :: head.inferred_vars;
          print_valn s
        done;
        loop !w'
      end
    end
  in
  try loop head.active_clauses with Exn_Conflict -> Conflict

let decide s =
  let n = Array.length s.valn in
  let rec loop i =
    if i = n then None
    else if s.valn.(i) = None then Some (i, true)
    else loop (i+1)
  in
  loop 0

let solve instance =
  let { nvar; clauses; name_table } = instance in
  let name_table = name_table in
  (* for i=0 to nvar-1 do
    Printf.printf "%s occurs in:" name_table.(i);
    pos_set.(i) |> S.iter begin fun cls_id ->
      Format.printf " (%a)" (pp_clause name_table) clauses.(cls_id)
    end;
    Format.printf "@.";
    Printf.printf "¬%s occurs in:" name_table.(i);
    neg_set.(i) |> S.iter begin fun cls_id ->
      Format.printf " (%a)" (pp_clause name_table) clauses.(cls_id)
    end;
    Format.printf "@."
  done; *)
  let valn = Array.make nvar None in
  let top = {
    guess = None;
    inferred_vars = [];
    active_clauses = S.of_list (range 0 (Array.length clauses))
  } in
  let solver = {
    clauses = DynArray.of_array clauses;
    valn;
    pos_set = Array.make nvar S.empty;
    neg_set = Array.make nvar S.empty;
    name_table;
    trail = [top]
  } in
  clauses |> Array.iteri (add_to_watch_sets solver);
  let rec loop () =
    match infer solver with
    | Conflict ->
      print_endline "conflict!";
      let confl_cls_id, confl_cls = add_conflict_clause solver in
      if confl_cls = [] then false
      else begin
        backtrack solver confl_cls;
        (*(List.hd solver.trail).active_clauses <- S.singleton confl_cls_id;*)
        loop ()
      end
    | No_Conflict ->
      assert (no_unit_clauses solver);
      begin match decide solver with
        | None -> assert (all_sat solver); true
        | Some (i, v) as guess ->
          Format.printf "setting %s to %b (guess)@." name_table.(i) v;
          valn.(i) <- Some v;
          print_valn solver;
          let dec = {
            guess;
            inferred_vars = [];
            active_clauses = (List.hd solver.trail).active_clauses
          } in
          solver.trail <- dec :: solver.trail;
          loop ()
      end
  in
  loop ()
