open ExtLib
open Term

type lit_i = int * bool

type clause = lit_i list

type instance = {
  clauses : clause array;
  nvar : int;
  name_table : string array
}

module M = Map.Make(String)

let convert_lit name_map (name, pos) =
  let id = M.find name name_map in
  (id, pos)

let rec convert_clause name_map = function
  | [] -> []
  | l :: cls ->
    convert_lit name_map l :: convert_clause name_map cls

let build_nametab cnf =
  let m = ref M.empty in
  let see_lit (name, _) =
    if not (M.mem name !m) then begin
      let id = M.cardinal !m in
      m := M.add name id !m
    end
  in
  let rec walk_clause = List.iter see_lit in
  let rec walk_cnf = List.iter walk_clause in
  walk_cnf cnf;
  !m

let instance_of_cnf cnf =
  let name_map = build_nametab cnf in
  let clauses = cnf |> List.map (convert_clause name_map) |> Array.of_list in
  let nvar = M.cardinal name_map in
  let name_table = Array.make nvar "" in
  M.iter (fun name id -> name_table.(id) <- name) name_map;
  { clauses; nvar; name_table }
