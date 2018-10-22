type term =
  | Const of bool
  | Var of string
  | Not of term
  | And of term * term
  | Or of term * term
  | Imp of term * term
  | Equiv of term * term

let rec canon = function

  | Not (Const b) -> Const (not b)
  | Not t -> Not (canon t)

  | And (Const b1, Const b2) -> Const (b1 && b2)
  | And (Const true, t) -> canon t
  | And (Const false, t) -> Const false
  | And (t, Const true) -> canon t
  | And (t, Const false) -> Const false
  | And (t1, t2) ->
    let t1' = canon t1 in
    let t2' = canon t2 in
    And (t1', t2')

  | Or (Const b1, Const b2) -> Const (b1 || b2)
  | Or (Const true, t) -> Const true
  | Or (Const false, t) -> canon t
  | Or (t, Const true) -> Const true
  | Or (t, Const false) -> canon t
  | Or (t1, t2) ->
    let t1' = canon t1 in
    let t2' = canon t2 in
    Or (t1', t2')

  | Imp (Const b1, Const b2) -> Const (not b1 || b2)
  | Imp (Const false, t) -> Const true
  | Imp (Const true, t) -> canon t
  | Imp (t, Const false) -> canon t
  | Imp (t, Const true) -> Const true
  | Imp (t1, t2) ->
    let t1' = canon t1 in
    let t2' = canon t2 in
    Or (Not t1', t2')

  | Equiv (Const b1, Const b2) -> Const (b1 = b2)
  | Equiv (Const true, t) -> canon t
  | Equiv (Const false, t) -> Not (canon t)
  | Equiv (t, Const true) -> canon t
  | Equiv (t, Const false) -> Not (canon t)
  | Equiv (t1, t2) ->
    let t1' = canon t1 in
    let t2' = canon t2 in
    Or (And (t1', t2'), And (Not t1', Not t2'))

  | t -> t

type lit = string * bool

let negate (name, pos) = (name, not pos)

let cnf_of_term t =
  match canon t with
  | Const true -> []
  | Const false -> [[]]
  | t ->
    let i = ref 0 in
    let fresh_name () =
      let name = Printf.sprintf "#%d" !i in
      incr i;
      name
    in
    let rec cnf_and t delta =
      match t with
      | Const _ -> assert false
      | Var x -> ((x, true), delta)
      | Not t' ->
        let l, delta' = cnf_and t' delta in
        (negate l, delta')
      | And (t1, t2) ->
        let l1, delta1 = cnf_and t1 delta in
        let l2, delta2 = cnf_and t2 delta1 in
        let p = fresh_name () in
        ((p, true), [(p, false); l1] :: [(p, false); l2] :: [(p, true); negate l1; negate l2] :: delta2)
      | Or (t1, t2) ->
        let l1, delta1 = cnf_and t1 delta in
        let l2, delta2 = cnf_and t2 delta1 in
        let p = fresh_name () in
        ((p, true), [(p, true); negate l1] :: [(p, true); negate l2] :: [(p, false); l1; l2] :: delta2)
      | Imp _ -> assert false
      | Equiv _ -> assert false
    in
    let l, delta = cnf_and t [] in
    [l] :: delta

let term_of_lit = function
  | (x, true) -> Var x
  | (x, false) -> Not (Var x)

let rec term_of_clause = function
  | [] -> Const false
  | [l] -> term_of_lit l
  | l :: cls -> Or (term_of_lit l, term_of_clause cls)

let rec term_of_cnf = function
  | [] -> Const true
  | [cls] -> term_of_clause cls
  | cls :: cnf -> And (term_of_clause cls, term_of_cnf cnf)

(* pretty printing *)

open Format

let rec pp_term_pri pri f = function
  | Const b -> pp_print_string f (if b then "⊤" else "⊥")
  | Var x -> pp_print_string f x
  | Not t -> fprintf f "¬%a" (pp_term_pri 4) t
  | And (t1, t2) ->
    if pri > 3 then
      fprintf f "(%a ∧ %a)" (pp_term_pri 3) t1 (pp_term_pri 3) t2
    else
      fprintf f "%a ∧ %a" (pp_term_pri 3) t1 (pp_term_pri 3) t2
  | Or (t1, t2) ->
    if pri > 2 then
      fprintf f "(%a ∨ %a)" (pp_term_pri 2) t1 (pp_term_pri 2) t2
    else
      fprintf f "%a ∨ %a" (pp_term_pri 2) t1 (pp_term_pri 2) t2
  | Imp (t1, t2) ->
    if pri > 1 then
      fprintf f "(%a → %a)" (pp_term_pri 1) t1 (pp_term_pri 1) t2
    else
      fprintf f "%a → %a" (pp_term_pri 1) t1 (pp_term_pri 1) t2
  | Equiv (t1, t2) ->
    if pri > 0 then
      fprintf f "(%a ↔ %a)" (pp_term_pri 0) t1 (pp_term_pri 0) t2
    else
      fprintf f "%a ↔ %a" (pp_term_pri 0) t1 (pp_term_pri 0) t2

let pp_term f = pp_term_pri 0 f
