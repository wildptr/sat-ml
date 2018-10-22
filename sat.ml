open Term

let () =
  let lexbuf = Lexing.from_channel stdin in
  let term = SatParser.top SatLexer.lex lexbuf in
  Format.printf "input: %a@." pp_term term;
  Format.printf "canon: %a@." pp_term (canon term);
  let cnf = cnf_of_term term in
  Format.printf "CNF: %a@." pp_term (term_of_cnf cnf);
  let instance = Instance.instance_of_cnf cnf in
  let sat = Solver.solve instance in
  print_endline (if sat then "sat" else "unsat")
