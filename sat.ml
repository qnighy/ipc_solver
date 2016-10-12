type sat_env = {
  mutable maxvar: int;
  mutable clauses: int array list
}

let new_sat_env () = {
  maxvar = 0;
  clauses = []
}

let fresh_var sat_env =
  let varid = sat_env.maxvar + 1 in
  sat_env.maxvar <- varid;
  varid

let add_clause sat_env c =
  sat_env.clauses <- c :: sat_env.clauses

let output_clauses sat_env f =
  Printf.fprintf f "p cnf %d %d\n"
    sat_env.maxvar (List.length sat_env.clauses);
  List.iter (fun clause ->
    Array.iter (fun literal ->
      Printf.fprintf f "%d " literal
    ) clause;
    Printf.fprintf f "0\n"
  ) sat_env.clauses

type sat_result =
    Satisfiable of bool array
  | Unsatisfiable
  | NotDetermined

let read_sat_output sat_env b =
  let status = Scanf.bscanf b "%s " (fun s -> s) in
  if status = "SAT" then begin
    let result = Array.make (sat_env.maxvar + 1) false in
    for i = 1 to sat_env.maxvar do
      result.(i) <- Scanf.bscanf b "%d " (fun i -> i) > 0
    done;
    Satisfiable result
  end else if status = "UNSAT" then
    Unsatisfiable
  else
    NotDetermined

let invoke_minisat sat_env =
  let (minisat_in_path, minisat_in) =
    Filename.open_temp_file "ipc_kripke" ".cnf" in
  output_clauses sat_env minisat_in;
  close_out minisat_in;
  let (minisat_out_path, minisat_out) =
    Filename.open_temp_file "ipc_kripke" ".out" in
  close_out minisat_out;
  ignore (Sys.command ("minisat -verb=0 -cpu-lim=1 -mem-lim=256 " ^ minisat_in_path ^ " " ^ minisat_out_path ^ ">/dev/null 2>/dev/null"));
  let minisat_out = open_in minisat_out_path in
  let minisat_out_buf = Scanf.Scanning.from_channel minisat_out in
  let minisat_result = read_sat_output sat_env minisat_out_buf in
  Sys.remove minisat_in_path;
  Sys.remove minisat_out_path;
  minisat_result
