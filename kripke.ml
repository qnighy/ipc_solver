open Term

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

type kripke_env = {
  n : int;
  accessibility : int array array
}

let new_kripke_env sat_env n =
  let accessibility = Array.init n (fun _ ->
    Array.init n (fun _ -> fresh_var sat_env)) in
  (* reflexivity *)
  for i = 0 to (n-1) do
    add_clause sat_env [| accessibility.(i).(i) |]
  done;
  (* transitivity *)
  for i = 0 to (n-1) do
    for j = 0 to (n-1) do
      for k = 0 to (n-1) do
        add_clause sat_env [|
          accessibility.(i).(k);
          -accessibility.(i).(j);
          -accessibility.(j).(k)
        |]
      done
    done
  done;
  (* Wi |=> Wj implies i <= j *)
  for i = 0 to (n-1) do
    for j = 0 to (n-1) do
      if i > j then
        add_clause sat_env [| -accessibility.(i).(j) |]
    done
  done;
  {
    n = n;
    accessibility = accessibility
  }

let rec make_clauses sat_env kripke_env term_memo t =
  try
    Hashtbl.find term_memo t
  with Not_found ->
    let varids = Array.init kripke_env.n (fun _ -> fresh_var sat_env) in
    Hashtbl.add term_memo t varids;
    begin match t with
    | PVar _ ->
        (* herediety *)
        for i = 0 to (kripke_env.n-1) do
          for j = 0 to (kripke_env.n-1) do
            add_clause sat_env [|
              -varids.(i); varids.(j); -kripke_env.accessibility.(i).(j) |];
          done
        done
    | PArrow (t0, t1) ->
        let varids0 = make_clauses sat_env kripke_env term_memo t0 in
        let varids1 = make_clauses sat_env kripke_env term_memo t1 in
        let varids2 = Array.init kripke_env.n (fun _ -> fresh_var sat_env) in
        (* varids2 = not varids0 or varids1 *)
        for i = 0 to (kripke_env.n-1) do
          add_clause sat_env [| varids2.(i); varids0.(i) |];
          add_clause sat_env [| varids2.(i); -varids1.(i) |];
          add_clause sat_env [| -varids2.(i); -varids0.(i); varids1.(i) |]
        done;
        (* varids = square varids2 *)
        for i = 0 to (kripke_env.n-1) do
          let varids3 =
            Array.init kripke_env.n (fun _ -> fresh_var sat_env) in
          for j = 0 to (kripke_env.n-1) do
            add_clause sat_env [|
              varids3.(j); -varids2.(j) |];
            add_clause sat_env [|
              varids3.(j); kripke_env.accessibility.(i).(j) |];
            add_clause sat_env [|
              -varids3.(j); varids2.(j); -kripke_env.accessibility.(i).(j) |];
          done;
          add_clause sat_env (Array.init (kripke_env.n + 1) (fun j ->
            if j == kripke_env.n then
              varids.(i)
            else
              -varids3.(j)
          ));
          for j = 0 to (kripke_env.n-1) do
            add_clause sat_env [|
              -varids.(i); varids3.(j) |];
          done
        done
    | POr (t0, t1) ->
        let varids0 = make_clauses sat_env kripke_env term_memo t0 in
        let varids1 = make_clauses sat_env kripke_env term_memo t1 in
        for i = 0 to (kripke_env.n-1) do
          add_clause sat_env [| varids.(i); -varids0.(i) |];
          add_clause sat_env [| varids.(i); -varids1.(i) |];
          add_clause sat_env [| -varids.(i); varids0.(i); varids1.(i) |]
        done
    | PAnd (t0, t1) ->
        let varids0 = make_clauses sat_env kripke_env term_memo t0 in
        let varids1 = make_clauses sat_env kripke_env term_memo t1 in
        for i = 0 to (kripke_env.n-1) do
          add_clause sat_env [| -varids.(i); varids0.(i) |];
          add_clause sat_env [| -varids.(i); varids1.(i) |];
          add_clause sat_env [| varids.(i); -varids0.(i); -varids1.(i) |]
        done
    | PTop ->
        for i = 0 to (kripke_env.n-1) do
          add_clause sat_env [| varids.(i) |]
        done
    | PBot ->
        for i = 0 to (kripke_env.n-1) do
          add_clause sat_env [| -varids.(i) |]
        done
    end;
    varids

type kripke_result =
    KripkeRefutable of int * bool array array * (pterm, bool array) Hashtbl.t
  | KripkeIrrefutable
  | KripkeNotDetermined

let solve_n penv n t =
  let sat_env = new_sat_env () in
  let kripke_env = new_kripke_env sat_env n in
  let term_memo = Hashtbl.create 13 in
  let varids = make_clauses sat_env kripke_env term_memo t in
  add_clause sat_env [| -varids.(0) |];
  let minisat_result = invoke_minisat sat_env in
  begin match minisat_result with
  | Satisfiable asgn ->
      (* Printf.eprintf "Satisfiable\n"; *)
      (* for x = 1 to sat_env.maxvar do
        if asgn.(x) then
          Printf.eprintf "%d\n" x
        else
          Printf.eprintf "%d\n" (-x)
      done; *)
      (* Hashtbl.iter (fun t0 varids0 ->
        Format.eprintf "%a = @." (pp_print_pterm penv 5) t0;
        Printf.eprintf "   [";
        Array.iter (fun x ->
          Printf.eprintf "%d, " (if asgn.(x) then 1 else 0)
        ) varids0;
        Printf.eprintf "]\n"
      ) term_memo; *)
      let accessibility = Array.map (fun row ->
        Array.map (fun v -> asgn.(v)) row
      ) kripke_env.accessibility in
      let term_asgn = Hashtbl.create 47 in
      Hashtbl.iter (fun t0 varids0 ->
        Hashtbl.add term_asgn t0 (Array.map (fun x -> asgn.(x)) varids0)
      ) term_memo;
      KripkeRefutable (n, accessibility, term_asgn)
  | Unsatisfiable ->
      (* Printf.eprintf "Unsatisfiable\n"; *)
      KripkeIrrefutable
  | NotDetermined ->
      (* Printf.eprintf "Not determined\n"; *)
      KripkeNotDetermined
  end

let solve penv t =
  let ret = ref KripkeIrrefutable in
  for n = 2 to 4 do
    if !ret = KripkeIrrefutable then
      ret := solve_n penv n t
  done;
  !ret
