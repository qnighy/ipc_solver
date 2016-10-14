open Term

type kripke_env = {
  n : int;
  accessibility : int array array
}

let new_kripke_env sat_env n =
  let accessibility = Array.init n (fun _ ->
    Array.init n (fun _ -> Sat.fresh_var sat_env)) in
  (* reflexivity *)
  for i = 0 to (n-1) do
    Sat.add_clause sat_env [| accessibility.(i).(i) |]
  done;
  (* transitivity *)
  for i = 0 to (n-1) do
    for j = 0 to (n-1) do
      for k = 0 to (n-1) do
        Sat.add_clause sat_env [|
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
        Sat.add_clause sat_env [| -accessibility.(i).(j) |]
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
    let varids = Array.init kripke_env.n (fun _ -> Sat.fresh_var sat_env) in
    Hashtbl.add term_memo t varids;
    begin match t with
    | PVar _ ->
        (* herediety *)
        for i = 0 to (kripke_env.n-1) do
          for j = 0 to (kripke_env.n-1) do
            Sat.add_clause sat_env [|
              -varids.(i); varids.(j); -kripke_env.accessibility.(i).(j) |];
          done
        done
    | PArrow (t0, t1) ->
        let varids0 = make_clauses sat_env kripke_env term_memo t0 in
        let varids1 = make_clauses sat_env kripke_env term_memo t1 in
        let varids2 =
          Array.init kripke_env.n (fun _ -> Sat.fresh_var sat_env) in
        (* varids2 = not varids0 or varids1 *)
        for i = 0 to (kripke_env.n-1) do
          Sat.add_clause sat_env [| varids2.(i); varids0.(i) |];
          Sat.add_clause sat_env [| varids2.(i); -varids1.(i) |];
          Sat.add_clause sat_env [| -varids2.(i); -varids0.(i); varids1.(i) |]
        done;
        (* varids = square varids2 *)
        for i = 0 to (kripke_env.n-1) do
          let varids3 =
            Array.init kripke_env.n (fun _ -> Sat.fresh_var sat_env) in
          for j = 0 to (kripke_env.n-1) do
            Sat.add_clause sat_env [| varids3.(j); -varids2.(j) |];
            Sat.add_clause sat_env [|
              varids3.(j); kripke_env.accessibility.(i).(j) |];
            Sat.add_clause sat_env [|
              -varids3.(j); varids2.(j); -kripke_env.accessibility.(i).(j) |];
          done;
          Sat.add_clause sat_env (Array.init (kripke_env.n + 1) (fun j ->
            if j == kripke_env.n then
              varids.(i)
            else
              -varids3.(j)
          ));
          for j = 0 to (kripke_env.n-1) do
            Sat.add_clause sat_env [| -varids.(i); varids3.(j) |];
          done
        done
    | POr (t0, t1) ->
        let varids0 = make_clauses sat_env kripke_env term_memo t0 in
        let varids1 = make_clauses sat_env kripke_env term_memo t1 in
        for i = 0 to (kripke_env.n-1) do
          Sat.add_clause sat_env [| varids.(i); -varids0.(i) |];
          Sat.add_clause sat_env [| varids.(i); -varids1.(i) |];
          Sat.add_clause sat_env [| -varids.(i); varids0.(i); varids1.(i) |]
        done
    | PAnd (t0, t1) ->
        let varids0 = make_clauses sat_env kripke_env term_memo t0 in
        let varids1 = make_clauses sat_env kripke_env term_memo t1 in
        for i = 0 to (kripke_env.n-1) do
          Sat.add_clause sat_env [| -varids.(i); varids0.(i) |];
          Sat.add_clause sat_env [| -varids.(i); varids1.(i) |];
          Sat.add_clause sat_env [| varids.(i); -varids0.(i); -varids1.(i) |]
        done
    | PTop ->
        for i = 0 to (kripke_env.n-1) do
          Sat.add_clause sat_env [| varids.(i) |]
        done
    | PBot ->
        for i = 0 to (kripke_env.n-1) do
          Sat.add_clause sat_env [| -varids.(i) |]
        done
    end;
    varids

type kripke_result =
    Refutable of int * bool array array * (pterm, bool array) Hashtbl.t
  | Irrefutable
  | NotDetermined

let solve_n penv n t =
  let sat_env = Sat.new_environment () in
  let kripke_env = new_kripke_env sat_env n in
  let term_memo = Hashtbl.create 13 in
  let varids = make_clauses sat_env kripke_env term_memo t in
  Sat.add_clause sat_env [| -varids.(0) |];
  let minisat_result = Sat.invoke_minisat sat_env in
  begin match minisat_result with
  | Sat.Satisfiable asgn ->
      (* Format.eprintf "Satisfiable@."; *)
      (* for x = 1 to sat_env.maxvar do
        if asgn.(x) then
          Format.eprintf "%d@." x
        else
          Format.eprintf "%d@." (-x)
      done; *)
      (* Hashtbl.iter (fun t0 varids0 ->
        Format.eprintf "%a = @." (pp_print_pterm penv 5) t0;
        Format.eprintf "   [";
        Array.iter (fun x ->
          Format.eprintf "%d, " (if asgn.(x) then 1 else 0)
        ) varids0;
        Format.eprintf "]@."
      ) term_memo; *)
      let accessibility = Array.map (fun row ->
        Array.map (fun v -> asgn.(v)) row
      ) kripke_env.accessibility in
      let term_asgn = Hashtbl.create 47 in
      Hashtbl.iter (fun t0 varids0 ->
        Hashtbl.add term_asgn t0 (Array.map (fun x -> asgn.(x)) varids0)
      ) term_memo;
      Refutable (n, accessibility, term_asgn)
  | Sat.Unsatisfiable ->
      (* Format.eprintf "Unsatisfiable@."; *)
      Irrefutable
  | Sat.NotDetermined ->
      (* Format.eprintf "Not determined@."; *)
      NotDetermined
  end

let solve penv t =
  let ret = ref Irrefutable in
  for n = 2 to 4 do
    if !ret = Irrefutable then
      ret := solve_n penv n t
  done;
  !ret
