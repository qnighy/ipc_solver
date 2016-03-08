open Term

exception UnificationFailure

let rec maxvar p =
  begin match p with
  | PVar x -> 1+x
  | PArrow (p1,p2) -> max (maxvar p1) (maxvar p2)
  | POr (p1,p2) -> max (maxvar p1) (maxvar p2)
  | PAnd (p1,p2) -> max (maxvar p1) (maxvar p2)
  | PTop -> 0
  | PBot -> 0
  end

let rec shiftvar s p =
  begin match p with
  | PVar x -> PVar (s+x)
  | PArrow (p1,p2) -> PArrow (shiftvar s p1,shiftvar s p2)
  | POr (p1,p2) -> POr (shiftvar s p1,shiftvar s p2)
  | PAnd (p1,p2) -> PAnd (shiftvar s p1,shiftvar s p2)
  | PTop -> PTop
  | PBot -> PBot
  end

let rec occur h x p =
  begin match p with
  | PVar y when Hashtbl.mem h y -> occur h x (Hashtbl.find h y)
  | PVar y -> x = y
  | PArrow (p1,p2) -> occur h x p1 || occur h x p2
  | POr (p1,p2) -> occur h x p1 || occur h x p2
  | PAnd (p1,p2) -> occur h x p1 || occur h x p2
  | _ -> false
  end

let unify_set h x p =
  if occur h x p then
    raise UnificationFailure
  else
    Hashtbl.add h x p; p

let rec unify_rec h pa pb =
  begin match pa,pb with
  | PVar xa,_ when Hashtbl.mem h xa ->
      unify_rec h (Hashtbl.find h xa) pb
  | _,PVar xb when Hashtbl.mem h xb ->
      unify_rec h pa (Hashtbl.find h xb)
  | PVar xa,PVar xb when xa = xb -> pa
  | PVar xa,_ -> unify_set h xa pb
  | _,PVar xb -> unify_set h xb pa
  | PArrow (pa1,pa2),PArrow (pb1,pb2) ->
      PArrow (unify_rec h pa1 pb1,unify_rec h pa2 pb2)
  | POr (pa1,pa2),POr (pb1,pb2) ->
      POr (unify_rec h pa1 pb1,unify_rec h pa2 pb2)
  | PAnd (pa1,pa2),PAnd (pb1,pb2) ->
      PAnd (unify_rec h pa1 pb1,unify_rec h pa2 pb2)
  | _,_ -> raise UnificationFailure
  end

let rec unify_extract h p =
  begin match p with
  | PVar x when Hashtbl.mem h x -> unify_extract h (Hashtbl.find h x)
  | PArrow (p1,p2) -> PArrow (unify_extract h p1,unify_extract h p2)
  | POr (p1,p2) -> POr (unify_extract h p1,unify_extract h p2)
  | PAnd (p1,p2) -> PAnd (unify_extract h p1,unify_extract h p2)
  | _ -> p
  end

let unify_application pa pb =
  begin match pa with
  | PArrow (pa1,pa2) ->
      let pb = shiftvar (maxvar pa) pb in
      let h = Hashtbl.create 101 in
      unify_rec h pa1 pb;
      unify_extract h pa2
  | _ -> raise UnificationFailure
  end

let comb_b = PArrow (
  PArrow (PVar 1,PVar 2),
  PArrow (PArrow (PVar 0,PVar 1),PArrow (PVar 0,PVar 2)))

let comb_c = PArrow (
  PArrow (PVar 0,PArrow (PVar 1,PVar 2)),
  PArrow (PVar 1,PArrow (PVar 0,PVar 2)))

let comb_k = PArrow (PVar 0,PArrow (PVar 1,PVar 0))

let comb_w = PArrow (
  PArrow (PVar 0,PArrow (PVar 0,PVar 1)),PArrow (PVar 0,PVar 1))

let comb_conj = PArrow (PVar 0,PArrow (PVar 1,PAnd (PVar 0,PVar 1)))
let comb_fst = PArrow (PAnd (PVar 0,PVar 1),PVar 0)
let comb_snd = PArrow (PAnd (PVar 0,PVar 1),PVar 1)
let comb_left = PArrow (PVar 0,POr (PVar 0,PVar 1))
let comb_right = PArrow (PVar 1,POr (PVar 0,PVar 1))
let comb_disj = PArrow (POr (PVar 0,PVar 1),
  PArrow (PArrow (PVar 0,PVar 2),
  PArrow (PArrow (PVar 1,PVar 2),PVar 2)))
let comb_tt = PTop
let comb_ab = PArrow (PBot,PVar 0)

let findlemma l =
  let r = Random.int 600 + 1000 * List.length l in
  if r < 100 then comb_b
  else if r < 200 then comb_c
  else if r < 225 then comb_k
  else if r < 300 then comb_w
  else if r < 350 then comb_conj
  else if r < 400 then comb_fst
  else if r < 450 then comb_snd
  else if r < 500 then comb_left
  else if r < 550 then comb_right
  else if r < 600 then comb_disj
  else
    let r = (r - 600) / 1000 in
    let r = max r (Random.int (List.length l)) in
    let r = max r (Random.int (List.length l)) in
    List.nth l r

let rec collect_var n h p =
  begin match p with
  | PVar x when not (Hashtbl.mem h x) ->
      Hashtbl.add h x (!n); n := 1 + !n
  | PArrow (p1,p2) -> collect_var n h p1;collect_var n h p2
  | POr (p1,p2) -> collect_var n h p1;collect_var n h p2
  | PAnd (p1,p2) -> collect_var n h p1;collect_var n h p2
  | _ -> ()
  end
let rec replace_var_rec h p =
  begin match p with
  | PVar x -> PVar (Hashtbl.find h x)
  | PArrow (p1,p2) -> PArrow (replace_var_rec h p1,replace_var_rec h p2)
  | POr (p1,p2) -> POr (replace_var_rec h p1,replace_var_rec h p2)
  | PAnd (p1,p2) -> PAnd (replace_var_rec h p1,replace_var_rec h p2)
  | _ -> p
  end
let replace_var p =
  let h = Hashtbl.create 101 in
  collect_var (ref 0) h p;
  replace_var_rec h p

let rec generate_rec l t =
  if Sys.time () -. t > 0.5 then
    generate_rec [] (Sys.time ())
  else
  let a = findlemma l in
  let b = findlemma l in
  begin try
    let c = unify_application a b in
    (* Format.printf "%s, %s ---> %s; "
      (pterm_short_string colorful_env 0 a)
      (pterm_short_string colorful_env 0 (shiftvar (maxvar a) b))
      (pterm_short_string colorful_env 0 c); *)
    let c = replace_var c in
    (* Format.printf "%s@." (pterm_short_string colorful_env 0 c); *)
    if List.length l >= 100 && Random.int 1000 <= 1 then
      Format.printf "%s@." (pterm_short_string colorful_env 0 c)
    else
      generate_rec (c::l) t
  with UnificationFailure ->
    generate_rec l t
  end

let generate () = generate_rec [] (Sys.time ())
