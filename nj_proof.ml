open Term
open Format
open Lf_proof

type nj_proof =
  | NJ_var of int
  | NJ_app of nj_proof * nj_proof
  | NJ_abs of pterm * nj_proof
  | NJ_tt (* True *)
  | NJ_ab of pterm (* False -> A *)
  | NJ_conj (* A -> B -> A /\ B *)
  | NJ_fst (* A /\ B -> A *)
  | NJ_snd (* A /\ B -> B *)
  | NJ_left of pterm (* A -> A \/ B *)
  | NJ_right of pterm (* B -> A \/ B *)
  | NJ_disj (* A \/B -> (A -> C) -> (B -> C) -> C *)

let make_app t1 t2 = NJ_app (t1,t2)
let make_ab p t1 = NJ_app (NJ_ab p,t1)
let make_conj t1 t2 = NJ_app (NJ_app (NJ_conj,t1),t2)
let make_fst t1 = NJ_app (NJ_fst,t1)
let make_snd t1 = NJ_app (NJ_snd,t1)
let make_left p t1 = NJ_app (NJ_left p,t1)
let make_right p t1 = NJ_app (NJ_right p,t1)
let make_disj t1 t2 t3 = NJ_app (NJ_app (NJ_app (NJ_disj,t1),t2),t3)
let destruct_abs t =
  begin match t with
  | NJ_abs (_,ta) -> ta
  | _ -> raise (Invalid_argument "t is not a lambda-abstraction")
  end

let rec pp_print_lambda ppf = function
  | NJ_var x ->
      fprintf ppf "@[<1>%d@]@," x
  | NJ_app (t1,t2) ->
      fprintf ppf "@[<1>%a@ (%a)@]@,"
        pp_print_lambda t1
        pp_print_lambda t2
  | NJ_abs (p,ta) ->
      fprintf ppf "@[<1>\\:%a.@ %a@]@,"
        (pp_print_pterm empty_env 0) p
        pp_print_lambda ta
  | NJ_tt -> fprintf ppf "@[<1>tt@]@,"
  | NJ_ab p ->
      fprintf ppf "@[<1>ab[%a]@]@,"
        (pp_print_pterm empty_env 0) p
  | NJ_conj -> fprintf ppf "@[<1>conj@]@,"
  | NJ_fst -> fprintf ppf "@[<1>fst@]@,"
  | NJ_snd -> fprintf ppf "@[<1>snd@]@,"
  | NJ_left p -> fprintf ppf "@[<1>left[%a]@]@,"
        (pp_print_pterm empty_env 0) p
  | NJ_right p -> fprintf ppf "@[<1>right[%a]@]@,"
        (pp_print_pterm empty_env 0) p
  | NJ_disj -> fprintf ppf "@[<1>disj@]@,"

let rec shift i j t =
  begin match t with
  | NJ_var x when x >= i -> NJ_var (x+j)
  | NJ_app (t1,t2) -> NJ_app (shift i j t1,shift i j t2)
  | NJ_abs (p,ta) -> NJ_abs (p,shift (i+1) j ta)
  | _ -> t
  end

let rec subst d t s =
  begin match t with
  | NJ_var x when x = d -> shift 0 d s
  | NJ_var x when x > d -> NJ_var (x-1)
  | NJ_app (t1,t2) -> NJ_app (subst d t1 s,subst d t2 s)
  | NJ_abs (p,ta) -> NJ_abs (p,subst (d+1) ta s)
  | _ -> t
  end

let rec reduce t =
  begin match t with
  | NJ_app (NJ_abs (_,ta),s) -> reduce (subst 0 ta s)
  | NJ_abs (p,ta) -> NJ_abs (p,reduce ta)
  | NJ_app (t1,t2) ->
      let rt1 = reduce t1 in
      let rt2 = reduce t2 in
      begin match rt1,rt2 with
      | NJ_abs (_,ta), s -> reduce (subst 0 ta s)
      | NJ_fst, NJ_app (NJ_app (NJ_conj,a),b) -> a
      | NJ_snd, NJ_app (NJ_app (NJ_conj,a),b) -> b
      | NJ_app (NJ_app (NJ_disj,NJ_app (NJ_left p,a)),ac),bc ->
          NJ_app (ac,a)
      | NJ_app (NJ_app (NJ_disj,NJ_app (NJ_right p,b)),ac),bc ->
          NJ_app (bc,b)
      | _,_ -> NJ_app (rt1,rt2)
      end
  | _ -> t
  end

let rec replace_type_type v s p =
  begin match p with
  | PVar x when x = v -> s
  | PArrow (p1,p2) -> PArrow (
      replace_type_type v s p1,
      replace_type_type v s p2)
  | POr (p1,p2) -> POr (
      replace_type_type v s p1,
      replace_type_type v s p2)
  | PAnd (p1,p2) -> PAnd (
      replace_type_type v s p1,
      replace_type_type v s p2)
  | _ -> p
  end

let rec replace_type v s t =
  begin match t with
  | NJ_app (t1,t2) -> NJ_app (
      replace_type v s t1,
      replace_type v s t2)
  | NJ_abs (p,ta) -> NJ_abs (
      replace_type_type v s p,
      replace_type v s ta)
  | NJ_ab p -> NJ_ab (replace_type_type v s p)
  | NJ_left p -> NJ_left (replace_type_type v s p)
  | NJ_right p -> NJ_right (replace_type_type v s p)
  | _ -> t
  end

let rec convert_lf_internal anum pnum ant sucL sucR pr =
  let debug_data = (* debug *)
  begin match pr with
  | LF_ax x ->
      begin match sucL with
      | None -> NJ_var (anum-1-x)
      | Some sucLS -> NJ_abs (PArrow (sucR,sucLS),NJ_var (anum-1-x+1))
      end
  | LF_RT -> NJ_tt
  | LF_RC (pr1,pr2) ->
      begin match sucR with
      | PAnd (t1,t2) ->
          let lt1 = convert_lf_internal anum pnum ant sucL t1 pr1 in
          let lt2 = convert_lf_internal anum pnum ant sucL t2 pr2 in
          begin match sucL with
          | None -> make_conj lt1 lt2
          | Some sucLS -> reduce (NJ_abs (PArrow (sucR,sucLS),make_conj
              (make_app (shift 0 1 lt1) (NJ_abs (t1,make_app (NJ_var 1)
                (make_conj (NJ_var 0) (make_app (shift 0 2 lt2) (NJ_abs
                  (t2,make_app (NJ_var 2) (make_conj (NJ_var 1) (NJ_var 0)))
                )))
              )))
              (make_app (shift 0 1 lt2) (NJ_abs (t2,make_app (NJ_var 1)
                (make_conj (make_app (shift 0 2 lt1) (NJ_abs
                  (t1,make_app (NJ_var 2) (make_conj (NJ_var 0) (NJ_var 1)))
                )) (NJ_var 0))
              )))
            ))
          end
      | _ -> raise (Invalid_argument "LF_RC given, but not PAnd")
      end
  | LF_RDL pr ->
      begin match sucR with
      | POr (t1,t2) ->
          begin match sucL with
          | None ->
              let lt = convert_lf_internal anum pnum ant sucL t1 pr in
              make_left t2 lt
          | Some sucLS ->
              let p = PVar pnum in
              let lt = convert_lf_internal (anum+2) (pnum+1)
                ((PArrow (t2,p),anum)::(PArrow (p,sucLS),anum+1)::ant)
                (Some p) t1 pr in
              let lt = NJ_abs (PArrow (t2,p),NJ_abs (PArrow (p,sucLS),lt)) in
              let lt = replace_type pnum (POr (t1,t2)) lt in
              reduce (NJ_abs (PArrow (sucR,sucLS),make_left t2
                (make_app (make_app (make_app (shift 0 1 lt)
                  (NJ_abs (t1,make_left t2 (NJ_var 0))))
                  (NJ_var 0))
                  (NJ_abs (t2,make_right t1 (NJ_var 0)))
                )
              ))
          end
      | _ -> raise (Invalid_argument "LF_RDL given, but not POr")
      end
  | LF_RDR pr ->
      begin match sucR with
      | POr (t1,t2) ->
          begin match sucL with
          | None ->
              let lt = convert_lf_internal anum pnum ant sucL t2 pr in
              make_right t1 lt
          | Some sucLS ->
              let p = PVar pnum in
              let lt = convert_lf_internal (anum+2) (pnum+1)
                ((PArrow (t1,p),anum)::(PArrow (p,sucLS),anum+1)::ant)
                (Some p) t2 pr in
              let lt = NJ_abs (PArrow (t1,p),NJ_abs (PArrow (p,sucLS),lt)) in
              let lt = replace_type pnum (POr (t1,t2)) lt in
              reduce (NJ_abs (PArrow (sucR,sucLS),make_right t2
                (make_app (make_app (make_app (shift 0 1 lt)
                  (NJ_abs (t2,make_right t1 (NJ_var 0))))
                  (NJ_var 0))
                  (NJ_abs (t1,make_left t2 (NJ_var 0)))
                )
              ))
          end
      | _ -> raise (Invalid_argument "LF_RDR given, but not POr")
      end
  | LF_RI pr ->
      begin match sucR with
      | PArrow (t1,t2) ->
          let lt =
            convert_lf_internal (anum+1) pnum ((t1,anum)::ant) sucL t2 pr in
          begin match sucL with
          | None -> NJ_abs (t1,lt)
          | Some sucLS -> reduce (
              NJ_abs (PArrow (sucR,sucLS),NJ_abs (t1,
                make_app (make_app (shift 0 2 (NJ_abs (t1,lt))) (NJ_var 0))
                  (NJ_abs (t2,make_app (NJ_var 2) (NJ_abs (t1,NJ_var 1))))
              ))
            )
          end
      | _ -> raise (Invalid_argument "LF_RI given, but not PArrow")
      end
  | LF_LT (x,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      convert_lf_internal anum pnum (ant0@ant1) sucL sucR pr
  | LF_LB x ->
      begin match sucL with
      | None -> make_ab sucR (NJ_var (anum-1-x))
      | Some sucLS ->
          make_ab
          (PArrow (PArrow (sucR,sucLS),sucR))
          (NJ_var (anum-1-x))
      end
  | LF_LC (x,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      begin match t with
      | PAnd (t1,t2) ->
          let lt = convert_lf_internal (anum+2) pnum
            (ant0@(t1,anum)::(t2,anum+1)::ant1) sucL sucR pr in
          let lt = NJ_abs (t1,NJ_abs (t2,lt)) in
          let var = NJ_var (anum-1-x) in
          reduce (
            make_app (make_app lt (make_fst var)) (make_snd var)
          )
      | _ -> raise (Invalid_argument "LF_LC given, but not PAnd")
      end
  | LF_LD (x,pr1,pr2) ->
      let (ant0,t,ant1) = cutAnt ant x in
      begin match t with
      | POr (t1,t2) ->
          let lt1 = convert_lf_internal (anum+1) pnum
            (ant0@(t1,anum)::ant1) sucL sucR pr1 in
          let lt2 = convert_lf_internal (anum+1) pnum
            (ant0@(t2,anum)::ant1) sucL sucR pr2 in
          reduce (make_disj
            (NJ_var (anum-1-x))
            (NJ_abs (t1,lt1))
            (NJ_abs (t2,lt2))
          )
      | _ -> raise (Invalid_argument "LF_LD given, but not POr")
      end
  | LF_LIT (x,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      begin match t with
      | PArrow (_,t2) ->
          let lt = convert_lf_internal (anum+1) pnum
            (ant0@(t2,anum)::ant1) sucL sucR pr in
          let var = NJ_var (anum-1-x) in
          reduce (make_app (NJ_abs (t2,lt)) (make_app var NJ_tt))
      | _ -> raise (Invalid_argument "LF_LIT given, but not PArrow")
      end
  | LF_LIB (x,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      convert_lf_internal anum pnum (ant0@ant1) sucL sucR pr
  | LF_LIP (x,y,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      begin match t with
      | PArrow (_,t2) ->
          let lt = convert_lf_internal (anum+1) pnum
            (ant0@(t2,anum)::ant1) sucL sucR pr in
          let var1 = NJ_var (anum-1-x) in
          let var2 = NJ_var (anum-1-y) in
          reduce (make_app (NJ_abs (t2,lt)) (make_app var1 var2))
      | _ -> raise (Invalid_argument "LF_LIP given, but not PArrow")
      end
  | LF_LIC (x,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      begin match t with
      | PArrow (PAnd (t1,t2),t3) ->
          let atype = PArrow (t1,PArrow (t2,t3)) in
          let lt = convert_lf_internal (anum+1) pnum
            (ant0@(atype,anum)::ant1)
            sucL sucR pr in
          reduce (make_app (NJ_abs (atype,lt)) (
            NJ_abs (t1,NJ_abs (t2,
              make_app (NJ_var (anum-1-x+2)) (make_conj (NJ_var 1) (NJ_var 0))
            ))
          ))
      | _ -> raise (Invalid_argument "LF_LIC given, but not PAnd")
      end
  | LF_LID (x,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      let p = PVar pnum in
      begin match t with
      | PArrow (POr (t1,t2),t3) ->
          let lt = convert_lf_internal (anum+3) (pnum+1) (ant0@
            (PArrow (t1,p),anum)::
            (PArrow (t2,p),anum+1)::
            (PArrow (p,t3),anum+2)::
          ant1) sucL sucR pr in
          let lt = NJ_abs (PArrow (t1,p),NJ_abs (PArrow (t2,p),
            NJ_abs (PArrow (p,t3),lt))) in
          let lt = replace_type pnum (POr (t1,t2)) lt in
          reduce (make_app (make_app (make_app lt
            (NJ_abs (t1,make_left t2 (NJ_var 0))))
            (NJ_abs (t2,make_right t1 (NJ_var 0))))
            (NJ_var (anum-1-x))
          )
      | _ -> raise (Invalid_argument "LF_LID given, but not PArrow-POr")
      end
  | LF_LII (x,pr1,pr2) ->
      let (ant0,t,ant1) = cutAnt ant x in
      let p = PVar pnum in
      begin match t with
      | PArrow (PArrow (t1,t2),t3) ->
          begin match sucL with
          | None ->
              let lt1 = convert_lf_internal (anum+1) pnum
                (ant0@(t1,anum)::ant1) (Some t3) t2 pr1 in
              let lt2 = (convert_lf_internal (anum+1) pnum
                (ant0@(t3,anum)::ant1) sucL sucR) pr2 in
              reduce (make_app (NJ_abs (t3,lt2)) (make_app (NJ_var (anum-1-x))
                (NJ_abs (t1,make_app
                  (make_app (shift 0 1 (NJ_abs (t1,lt1))) (NJ_var 0))
                  (NJ_abs (t2,make_app
                    (NJ_var (anum-1-x+2))
                    (NJ_abs (t1,NJ_var 1))
                  ))
                ))
              ))
          | Some sucLS ->
              let atype = PArrow (sucR,sucLS) in
              let lt1 = convert_lf_internal (anum+2) pnum
                (ant0@(atype,anum)::(t1,anum+1)::ant1)
                (Some t3) t2 pr1 in
              let lt2 = (convert_lf_internal (anum+1) pnum
                (ant0@(t3,anum)::ant1) sucL sucR) pr2 in
              reduce (NJ_abs (atype,make_app (
                make_app (shift 0 1 (NJ_abs (t3,lt2))) (make_app (NJ_var (anum-1-x+1))
                  (NJ_abs (t1,make_app
                    (make_app
                      (make_app (shift 0 2 (NJ_abs (atype,NJ_abs (t1,lt1))))
                      (NJ_var 1))
                      (NJ_var 0)
                    )
                    (NJ_abs (t2,make_app
                      (NJ_var (anum-1-x+3))
                      (NJ_abs (t1,NJ_var 1))
                    ))
                  ))
                )
              ) (NJ_var 0)))
          end
      | _ -> raise (Invalid_argument "LF_LII given, but not PArrow-PArrow")
      end
  end
  (* debug *)
  in
  eprintf "debug: ";
  List.iter (fun (x,y) ->
    eprintf "%a[%d,%d],@ "
      (pp_print_pterm empty_env 0) x
      y (anum-1-y)
  ) ant;
  begin match sucL with
  | None ->
      eprintf "@ /@ %d@ |-@ %a@," anum
        (pp_print_pterm empty_env 0) sucR
  | Some sucLS ->
      eprintf "@ /@ %d@ [%a -> %a],@ |-@ %a@," anum
        (pp_print_pterm empty_env 0) sucR
        (pp_print_pterm empty_env 0) sucLS
        (pp_print_pterm empty_env 0) sucR
  end;
  eprintf "proof = %a@," (pp_print_proof_internal empty_env anum pnum ant sucL
  sucR) pr;
  eprintf "output : %a@." pp_print_lambda debug_data;
  debug_data

let convert_lf pnum sucR pr =
  convert_lf_internal 0 pnum [] None sucR pr

type nj_diagram =
  | NJD_var of pterm
  | NJD_app of pterm * nj_diagram * nj_diagram
  | NJD_abs of pterm * nj_diagram
  | NJD_tt of pterm
  | NJD_ab of pterm * nj_diagram
  | NJD_conj of pterm * nj_diagram * nj_diagram
  | NJD_fst of pterm * nj_diagram
  | NJD_snd of pterm * nj_diagram
  | NJD_left of pterm * nj_diagram
  | NJD_right of pterm * nj_diagram
  | NJD_disj of pterm * nj_diagram * nj_diagram * nj_diagram

let nj_diagram_type = function
  | NJD_var p -> p
  | NJD_app (p,_,_) -> p
  | NJD_abs (p,_) -> p
  | NJD_tt p -> p
  | NJD_ab (p,_) -> p
  | NJD_conj (p,_,_) -> p
  | NJD_fst (p,_) -> p
  | NJD_snd (p,_) -> p
  | NJD_left (p,_) -> p
  | NJD_right (p,_) -> p
  | NJD_disj (p,_,_,_) -> p


let rec make_diagram_internal stack t =
  begin match t with
  | NJ_tt -> NJD_tt PTop
  | NJ_app (NJ_ab p0,t1) ->
      let d1 = make_diagram_internal stack t1 in
      NJD_ab (p0,d1)
  | NJ_app (NJ_app (NJ_conj,t1),t2) ->
      let d1 = make_diagram_internal stack t1 in
      let d2 = make_diagram_internal stack t2 in
      NJD_conj (PAnd (nj_diagram_type d1,nj_diagram_type d2),d1,d2)
  | NJ_app (NJ_fst,t1) ->
      let d1 = make_diagram_internal stack t1 in
      begin match nj_diagram_type d1 with
      | PAnd (p1,p2) -> NJD_fst (p1,d1)
      | _ -> raise (Invalid_argument "PAnd required")
      end
  | NJ_app (NJ_snd,t1) ->
      let d1 = make_diagram_internal stack t1 in
      begin match nj_diagram_type d1 with
      | PAnd (p1,p2) -> NJD_snd (p2,d1)
      | _ -> raise (Invalid_argument "PAnd required")
      end
  | NJ_app (NJ_left p,t1) ->
      let d1 = make_diagram_internal stack t1 in
      NJD_left (POr (nj_diagram_type d1,p),d1)
  | NJ_app (NJ_right p,t1) ->
      let d1 = make_diagram_internal stack t1 in
      NJD_left (POr (p,nj_diagram_type d1),d1)
  | NJ_app (NJ_app (NJ_app (NJ_disj,t1),t2),t3) ->
      let d1 = make_diagram_internal stack t1 in
      let d2 = make_diagram_internal stack t2 in
      let d3 = make_diagram_internal stack t3 in
      begin match nj_diagram_type d3 with
      | PArrow (p1,p2) -> NJD_disj (p2,d1,d2,d3)
      | _ -> raise (Invalid_argument "PArrow required")
      end
  | NJ_var x -> NJD_var (List.nth stack x)
  | NJ_app (t1,t2) ->
      let d1 = make_diagram_internal stack t1 in
      let d2 = make_diagram_internal stack t2 in
      eprintf "t1 = %a@." (pp_print_lambda) t1;
      eprintf "d1 = %a@." (pp_print_pterm empty_env 0) (nj_diagram_type d1);
      eprintf "t2 = %a@." (pp_print_lambda) t2;
      eprintf "d2 = %a@." (pp_print_pterm empty_env 0) (nj_diagram_type d2);
      begin match nj_diagram_type d1 with
      | PArrow (p1,p2) -> NJD_app (p2,d1,d2)
      | _ -> raise (Invalid_argument "PArrow required")
      end
  | NJ_abs (pa,ta) ->
      let da = make_diagram_internal (pa::stack) ta in
      NJD_abs (PArrow (pa,nj_diagram_type da),da)
  | _ -> raise (Invalid_argument "constructors cannot appear singly")
  end

let make_diagram t = make_diagram_internal [] t

let rec print_nj_diagram_latex env ppf d =
  fprintf ppf "@[<1>";
  begin match d with
  | NJD_var p ->
      fprintf ppf "\\AxiomC{%a}@,"
        (pp_print_pterm_latex env 5) p
  | NJD_app (p,d1,d2) ->
      fprintf ppf "%a%a\\BinaryInfC{%a}@,"
        (print_nj_diagram_latex env) d1
        (print_nj_diagram_latex env) d2
        (pp_print_pterm_latex env 5) p
  | NJD_abs (p,d1) ->
      fprintf ppf "%a\\UnaryInfC{%a}@,"
        (print_nj_diagram_latex env) d1
        (pp_print_pterm_latex env 5) p
  | NJD_tt p ->
      fprintf ppf "\\AxiomC{%a}@,"
        (pp_print_pterm_latex env 5) p
  | NJD_ab (p,d1) ->
      fprintf ppf "%a\\UnaryInfC{%a}@,"
        (print_nj_diagram_latex env) d1
        (pp_print_pterm_latex env 5) p
  | NJD_conj (p,d1,d2) ->
      fprintf ppf "%a%a\\BinaryInfC{%a}@,"
        (print_nj_diagram_latex env) d1
        (print_nj_diagram_latex env) d2
        (pp_print_pterm_latex env 5) p
  | NJD_fst (p,d1) ->
      fprintf ppf "%a\\UnaryInfC{%a}@,"
        (print_nj_diagram_latex env) d1
        (pp_print_pterm_latex env 5) p
  | NJD_snd (p,d1) ->
      fprintf ppf "%a\\UnaryInfC{%a}@,"
        (print_nj_diagram_latex env) d1
        (pp_print_pterm_latex env 5) p
  | NJD_left (p,d1) ->
      fprintf ppf "%a\\UnaryInfC{%a}@,"
        (print_nj_diagram_latex env) d1
        (pp_print_pterm_latex env 5) p
  | NJD_right (p,d1) ->
      fprintf ppf "%a\\UnaryInfC{%a}@,"
        (print_nj_diagram_latex env) d1
        (pp_print_pterm_latex env 5) p
  | NJD_disj (p,d1,d2,d3) ->
      fprintf ppf "%a%a%a\\TrinaryInfC{%a}@,"
        (print_nj_diagram_latex env) d1
        (print_nj_diagram_latex env) d2
        (print_nj_diagram_latex env) d3
        (pp_print_pterm_latex env 5) p
  end;
  fprintf ppf "@]@,"

