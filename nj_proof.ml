open Term
open Format
open Lf_proof

type nj_proof =
  | NJ_var of pterm * int
  | NJ_app of pterm * nj_proof * nj_proof
  | NJ_abs of pterm * pterm * nj_proof
  | NJ_tt (* True *)
  | NJ_ab of pterm * nj_proof (* False -> A *)
  | NJ_conj of pterm * nj_proof * nj_proof (* A -> B -> A /\ B *)
  | NJ_fst of pterm * nj_proof (* A /\ B -> A *)
  | NJ_snd of pterm * nj_proof(* A /\ B -> B *)
  | NJ_left of pterm * nj_proof (* A -> A \/ B *)
  | NJ_right of pterm * nj_proof (* B -> A \/ B *)
  | NJ_disj of pterm * nj_proof * nj_proof * nj_proof (* A \/B -> (A -> C) -> (B -> C) -> C *)

let nj_type = function
  | NJ_var (p,_) -> p
  | NJ_app (p,_,_) -> p
  | NJ_abs (p,_,_) -> p
  | NJ_tt -> PTop
  | NJ_ab (p,_) -> p
  | NJ_conj (p,_,_) -> p
  | NJ_fst (p,_) -> p
  | NJ_snd (p,_) -> p
  | NJ_left (p,_) -> p
  | NJ_right (p,_) -> p
  | NJ_disj (p,_,_,_) -> p

let abs_over p t = NJ_abs (PArrow (p,nj_type t),p,t)

let rec pp_print_lambda env ppf = function
  | NJ_var (p,x) ->
      fprintf ppf "@[<1>(%d@ :@ %a)@]@," x
        (pp_print_pterm env 0) p
  | NJ_app (p,t1,t2) ->
      fprintf ppf "@[<1>(%a@ %a@ :@ %a)@]@,"
        (pp_print_lambda env) t1
        (pp_print_lambda env) t2
        (pp_print_pterm env 0) p
  | NJ_abs (p,pa,ta) ->
      fprintf ppf "@[<1>(\\:%a.@ %a@ :@ %a)@]@,"
        (pp_print_pterm env 0) pa
        (pp_print_lambda env) ta
        (pp_print_pterm env 0) p
  | NJ_tt -> fprintf ppf "@[<1>tt@]@,"
  | NJ_ab (p,t1) ->
      fprintf ppf "@[<1>([ab]@ %a@ :@ %a)@]@,"
        (pp_print_lambda env) t1
        (pp_print_pterm env 0) p
  | NJ_conj (p,t1,t2) ->
      fprintf ppf "@[<1>([conj]@ %a %a@ :@ %a)@]@,"
        (pp_print_lambda env) t1
        (pp_print_lambda env) t2
        (pp_print_pterm env 0) p
  | NJ_fst (p,t1) ->
      fprintf ppf "@[<1>([fst]@ %a@ :@ %a)@]@,"
        (pp_print_lambda env) t1
        (pp_print_pterm env 0) p
  | NJ_snd (p,t1) ->
      fprintf ppf "@[<1>([snd]@ %a@ :@ %a)@]@,"
        (pp_print_lambda env) t1
        (pp_print_pterm env 0) p
  | NJ_left (p,t1) ->
      fprintf ppf "@[<1>([left]@ %a@ :@ %a)@]@,"
        (pp_print_lambda env) t1
        (pp_print_pterm env 0) p
  | NJ_right (p,t1) ->
      fprintf ppf "@[<1>([right]@ %a@ :@ %a)@]@,"
        (pp_print_lambda env) t1
        (pp_print_pterm env 0) p
  | NJ_disj (p,t1,t2,t3) ->
      fprintf ppf "@[<1>([disj]@ %a@ %a@ %a@ :@ %a)@]@,"
        (pp_print_lambda env) t1
        (pp_print_lambda env) t2
        (pp_print_lambda env) t3
        (pp_print_pterm env 0) p

let rec shift i j t =
  begin match t with
  | NJ_var (p,x) when x >= i -> NJ_var (p,x+j)
  | NJ_var (_,_) -> t
  | NJ_app (p,t1,t2) -> NJ_app (p,shift i j t1,shift i j t2)
  | NJ_abs (p,pa,ta) -> NJ_abs (p,pa,shift (i+1) j ta)
  | NJ_tt -> NJ_tt
  | NJ_ab (p,t1) -> NJ_ab (p,shift i j t1)
  | NJ_conj (p,t1,t2) -> NJ_conj (p,shift i j t1,shift i j t2)
  | NJ_fst (p,t1) -> NJ_fst (p,shift i j t1)
  | NJ_snd (p,t1) -> NJ_snd (p,shift i j t1)
  | NJ_left (p,t1) -> NJ_left (p,shift i j t1)
  | NJ_right (p,t1) -> NJ_right (p,shift i j t1)
  | NJ_disj (p,t1,t2,t3) -> NJ_disj (p,shift i j t1,shift i j t2,shift i j t3)
  end

let rec subst d t s =
  begin match t with
  | NJ_var (_,x) when x = d -> shift 0 d s
  | NJ_var (p,x) when x > d -> NJ_var (p,x-1)
  | NJ_var (_,_) -> t
  | NJ_app (p,t1,t2) -> NJ_app (p,subst d t1 s,subst d t2 s)
  | NJ_abs (p,pa,ta) -> NJ_abs (p,pa,subst (d+1) ta s)
  | NJ_tt -> NJ_tt
  | NJ_ab (p,t1) -> NJ_ab (p,subst d t1 s)
  | NJ_conj (p,t1,t2) -> NJ_conj (p,subst d t1 s,subst d t2 s)
  | NJ_fst (p,t1) -> NJ_fst (p,subst d t1 s)
  | NJ_snd (p,t1) -> NJ_snd (p,subst d t1 s)
  | NJ_left (p,t1) -> NJ_left (p,subst d t1 s)
  | NJ_right (p,t1) -> NJ_right (p,subst d t1 s)
  | NJ_disj (p,t1,t2,t3) -> NJ_disj (p,subst d t1 s,subst d t2 s,subst d t3 s)
  end

let rec count_fv v t =
  begin match t with
  | NJ_var (_,x) when x = v -> 1
  | NJ_var (_,_) -> 0
  | NJ_app (_,t1,t2) -> count_fv v t1 + count_fv v t2
  | NJ_abs (_,_,ta) -> count_fv (v+1) ta
  | NJ_tt -> 0
  | NJ_ab (_,t1) -> count_fv v t1
  | NJ_conj (_,t1,t2) -> count_fv v t1 + count_fv v t2
  | NJ_fst (_,t1) -> count_fv v t1
  | NJ_snd (_,t1) -> count_fv v t1
  | NJ_left (_,t1) -> count_fv v t1
  | NJ_right (_,t1) -> count_fv v t1
  | NJ_disj (_,t1,t2,t3) -> count_fv v t1 + count_fv v t2 + count_fv v t3
  end

let rec reduce t =
  begin match t with
  | NJ_var (p,x) -> reduce2 t
  | NJ_app (p,t1,t2) ->
      let rt2 = reduce t2 in
      begin match reduce t1 with
      | NJ_abs (_,_,ta) -> reduce (subst 0 ta rt2)
      | rt1 -> reduce2 (NJ_app (p,rt1,rt2))
      end
  | NJ_abs (p,pa,ta) -> reduce2 (NJ_abs (p,pa,reduce ta))
  | NJ_tt -> NJ_tt
  | NJ_ab (p,t1) -> reduce2 (NJ_ab (p,reduce t1))
  | NJ_conj (p,t1,t2) -> reduce2 (NJ_conj (p,reduce t1,reduce t2))
  | NJ_fst (p,t1) -> reduce2 (NJ_fst (p,reduce t1))
  | NJ_snd (p,t1) -> reduce2 (NJ_snd (p,reduce t1))
  | NJ_left (p,t1) -> reduce2 (NJ_left (p,reduce t1))
  | NJ_right (p,t1) -> reduce2 (NJ_right (p,reduce t1))
  | NJ_disj (p,t1,t2,t3) -> reduce2 (NJ_disj (p,reduce t1,reduce t2,reduce t3))
  end
and reduce2 t =
  begin match t with
  | NJ_abs (_,_,NJ_app (_,t1,NJ_var (_,0)))
      when count_fv 0 t1 = 0 -> shift 0 (-1) t1
  | NJ_fst (_,NJ_conj (_,t1,_)) -> t1
  | NJ_snd (_,NJ_conj (_,_,t2)) -> t2
  | NJ_disj (p,NJ_left (_,t1),t2,_) -> reduce (NJ_app (p,t2,t1))
  | NJ_disj (p,NJ_right (_,t1),_,t3) -> reduce (NJ_app (p,t3,t1))
  | NJ_disj (p,t1,NJ_abs (_,_,t2),_) when count_fv 0 t2 = 0 -> shift 0 (-1) t2
  | NJ_disj (p,t1,_,NJ_abs (_,_,t3)) when count_fv 0 t3 = 0 -> shift 0 (-1) t3
  | NJ_disj (p,t1,NJ_abs (_,pa2,t2),NJ_abs (_,pa3,t3)) ->
      begin match t2,t3 with
      | NJ_ab (p2,t2x),NJ_ab (p3,t3x) ->
          NJ_ab (p,NJ_disj (PBot,t1,NJ_abs (PArrow (pa2,PBot),pa2,t2x),NJ_abs
          (PArrow (pa3,PBot),pa3,t3x)))
      | _,_ -> t
      end
  | NJ_conj (p,NJ_fst (_,t1),NJ_snd (_,t2)) when t1 = t2 -> t1
  | _ -> t
  end

let rec nj_check_type e t =
  begin match t with
  | NJ_var (p,x) -> assert (List.nth e x = p); p
  | NJ_app (p,t1,t2) ->
      assert (nj_check_type e t1 = PArrow (nj_check_type e t2, p)); p
  | NJ_abs (p,pa,ta) ->
      assert (p = PArrow (pa, nj_check_type (pa::e) ta)); p
  | NJ_tt -> PTop
  | NJ_ab (p,t1) -> assert (nj_check_type e t1 = PBot); p
  | NJ_conj (p,t1,t2) ->
      assert (p = PAnd (nj_check_type e t1, nj_check_type e t2)); p
  | NJ_fst (p,t1) ->
      begin match nj_check_type e t1 with
      | PAnd (t1f,_) -> assert (t1f = p)
      | _ -> assert false
      end; p
  | NJ_snd (p,t1) ->
      begin match nj_check_type e t1 with
      | PAnd (_,t1s) -> assert (t1s = p)
      | _ -> assert false
      end; p
  | NJ_left (p,t1) ->
      begin match p with
      | POr (t1l,_) -> assert (t1l = nj_check_type e t1)
      | _ -> assert false
      end; p
  | NJ_right (p,t1) ->
      begin match p with
      | POr (_,t1r) -> assert (t1r = nj_check_type e t1)
      | _ -> assert false
      end; p
  | NJ_disj (p,t1,t2,t3) ->
      begin match nj_check_type e t1,nj_check_type e t2,nj_check_type e t3 with
      | POr (t1l,t1r), PArrow (t2a,t2b), PArrow (t3a,t3b) ->
          assert (t1l = t2a);
          assert (t1r = t3a);
          assert (t2b = p);
          assert (t3b = p);
      | _ -> assert false
      end; p
  end

let rec convert_lf_internal anum ant sucL sucR pr =
  let debug_data = (* debug *)
  let suc =
    begin match sucL with
    | None -> sucR
    | Some sucLS -> PArrow (PArrow (sucR,sucLS),sucR)
    end in
  begin match pr with
  | LF_ax x ->
      begin match sucL with
      | None -> NJ_var (sucR,anum-1-x)
      | Some sucLS ->
          let sucRL = PArrow (sucR,sucLS) in
          NJ_abs (PArrow (sucRL,sucR),sucRL,NJ_var (sucR,anum-1-x+1))
      end
  | LF_RT -> NJ_tt
  | LF_RC (pr1,pr2) ->
      begin match sucR with
      | PAnd (t1,t2) ->
          let lt1 = convert_lf_internal anum ant sucL t1 pr1 in
          let lt2 = convert_lf_internal anum ant sucL t2 pr2 in
          begin match sucL with
          | None -> NJ_conj (sucR,lt1,lt2)
          | Some sucLS ->
              let sucRL = PArrow (sucR,sucLS) in
              NJ_abs (PArrow (sucRL,sucR),sucRL, (* f : sucR -> sucLS *)
                NJ_conj (sucR,
                  NJ_app (t1,
                    shift 0 1 lt1,
                    NJ_abs (PArrow (t1,sucLS),t1, (* x : t1 *)
                      NJ_app (sucLS,
                        NJ_var (sucRL,1), (* f *)
                        NJ_conj (sucR,
                          NJ_var (t1,0), (* x *)
                          NJ_app (t2,
                            shift 0 2 lt2,
                            NJ_abs (PArrow (t2,sucLS),t2, (* y : t2 *)
                              NJ_app (sucLS,
                                NJ_var (sucRL,2), (* f *)
                                NJ_conj (sucR,
                                  NJ_var (t1,1), (* x *)
                                  NJ_var (t2,0) (* y *)
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  ),
                  NJ_app (t2,
                    shift 0 1 lt2,
                    NJ_abs (PArrow (t2,sucLS),t2, (* y : t2 *)
                      NJ_app (sucLS,
                        NJ_var (sucRL,1), (* f *)
                        NJ_conj (sucR,
                          NJ_app (t1,
                            shift 0 2 lt1,
                            NJ_abs (PArrow (t1,sucLS),t1, (* x : t1 *)
                              NJ_app (sucLS,
                                NJ_var (sucRL,2), (* f *)
                                NJ_conj (sucR,
                                  NJ_var (t1,0), (* x *)
                                  NJ_var (t2,1) (* y *)
                                )
                              )
                            )
                          ),
                          NJ_var (t2,0) (* y *)
                        )
                      )
                    )
                  )
                )
              )
          end
      | _ -> raise (Invalid_argument "LF_RC given, but not PAnd")
      end
  | LF_RDL pr ->
      begin match sucR with
      | POr (t1,t2) ->
          begin match sucL with
          | None ->
              let lt = convert_lf_internal anum ant sucL t1 pr in
              NJ_left (sucR,lt)
          | Some sucLS ->
              let sucRL = PArrow (sucR,sucLS) in
              let paramT1 = PArrow (t2,sucR) in
              let ltt = PArrow (PArrow (t1,sucR),t1) in
              let lt = convert_lf_internal (anum+2)
                ((paramT1,anum)::(sucRL,anum+1)::ant) (Some sucR) t1 pr in
              let lt = abs_over paramT1 (abs_over sucRL lt) in
              NJ_abs (PArrow(sucRL,sucR),sucRL, (* f : sucR -> sucLS *)
                NJ_left (sucR,
                  NJ_app (t1,
                    NJ_app (ltt,
                      NJ_app (PArrow (sucRL,ltt),
                        shift 0 1 lt,
                        NJ_abs (PArrow (t2,sucR),t2, (* y : t2 *)
                          NJ_right (sucR,
                            NJ_var (t2,0) (* y *)
                          )
                        )
                      ),
                      NJ_var (sucRL,0) (* f *)
                    ),
                    NJ_abs (PArrow(t1,sucR),t1, (* x : t1 *)
                      NJ_left (sucR,
                        NJ_var (t1,0) (* x *)
                      )
                    )
                  )
                )
              )
          end
      | _ -> raise (Invalid_argument "LF_RDL given, but not POr")
      end
  | LF_RDR pr ->
      begin match sucR with
      | POr (t1,t2) ->
          begin match sucL with
          | None ->
              let lt = convert_lf_internal anum ant sucL t2 pr in
              NJ_right (sucR,lt)
          | Some sucLS ->
              let sucRL = PArrow (sucR,sucLS) in
              let paramT1 = PArrow (t1,sucR) in
              let ltt = PArrow (PArrow (t2,sucR),t2) in
              let lt = convert_lf_internal (anum+2)
                ((paramT1,anum)::(sucRL,anum+1)::ant) (Some sucR) t2 pr in
              let lt = abs_over paramT1 (abs_over sucRL lt) in
              NJ_abs (PArrow(sucRL,sucR),sucRL, (* f : sucR -> sucLS *)
                NJ_right (sucR,
                  NJ_app (t2,
                    NJ_app (ltt,
                      NJ_app (PArrow (sucRL,ltt),
                        shift 0 1 lt,
                        NJ_abs (PArrow (t1,sucR),t1, (* x : t1 *)
                          NJ_right (sucR,
                            NJ_var (t1,0) (* x *)
                          )
                        )
                      ),
                      NJ_var (sucRL,0) (* f *)
                    ),
                    NJ_abs (PArrow(t2,sucR),t2, (* y : t2 *)
                      NJ_left (sucR,
                        NJ_var (t2,0) (* y *)
                      )
                    )
                  )
                )
              )
          end
      | _ -> raise (Invalid_argument "LF_RDR given, but not POr")
      end
  | LF_RI pr ->
      begin match sucR with
      | PArrow (t1,t2) ->
          let lt =
            convert_lf_internal (anum+1) ((t1,anum)::ant) sucL t2 pr in
          let lt = abs_over t1 lt in
          begin match sucL with
          | None -> lt
          | Some sucLS ->
              let sucRL = PArrow (sucR,sucLS) in
              NJ_abs (PArrow (sucRL,sucR),sucRL, (* f : sucR -> sucLS *)
                NJ_abs (sucR,t1, (* g : t1 *)
                  NJ_app (t2,
                    NJ_app (PArrow(PArrow (t2,sucLS),t2),
                      shift 0 2 lt,
                      NJ_var (t1,0) (* g *)
                    ),
                    NJ_abs (PArrow (t2,sucLS),t2, (* y : t2 *)
                      NJ_app (sucLS,
                        NJ_var (sucRL,2), (* f *)
                        NJ_abs (sucR,t1, (* _ : t1 *)
                          NJ_var (t2,1) (* y *)
                        )
                      )
                    )
                  )
                )
              )
          end
      | _ -> raise (Invalid_argument "LF_RI given, but not PArrow")
      end
  | LF_LT (x,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      convert_lf_internal anum (ant0@ant1) sucL sucR pr
  | LF_LB x ->
      NJ_ab (suc,NJ_var (PBot,anum-1-x))
  | LF_LC (x,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      begin match t with
      | PAnd (t1,t2) ->
          let lt = convert_lf_internal (anum+2)
            (ant0@(t1,anum)::(t2,anum+1)::ant1) sucL sucR pr in
          let lt = abs_over t1 (abs_over t2 lt) in
          let var = NJ_var (t,anum-1-x) in
          NJ_app (suc,
            NJ_app (PArrow (t2,suc),
              lt,
              NJ_fst (t1,var)
            ),
            NJ_snd (t2,var)
          )
      | _ -> raise (Invalid_argument "LF_LC given, but not PAnd")
      end
  | LF_LD (x,pr1,pr2) ->
      let (ant0,t,ant1) = cutAnt ant x in
      begin match t with
      | POr (t1,t2) ->
          let lt1 = convert_lf_internal (anum+1)
            (ant0@(t1,anum)::ant1) sucL sucR pr1 in
          let lt2 = convert_lf_internal (anum+1)
            (ant0@(t2,anum)::ant1) sucL sucR pr2 in
          let lt1 = abs_over t1 lt1 in
          let lt2 = abs_over t2 lt2 in
          NJ_disj (suc,
            NJ_var (t,anum-1-x),
            lt1,
            lt2
          )
      | _ -> raise (Invalid_argument "LF_LD given, but not POr")
      end
  | LF_LIT (x,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      begin match t with
      | PArrow (_,t2) ->
          let lt = convert_lf_internal (anum+1)
            (ant0@(t2,anum)::ant1) sucL sucR pr in
          let lt = abs_over t2 lt in
          let var = NJ_var (t,anum-1-x) in
          NJ_app (suc,
            lt,
            NJ_app (t2,var,NJ_tt)
          )
      | _ -> raise (Invalid_argument "LF_LIT given, but not PArrow")
      end
  | LF_LIB (x,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      convert_lf_internal anum (ant0@ant1) sucL sucR pr
  | LF_LIP (x,y,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      begin match t with
      | PArrow (t1,t2) ->
          let lt = convert_lf_internal (anum+1)
            (ant0@(t2,anum)::ant1) sucL sucR pr in
          let lt = abs_over t2 lt in
          let var1 = NJ_var (t,anum-1-x) in
          let var2 = NJ_var (t1,anum-1-y) in
          NJ_app (suc,
            lt,
            NJ_app (t2,var1,var2)
          )
      | _ -> raise (Invalid_argument "LF_LIP given, but not PArrow")
      end
  | LF_LIC (x,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      begin match t with
      | PArrow (PAnd (t1,t2),t3) ->
          let atype = PArrow (t1,PArrow (t2,t3)) in
          let lt = convert_lf_internal (anum+1)
            (ant0@(atype,anum)::ant1)
            sucL sucR pr in
          let lt = abs_over atype lt in
          NJ_app (suc,
            lt,
            NJ_abs (atype,t1, (* x : t1 *)
              NJ_abs (PArrow (t2,t3),t2, (* y : t2 *)
                NJ_app (t3,
                  NJ_var (t,anum-1-x+2),
                  NJ_conj (PAnd (t1,t2),
                    NJ_var (t1,1), (* x *)
                    NJ_var (t2,0) (* y *)
                  )
                )
              )
            )
          )
      | _ -> raise (Invalid_argument "LF_LIC given, but not PAnd")
      end
  | LF_LID (x,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      begin match t with
      | PArrow (POr (t1,t2) as t12,t3) ->
          let paramT1 = PArrow (t1,t12) in
          let paramT2 = PArrow (t2,t12) in
          let lt = convert_lf_internal (anum+3) (ant0@
            (paramT1,anum)::
            (paramT2,anum+1)::
            (t,anum+2)::
          ant1) sucL sucR pr in
          let lt = abs_over paramT1 (abs_over paramT2 (abs_over t lt)) in
          NJ_app (suc,
            NJ_app (PArrow (t,suc),
              NJ_app (PArrow (paramT2,PArrow (t,suc)),
                lt,
                NJ_abs (paramT1,t1,
                  NJ_left (t12,NJ_var (t1,0))
                )
              ),
              NJ_abs (paramT2,t2,
                NJ_right (t12,NJ_var (t2,0))
              )
            ),
            NJ_var (t,anum-1-x)
          )
      | _ -> raise (Invalid_argument "LF_LID given, but not PArrow-POr")
      end
  | LF_LII (x,pr1,pr2) ->
      let (ant0,t,ant1) = cutAnt ant x in
      begin match t with
      | PArrow (PArrow (t1,t2) as t12,t3) ->
          begin match sucL with
          | None ->
              let lt1 = convert_lf_internal (anum+1)
                (ant0@(t1,anum)::ant1) (Some t3) t2 pr1 in
              let lt2 = (convert_lf_internal (anum+1)
                (ant0@(t3,anum)::ant1) sucL sucR) pr2 in
              let lt1 = abs_over t1 lt1 in
              let lt2 = abs_over t3 lt2 in
              NJ_app (sucR,
                lt2,
                NJ_app (t3,
                  NJ_var (t,anum-1-x),
                  NJ_abs (t12,t1, (* x : t1 *)
                    NJ_app (t2,
                      NJ_app (PArrow (PArrow (t2,t3),t2),
                        shift 0 1 lt1,
                        NJ_var (t1,0) (* x *)
                      ),
                      NJ_abs (PArrow (t2,t3),t2, (* y : t2 *)
                        NJ_app (t3,
                          NJ_var (t,anum-1-x+2),
                          NJ_abs (t12,t1, (* _ : t1 *)
                            NJ_var (t2,1) (* y *)
                          )
                        )
                      )
                    )
                  )
                )
              )
          | Some sucLS ->
              let atype = PArrow (sucR,sucLS) in
              let lt1 = convert_lf_internal (anum+2)
                (ant0@(atype,anum)::(t1,anum+1)::ant1)
                (Some t3) t2 pr1 in
              let lt2 = (convert_lf_internal (anum+1)
                (ant0@(t3,anum)::ant1) sucL sucR) pr2 in
              let lt1 = abs_over atype (abs_over t1 lt1) in
              let lt2 = abs_over t3 lt2 in
              NJ_abs (suc,atype, (* f : sucR -> sucLS *)
                NJ_app (sucR,
                  NJ_app (suc,
                    shift 0 1 lt2,
                    NJ_app (t3,
                      NJ_var (t,anum-1-x+1),
                      NJ_abs (t12,t1, (* x : t1 *)
                        NJ_app (t2,
                          NJ_app (PArrow (PArrow (t2,t3),t2),
                            NJ_app (PArrow (t1,PArrow (PArrow (t2,t3),t2)),
                              shift 0 2 lt1,
                              NJ_var (atype,1) (* f *)
                            ),
                            NJ_var (t1,0) (* x *)
                          ),
                          NJ_abs (PArrow (t2,t3),t2, (* y : t2 *)
                            NJ_app (t3,
                              NJ_var (t,anum-1-x+3),
                              NJ_abs (t12,t1, (* _ : t1 *)
                                NJ_var (t2,1) (* y *)
                              )
                            )
                          )
                        )
                      )
                    )
                  ),
                  NJ_var (atype,0) (* f *)
                )
              )
          end
      | _ -> raise (Invalid_argument "LF_LII given, but not PArrow-PArrow")
      end
  end
  (* debug *)
  in
  (*
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
  eprintf "proof = %a@," (pp_print_proof_internal empty_env anum 100 ant sucL
  sucR) pr;
  eprintf "output : %a@." (pp_print_lambda empty_env) debug_data;
  *)
  debug_data

let convert_lf sucR pr =
  convert_lf_internal 0 [] None sucR pr

let rec compress_proof_internal1 p t =
  let result =
  begin match t with
  | NJ_var (_,_) -> None
  | NJ_app (_,t1,t2) ->
      begin match compress_proof_internal1 p t1 with
      | Some k -> Some k
      | None -> compress_proof_internal1 p t2
      end
  | NJ_abs (_,_,ta) -> None
  | NJ_tt -> None
  | NJ_ab (_,t1) ->
      compress_proof_internal1 p t1
  | NJ_conj (_,t1,t2) ->
      begin match compress_proof_internal1 p t1 with
      | Some k -> Some k
      | None -> compress_proof_internal1 p t2
      end
  | NJ_fst (_,t1) ->
      compress_proof_internal1 p t1
  | NJ_snd (_,t1) ->
      compress_proof_internal1 p t1
  | NJ_left (_,t1) ->
      compress_proof_internal1 p t1
  | NJ_right (_,t1) ->
      compress_proof_internal1 p t1
  | NJ_disj (_,t1,t2,t3) ->
      begin match compress_proof_internal1 p t1 with
      | Some k -> Some k
      | None ->
          begin match compress_proof_internal1 p t2 with
          | Some k -> Some k
          | None -> compress_proof_internal1 p t3
          end
      end
  end in
  begin match result with
  | Some k -> Some k
  | None ->
      if nj_type t = p then
        Some t
      else if nj_type t = PBot then
        Some (NJ_ab (p,t))
      else
        None
  end

let rec findstack p = function
  | [] -> raise Not_found
  | pp::t when pp = p -> 0
  | h::t -> 1 + findstack p t

let rec compress_proof_internal2 stack t =
  try
    NJ_var (nj_type t,findstack (nj_type t) stack)
  with Not_found ->
  let t =
    begin match compress_proof_internal1 (nj_type t) t with
    | Some t -> t
    | None -> t
    end in
  begin match t with
  | NJ_var (_,_) -> t
  | NJ_app (p,t1,t2) ->
      NJ_app (p,
        compress_proof_internal2 stack t1,
        compress_proof_internal2 stack t2)
  | NJ_abs (p,pa,ta) ->
      NJ_abs (p,pa,compress_proof_internal2 (pa::stack) ta)
  | NJ_tt -> t
  | NJ_ab (p,t1) ->
      NJ_ab (p,compress_proof_internal2 stack t1)
  | NJ_conj (p,t1,t2) ->
      NJ_conj (p,
        compress_proof_internal2 stack t1,
        compress_proof_internal2 stack t2)
  | NJ_fst (p,t1) ->
      NJ_fst (p,compress_proof_internal2 stack t1)
  | NJ_snd (p,t1) ->
      NJ_snd (p,compress_proof_internal2 stack t1)
  | NJ_left (p,t1) ->
      NJ_left (p,compress_proof_internal2 stack t1)
  | NJ_right (p,t1) ->
      NJ_right (p,compress_proof_internal2 stack t1)
  | NJ_disj (p,t1,t2,t3) ->
      NJ_disj (p,
        compress_proof_internal2 stack t1,
        compress_proof_internal2 stack t2,
        compress_proof_internal2 stack t3)
  end

let postproc_proof t =
  let t = reduce t in
  let t = compress_proof_internal2 [] t in
  t

type proof_tree =
  | PTassumption of string
  | PTaxiom of string * string
  | PTunary of string * string * proof_tree
  | PTbinary of string * string * proof_tree * proof_tree
  | PTtrinary of string * string * proof_tree * proof_tree * proof_tree

let pt_append s = function
  | PTassumption p -> PTassumption (p^s)
  | PTaxiom (p,r) -> PTaxiom (p^s,r)
  | PTunary (p,r,t1) -> PTunary (p^s,r,t1)
  | PTbinary (p,r,t1,t2) -> PTbinary (p^s,r,t1,t2)
  | PTtrinary (p,r,t1,t2,t3) -> PTtrinary (p^s,r,t1,t2,t3)

let pt_prop = function
  | PTassumption p -> p
  | PTaxiom (p,r) -> p
  | PTunary (p,r,t1) -> p
  | PTbinary (p,r,t1,t2) -> p
  | PTtrinary (p,r,t1,t2,t3) -> p

let rec print_proof_tree ppf pt =
  begin match pt with
  | PTassumption p ->
      fprintf ppf "\\AxiomC{%s}@," p
  | PTaxiom (p,r) ->
      fprintf ppf "\\AxiomC{}@,";
      fprintf ppf "\\RightLabel{\\scriptsize%s}@," r;
      fprintf ppf "\\UnaryInfC{%s}@," p
  | PTunary (p,r,t1) ->
      print_proof_tree ppf t1;
      fprintf ppf "\\RightLabel{\\scriptsize%s}@," r;
      fprintf ppf "\\UnaryInfC{%s}@," p
  | PTbinary (p,r,t1,t2) ->
      print_proof_tree ppf t1;
      print_proof_tree ppf t2;
      fprintf ppf "\\RightLabel{\\scriptsize%s}@," r;
      fprintf ppf "\\BinaryInfC{%s}@," p
  | PTtrinary (p,r,t1,t2,t3) ->
      print_proof_tree ppf t1;
      print_proof_tree ppf t2;
      print_proof_tree ppf t3;
      fprintf ppf "\\RightLabel{\\scriptsize%s}@," r;
      fprintf ppf "\\TrinaryInfC{%s}@," p
  end

let nj_remove_abstraction t =
  begin match t with
  | NJ_abs (p,pa,ta) -> ta
  | _ ->
      let (p1,p2) =
        begin match nj_type t with
        | PArrow (p1,p2) -> (p1,p2)
        | _ -> assert false
        end in
      NJ_app (p2,shift 0 1 t,NJ_var (p1,0))
  end

let rec nj_make_tree env stack_e stack_n t =
  begin match t with
  | NJ_var (p,x) ->
      PTassumption (
        Misc.sprintf "[%a]$_{%d}$"
          (pp_print_pterm_latex env 5) p
          (List.nth stack_e x)
      )
  | NJ_app (p,t1,t2) ->
      PTbinary (
        Misc.sprintf "%a"
          (pp_print_pterm_latex env 5) p,
        "$\\to E$",
        nj_make_tree env stack_e stack_n t1,
        nj_make_tree env stack_e stack_n t2
      )
  | NJ_abs (p,pa,ta) ->
      let assump_num = 1 + !stack_n in
      stack_n := assump_num;
      let stack_e = assump_num :: stack_e in
      PTunary (
        Misc.sprintf "%a"
          (pp_print_pterm_latex env 5) p,
        Misc.sprintf "$\\to I(%d)$" assump_num,
        nj_make_tree env stack_e stack_n ta
      )
  | NJ_tt ->
      PTaxiom (
        Misc.sprintf "%a"
          (pp_print_pterm_latex env 5) PTop,
        "$\\top I$"
      )
  | NJ_ab (p,t1) ->
      PTunary (
        Misc.sprintf "%a"
          (pp_print_pterm_latex env 5) p,
        "$\\bot E$",
        nj_make_tree env stack_e stack_n t1
      )
  | NJ_conj (p,t1,t2) ->
      PTbinary (
        Misc.sprintf "%a"
          (pp_print_pterm_latex env 5) p,
        "$\\land I$",
        nj_make_tree env stack_e stack_n t1,
        nj_make_tree env stack_e stack_n t2
      )
  | NJ_fst (p,t1) ->
      PTunary (
        Misc.sprintf "%a"
          (pp_print_pterm_latex env 5) p,
        "$\\land E_1$",
        nj_make_tree env stack_e stack_n t1
      )
  | NJ_snd (p,t1) ->
      PTunary (
        Misc.sprintf "%a"
          (pp_print_pterm_latex env 5) p,
        "$\\land E_2$",
        nj_make_tree env stack_e stack_n t1
      )
  | NJ_left (p,t1) ->
      PTunary (
        Misc.sprintf "%a"
          (pp_print_pterm_latex env 5) p,
        "$\\lor I_1$",
        nj_make_tree env stack_e stack_n t1
      )
  | NJ_right (p,t1) ->
      PTunary (
        Misc.sprintf "%a"
          (pp_print_pterm_latex env 5) p,
        "$\\lor I_2$",
        nj_make_tree env stack_e stack_n t1
      )
  | NJ_disj (p,t1,t2,t3) ->
      let assump_num = 1 + !stack_n in
      stack_n := assump_num;
      let stack_e2 = assump_num :: stack_e in
      PTtrinary (
        Misc.sprintf "%a"
          (pp_print_pterm_latex env 5) p,
        Misc.sprintf "$\\lor E(%d)$" assump_num,
        nj_make_tree env stack_e stack_n t1,
        nj_make_tree env stack_e2 stack_n (nj_remove_abstraction t2),
        nj_make_tree env stack_e2 stack_n (nj_remove_abstraction t3)
      )
  end

let proof_tree_threshold = 40

let numberstr number = "\\ \\textcolor{red}{("^string_of_int number^")}"
let rec split_proof_tree trees number pt =
  begin match pt with
  | PTassumption p -> (pt,1,trees,number)
  | PTaxiom (p,r) -> (pt,1,trees,number)
  | PTunary (p,r,t1) ->
      let (t1s,t1n,trees,number) = split_proof_tree2 trees number t1 in
      (PTunary (p,r,t1s),t1n+1,trees,number)
  | PTbinary (p,r,t1,t2) ->
      let (t1s,t1n,trees,number) = split_proof_tree2 trees number t1 in
      let (t2s,t2n,trees,number) = split_proof_tree2 trees number t2 in
      (PTbinary (p,r,t1s,t2s),t1n+t2n+1,trees,number)
  | PTtrinary (p,r,t1,t2,t3) ->
      let (t1s,t1n,trees,number) = split_proof_tree2 trees number t1 in
      let (t2s,t2n,trees,number) = split_proof_tree2 trees number t2 in
      let (t3s,t3n,trees,number) = split_proof_tree2 trees number t3 in
      (PTtrinary (p,r,t1s,t2s,t3s),t1n+t2n+t3n+1,trees,number)
  end
and split_proof_tree2 trees number pt =
  let (pts,ptn,trees,number) = split_proof_tree trees number pt in
  if ptn > proof_tree_threshold then
    (PTassumption (pt_prop pts ^ (numberstr number)),
    1,pt_append (numberstr number) pts::trees,number+1)
  else
    (pts,ptn,trees,number)

let print_nj_latex env ppf d =
  let pt = nj_make_tree env [] (ref 0) d in
  let (pts,_,trees,_) = split_proof_tree [] 1 pt in
  let trees = pts::trees in
  List.iter (fun x ->
    fprintf ppf "%s@." "\\begin{prooftree}";
    fprintf ppf "%a@." print_proof_tree x;
    fprintf ppf "%s@.@." "\\end{prooftree}"
  ) (List.rev trees);
