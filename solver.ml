(*
 * This solver is based on:
 * JÖRG HUDELMAIER,
 * An O(n log n)-Space Decision Procedure
 * for Intuitionistic Propositional Logic.
 * J Logic Computation (1993) 3 (1): 63-75.
 * DOI: http://dx.doi.org/10.1093/logcom/3.1.63
 *)
(* author: Masaki Hara *)

open Term
open Lf_proof

(*
 * general rules:
 * Antecedent:
 *   list of pair (Term,Number).
 *   Number is counted using ``anum''.
 * Succedent:
 *   pair of Term.
 *   1. sucR is usual succedent.
 *   2. sucL is special succedent for ->->L rules.
 * Atomic Proposition:
 *   fresh atomic proposition comes from ``pnum''.
 *)

let do_debug_sequent = false

let debug_sequent name ant1 ant2 sucL sucR =
  if do_debug_sequent then begin
    Format.eprintf "%s: " name;
    List.iter (fun (x,_) -> Format.eprintf "%a, "
      (Term.pp_print_pterm empty_env 0) x) (List.rev ant2);
    Format.eprintf ";; ";
    List.iter (fun (x,_) -> Format.eprintf "%a, "
      (Term.pp_print_pterm empty_env 0) x) ant1;
    begin match sucL with
    | None ->
        Format.eprintf "|- %a@."
          (Term.pp_print_pterm empty_env 0) sucR
    | Some sucLS ->
        Format.eprintf " [%a -> %a], |- %a@."
          (Term.pp_print_pterm empty_env 0) sucR
          (Term.pp_print_pterm empty_env 0) sucLS
          (Term.pp_print_pterm empty_env 0) sucR
    end
  end else ()

let make_proof (f:lf_proof -> lf_proof) (t:lf_proof option) =
  begin match t with
  | None -> None
  | Some ts -> Some (f ts)
  end

let make_proof_and (f:lf_proof -> lf_proof -> lf_proof)
    (t1: unit -> lf_proof option)
    (t2: unit -> lf_proof option) =
  begin match t1 () with
  | None -> None
  | Some pr1 ->
      begin match t2 () with
      | None -> None
      | Some pr2 -> Some (f pr1 pr2)
      end
  end

let make_proof_or
    (f1: lf_proof -> lf_proof)
    (f2: lf_proof -> lf_proof)
    (t1: unit -> lf_proof option)
    (t2: unit -> lf_proof option) =
  begin match t1 () with
  | Some pr -> Some (f1 pr)
  | None ->
      begin match t2 () with
      | Some pr -> Some (f2 pr)
      | None -> None
      end
  end

(* solve1: only use reversible rules *)

(*
 * solves [ant |- (sucR -> sucL) -> sucR ]
 * handles:
 * 1. |- (A -> B)
 * 2. |- (A /\ B)
 * 3. |- True
 *)
let rec solve1_internal_s anum pnum ant sucL sucR =
  debug_sequent "1S" ant [] sucL sucR;
  begin match sucR with
  | PArrow (t1,t2) ->
      make_proof (fun pr -> LF_RI pr)
        (solve1_internal_s (anum+1) pnum ((t1,anum)::ant) sucL t2)
  | PAnd (t1,t2) ->
      make_proof_and (fun pr1 pr2 -> LF_RC (pr1,pr2))
        (fun _ -> solve1_internal_s anum pnum ant sucL t1)
        (fun _ -> solve1_internal_s anum pnum ant sucL t2)
  | PTop -> Some LF_RT
  | _ -> solve1_internal_a1 anum pnum ant [] sucL sucR
  end

(*
 * solves [ant2 @ ant1 |- (sucR -> sucL) -> sucR ]
 * handles:
 *  1. (A <-> B) |-
 *  2. (A /\ B) |-
 *  3. (A \/ B) |-
 *  4. True |-
 *  5. False |-
 *  6. p |- p
 *  7. (True -> A) |-
 *  8. (False -> A) |-
 *  9. (A /\ B -> C) |-
 * 10. ((A <-> B) -> C) |-
 * 11. (A \/ B -> C) |-
 * note: only solve1_internal_{s,a1,a2} can call it.
 * note: ``ant2'' must not have propositions which can be handled in
 *   solve1_internal_a1.
 *)
and solve1_internal_a1 anum pnum ant1 ant2 sucL sucR =
  debug_sequent "1A1" ant1 ant2 sucL sucR;
  begin match ant1 with
  | [] -> solve1_internal_a2 anum pnum ant2 [] sucL sucR
  | (PAnd (t1,t2),ti) :: ant1t ->
      make_proof (fun pr -> LF_LC (ti,pr))
      (solve1_internal_a1 (anum+2) pnum
        ((t1,anum)::(t2,anum+1)::ant1t) ant2 sucL sucR)
  | (POr (t1,t2),ti) :: ant1t ->
      make_proof_and (fun pr1 pr2 -> LF_LD (ti,pr1,pr2))
        (fun _ ->
          solve1_internal_a1 (anum+1) pnum
            ((t1,anum)::ant1t) ant2 sucL sucR)
        (fun _ ->
          solve1_internal_a1 (anum+1) pnum
            ((t2,anum)::ant1t) ant2 sucL sucR)
  | (PTop,ti) :: ant1t ->
      make_proof (fun pr -> LF_LT (ti,pr))
        (solve1_internal_a1 anum pnum ant1t ant2 sucL sucR)
  | (PBot,ti) :: ant1t -> Some (LF_LB ti)
  | (PVar p,ti) :: ant1t when sucR = PVar p -> Some (LF_ax ti)
  | (PArrow (PTop,t3),ti) :: ant1t ->
      make_proof (fun pr -> LF_LIT (ti,pr))
        (solve1_internal_a1 (anum+1) pnum
          ((t3,anum)::ant1t) ant2 sucL sucR)
  | (PArrow (PBot,t3),ti) :: ant1t ->
      make_proof (fun pr -> LF_LIB (ti,pr))
        (solve1_internal_a1 anum pnum ant1t ant2 sucL sucR)
  | (PArrow (PAnd (t1,t2),t3),ti) :: ant1t ->
      make_proof (fun pr -> LF_LIC (ti,pr))
        (solve1_internal_a1 (anum+1) pnum
          ((PArrow (t1,PArrow (t2,t3)),anum)::ant1t) ant2 sucL sucR)
  | (PArrow (POr (t1,t2),t3),ti) :: ant1t ->
      let p = PVar pnum in
      make_proof (fun pr -> LF_LID (ti,pr))
        (solve1_internal_a1 (anum+3) (pnum+1) (
            (PArrow (t1,p),anum)::
            (PArrow (t2,p),anum+1)::
            (PArrow (p,t3),anum+2)::ant1t)
          ant2 sucL sucR)
  | ant1h :: ant1t ->
      solve1_internal_a1 anum pnum ant1t (ant1h::ant2) sucL sucR
  end

(*
 * solves [ant2 @ ant1 |- (sucR -> sucL) -> sucR ]
 * handles:
 * 1. (p -> C) |- [ only handles when p is in (ant2 @ ant1). ]
 * note: only solve1_internal_{a1,a2} can call it.
 * note: ``ant2'' must not have propositions which can be handled in
 *   solve1_internal_a1 and solve1_internal_a2.
 *)
and solve1_internal_a2 anum pnum ant1 ant2 sucL sucR =
  debug_sequent "1A2" ant1 ant2 sucL sucR;
  begin match ant1 with
  | [] -> solve2_internal_s anum pnum ant2 sucL sucR
  | (PArrow (PVar p,t3),ti) :: ant1t
      when List.exists (fun (x,_) -> x = PVar p) ant1 ->
      let tj = snd (List.find (fun (x,_) -> x = PVar p) ant1) in
      make_proof (fun pr -> LF_LIP (ti,tj,pr))
        (solve1_internal_a1 (anum+1) pnum [(t3,anum)] (ant2@ant1t) sucL sucR)
  | (PArrow (PVar p,t3),ti) :: ant1t
      when List.exists (fun (x,_) -> x = PVar p) ant2 ->
      let tj = snd (List.find (fun (x,_) -> x = PVar p) ant2) in
      make_proof (fun pr -> LF_LIP (ti,tj,pr))
        (solve1_internal_a1 (anum+1) pnum [(t3,anum)] (ant2@ant1t) sucL sucR)
  | ant1h :: ant1t ->
      solve1_internal_a2 anum pnum ant1t (ant1h::ant2) sucL sucR
  end

(*
 * solves [ant |- (sucR -> sucL) -> sucR ]
 * handles:
 * 1. |- (A \/ B)
 *)
and solve2_internal_s anum pnum ant sucL sucR =
  debug_sequent "2S" ant [] sucL sucR;
  begin match sucR with
  | POr (t1,t2) ->
      begin match sucL with
      | None ->
          make_proof_or (fun pr -> LF_RDL pr) (fun pr -> LF_RDR pr)
            (fun _ -> solve1_internal_s anum pnum ant sucL t1)
            (fun _ -> solve1_internal_s anum pnum ant sucL t2)
      | Some sucLS ->
          let p = PVar pnum in
          let sp = Some p in
          make_proof_or (fun pr -> LF_RDL pr) (fun pr -> LF_RDR pr)
            (fun _ ->
              solve1_internal_s (anum+2) (pnum+1)
                ((PArrow (t2,p),anum)::(PArrow (p,sucLS),anum+1)::ant) sp t1)
            (fun _ ->
              solve1_internal_s (anum+2) (pnum+1)
                ((PArrow (t1,p),anum)::(PArrow (p,sucLS),anum+1)::ant) sp t2)
      end
  | _ -> solve2_internal_a anum pnum ant [] sucL sucR
  end

(*
 * solves [ant2 @ ant1 |- (sucR -> sucL) -> sucR ]
 * handles:
 * 1. ((A -> B) -> C) |-
 * note: ``ant2'' must not have propositions which can be handled in
 *   solve2_internal_a.
 *)
and solve2_internal_a anum pnum ant1 ant2 sucL sucR =
  debug_sequent "2A" ant1 ant2 sucL sucR;
  begin match ant1 with
  | [] -> None
  | ant1h :: ant1t ->
      make_proof_or (fun pr -> pr) (fun pr -> pr)
      (fun _ ->
      begin match ant1h with
      | PArrow (PArrow (t1,t2),t3),ti ->
          make_proof_and (fun pr1 pr2 -> LF_LII (ti,pr1,pr2))
          (fun _ ->
          begin match sucL with
          | None ->
              solve1_internal_s (anum+1) pnum
                ((t1,anum)::ant1t@ant2) (Some t3) t2
          | Some sucLS ->
              solve1_internal_s (anum+2) pnum
                ((PArrow (sucR,sucLS),anum)::(t1,anum+1)::ant1t@ant2)
                (Some t3) t2
          end)
          (fun _ ->
          solve1_internal_s (anum+1) pnum
            ((t3,anum)::ant1t@ant2) sucL sucR)
      | _ -> None
      end)
      (fun _ ->
      solve2_internal_a anum pnum ant1t (ant1h::ant2) sucL sucR)
  end

let solve pnum p =
  solve1_internal_s 0 pnum [] None p
