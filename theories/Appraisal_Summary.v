From RocqCandy Require Import All.
From RocqJSON Require Import All.
From CoplandSpec Require Import Term_Defs ID_Type.

Definition AppraisalSummary := (Map ASP_ID (Map TARG_ID bool)).

Definition map_get_default {A B:Type} `{H : DecEq A} (x:A) (y:B) (m:Map A B) : B := 
  match (m ![ x ]) with
  | Some v => v 
  | None => y 
  end.

Definition set_AppraisalSummary (i:ASP_ID) (tid:TARG_ID) (b:bool) 
    (s:AppraisalSummary) : AppraisalSummary := 
  let m := map_get_default i ([] : Map TARG_ID bool) s in
  let m' := m ![ tid := b ] in
  s ![ i := m' ].

Definition check_simple_appraised_rawev (ls:RawEv) : bool := 
  match ls with 
  | [bs] => if dec_eq bs passed_bs then true else false
  | _ => false 
  end.

Definition add_asp_summary (i:ASP_ID) (tid:TARG_ID) (ls:RawEv)
    (s:AppraisalSummary) : AppraisalSummary := 
  let b := check_simple_appraised_rawev ls in  
  set_AppraisalSummary i tid b s.

Fixpoint do_AppraisalSummary' (et:EvidenceT) (r:RawEv) (G:GlobalContext) 
    (s:AppraisalSummary) : Result AppraisalSummary string := 
  match et with 
  | mt_evt => res s 
  | nonce_evt nid => res s (* TODO:  do anything else with nonce check here? *)
  | split_evt et1 et2 => 
      et1_size <- et_size G et1 ;;
      et2_size <- et_size G et2 ;;
      '(r1, rest) <- peel_n_rawev et1_size r ;;
      '(r2, _) <- peel_n_rawev et2_size rest ;;
      s1 <- do_AppraisalSummary' et1 r1 G s ;;
      do_AppraisalSummary' et2 r2 G s1
  | left_evt et' => 
      r <- apply_to_evidence_below G (fun et'' => do_AppraisalSummary' et'' r G s) [Trail_LEFT] et' ;;
      r
  
  | right_evt et' => 
      r <- apply_to_evidence_below G (fun et'' => do_AppraisalSummary' et'' r G s) [Trail_RIGHT] et' ;;
      r
  
  | asp_evt p ps et' => 
      let '(asp_paramsC i args tp tid) := ps in 
      match ((asp_types G) ![ i ]) with 
      | None => res s  (* TODO: resultT type eventually... *)
      | Some (ev_arrow fwd in_sig out_sig) => 
        match fwd with 
        | EXTEND => 
          match out_sig with 
          | OutN n => 
              '(r1, rest) <- peel_n_rawev n r ;; 
              let s' := add_asp_summary i tid r1 s in 
              do_AppraisalSummary' et' rest G s'

          | _ => err err_str_cannot_have_outwrap
          end
        | REPLACE => 
          match out_sig with 
          | OutN n => 
              '(r1, rest) <- peel_n_rawev n r ;; 
              let s' := add_asp_summary i tid r1 s in 
              res s'

          | _ => err err_str_cannot_have_outwrap
          end
        | _ => res s 
        end
      end
  end.

Definition do_AppraisalSummary (et:EvidenceT) (r:RawEv) (G:GlobalContext) : Result AppraisalSummary string := 
  do_AppraisalSummary' et r G [].

Definition fold_appsumm (appsumm:AppraisalSummary) : bool := 
  let targmaps : list (Map TARG_ID bool) := map snd appsumm in
  let targbools : list (list bool) := map (map snd) targmaps in
  forallb (fun ls => forallb id ls) targbools.


Global Instance AppraisalSummaryJsonifiable `{Stringifiable ASP_ID, Stringifiable (Map TARG_ID bool)} : Jsonifiable AppraisalSummary.
eapply Build_Jsonifiable with 
(to_JSON := map_serial_serial_to_JSON)
(from_JSON := map_serial_serial_from_JSON).
intros.
rewrite canonical_jsonification_map_serial_serial in *.
eauto.
Qed.