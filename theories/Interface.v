From CoplandSpec Require Import Term_Defs Attestation_Session Interface.
From CoplandEvidenceTools Require Import Appraisal_Summary.

Record AppraisalSummaryRequest := 
  mkAppSummReq {
    appsummreq_att_sess : Attestation_Session;
    appsummreq_Evidence: Evidence;
  }.

Record AppraisalSummaryResponse := 
  mkAppSummResp {
    appsummresp_success: bool;
    appsummresp_summary: AppraisalSummary;
  }.

Global Instance Jsonifiable_AppraisalSummaryRequest `{Jsonifiable Evidence, Jsonifiable Attestation_Session}: Jsonifiable AppraisalSummaryRequest.
eapply Build_Jsonifiable with
(to_JSON := fun req =>
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_REQUEST));
    (STR_ACTION, (JSON_String STR_APPSUMM));
    (STR_ATTEST_SESS, (to_JSON (appsummreq_att_sess req)));
    (STR_EVIDENCE, (to_JSON (appsummreq_Evidence req)))])
(from_JSON := (fun j =>
  temp_att_sess <- JSON_get_Object STR_ATTEST_SESS j ;;
  temp_ev <- JSON_get_Object STR_EVIDENCE j ;;

  att_sess <- from_JSON temp_att_sess ;;
  ev <- from_JSON temp_ev ;;
  res (mkAppSummReq att_sess ev)));
solve_json.
Qed.

Global Instance Jsonifiable_AppraisalSummaryResponse `{Jsonifiable AppraisalSummary}: Jsonifiable AppraisalSummaryResponse.
eapply Build_Jsonifiable with
(to_JSON := fun resp =>
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_RESPONSE));
    (STR_ACTION, (JSON_String STR_APPSUMM));
    (STR_SUCCESS, (JSON_Boolean (appsummresp_success resp)));
    (STR_PAYLOAD, (to_JSON (appsummresp_summary resp)))])
(from_JSON := (fun resp =>
  temp_success <- JSON_get_bool STR_SUCCESS resp ;;
  temp_appsumm <- JSON_get_Object STR_PAYLOAD resp ;;

  appsumm <- from_JSON temp_appsumm ;;
  res (mkAppSummResp temp_success appsumm))); solve_json.
Qed.