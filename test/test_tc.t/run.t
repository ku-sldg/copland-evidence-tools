Test that Typechecking Succeeds as expected
  $ copland_evidence_tools --req "$(cat Test_Req.json)"
  { "TYPE": "RESPONSE", "ACTION": "TypeCheck", "SUCCESS": true, "PAYLOAD": { "Option_Body": { "EvidenceT_CONSTRUCTOR": "asp_evt", "EvidenceT_BODY": ["P0", { "ASP_ID": "attest", "ASP_ARGS": {  } }, { "EvidenceT_CONSTRUCTOR": "mt_evt" }] } } }

Test that Typechecking Succeeds as expected when doing APPR too
  $ copland_evidence_tools --req "$(cat Test_Req_with_Appr.json)"
  { "TYPE": "RESPONSE", "ACTION": "TypeCheck", "SUCCESS": true, "PAYLOAD": { "Option_Body": { "EvidenceT_CONSTRUCTOR": "split_evt", "EvidenceT_BODY": [{ "EvidenceT_CONSTRUCTOR": "asp_evt", "EvidenceT_BODY": ["P0", { "ASP_ID": "magic_appr", "ASP_ARGS": {  } }, { "EvidenceT_CONSTRUCTOR": "asp_evt", "EvidenceT_BODY": ["P0", { "ASP_ID": "attest", "ASP_ARGS": {  } }, { "EvidenceT_CONSTRUCTOR": "mt_evt" }] }] }, { "EvidenceT_CONSTRUCTOR": "mt_evt" }] } } }
